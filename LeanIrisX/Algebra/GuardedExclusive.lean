import LeanIrisX.Algebra.TotalCore
import LeanIrisX.Core.Later

namespace LeanIrisX

/-- An exclusive resource whose payload is guarded by one logical step. -/
inductive GuardedExcl (α : Type u) where
  | unit
  | own (value : Later α)
  | invalid
deriving Repr

namespace GuardedExcl

variable {α : Type u} {β : Type v}

def Dist [OFE α] (n : Nat) : GuardedExcl α → GuardedExcl α → Prop
  | .unit, .unit => True
  | .own x, .own y => x ≡{n}≡ y
  | .invalid, .invalid => True
  | _, _ => False

instance [OFE α] : OFE (GuardedExcl α) where
  dist := Dist
  dist_equivalence n := by
    constructor
    · intro x; cases x <;> simp [Dist, OFE.refl]
    · intro x y h
      cases x <;> cases y <;> simp [Dist] at h ⊢
      exact OFE.symm h
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;> simp [Dist] at hxy hyz ⊢
      exact OFE.trans hxy hyz
  eq_dist x y := by
    constructor
    · intro h n; subst y; cases x <;> simp [Dist, OFE.refl]
    · intro h
      cases x <;> cases y <;> simp [Dist] at h ⊢
      congr
      exact OFE.eq_of_dist h
  dist_mono := by
    intro n m x y hnm h
    cases x <;> cases y <;> simp [Dist] at h ⊢
    exact OFE.mono hnm h

private def ownChain [OFE α] (c : OFEChain (GuardedExcl α))
    (fallback : Later α) : OFEChain (Later α) where
  approx n := match c n with
    | .own x => x
    | _ => fallback
  coherent := by
    intro n m hnm
    have h := c.coherent hnm
    change Dist n (c n) (c m) at h
    change (match c n with | .own x => x | _ => fallback) ≡{n}≡
      (match c m with | .own x => x | _ => fallback)
    cases hn : c n <;> cases hm : c m <;>
      simp [hn, hm, Dist] at h ⊢
    · exact OFE.refl n fallback
    · exact h
    · exact OFE.refl n fallback

instance [OFE α] [COFE α] : COFE (GuardedExcl α) where
  limit c := match h : c 0 with
    | .unit => .unit
    | .own x => .own (COFE.lim (ownChain c x))
    | .invalid => .invalid
  limit_spec := by
    intro c n
    split <;> rename_i hzero
    · have h := c.coherent (Nat.zero_le n)
      change Dist 0 (c 0) (c n) at h
      change Dist n .unit (c n)
      cases hn : c n <;> simp [hzero, hn, Dist] at h ⊢
    · rename_i x
      have hshape := c.coherent (Nat.zero_le n)
      change Dist 0 (c 0) (c n) at hshape
      cases hn : c n
      · simp [hzero, hn, Dist] at hshape
      · rename_i y
        change Dist n (.own (COFE.lim (ownChain c x))) (.own y)
        change COFE.lim (ownChain c x) ≡{n}≡ y
        simpa [ownChain, hn] using COFE.lim_dist (ownChain c x) n
      · simp [hzero, hn, Dist] at hshape
    · have h := c.coherent (Nat.zero_le n)
      change Dist 0 (c 0) (c n) at h
      change Dist n .invalid (c n)
      cases hn : c n <;> simp [hzero, hn, Dist] at h ⊢

def op : GuardedExcl α → GuardedExcl α → GuardedExcl α
  | .unit, y => y
  | x, .unit => x
  | _, _ => .invalid

def valid : GuardedExcl α → Prop
  | .invalid => False
  | _ => True

instance [OFE α] : CMRA (GuardedExcl α) where
  pcore _ := some .unit
  op := op
  validN _ x := valid x
  valid := valid
  op_ne x := by
    intro n y₁ y₂ h
    change Dist n y₁ y₂ at h
    change Dist n (op x y₁) (op x y₂)
    cases x <;> cases y₁ <;> cases y₂ <;> simp [Dist, op] at h ⊢
    · exact h
    · exact OFE.refl n _
  pcore_ne := by
    intro n x y cx hxy hcore
    have : cx = .unit := Option.some.inj hcore.symm
    subst cx
    exact ⟨.unit, rfl, OFE.refl n (GuardedExcl.unit : GuardedExcl α)⟩
  pcore_none_ne := by intro n x y hxy hnone; contradiction
  validN_ne := by
    intro n x y hxy hx
    change Dist n x y at hxy
    change valid x at hx
    change valid y
    cases x <;> cases y <;> simp [Dist, valid] at hxy hx ⊢
  valid_iff_validN := by
    intro x; constructor
    · intro h n; exact h
    · intro h; exact h 0
  validN_succ := by intro n x h; exact h
  validN_op_left := by
    intro n x y h
    cases x <;> cases y <;> simp [op, valid] at h ⊢
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by
    intro x cx h
    have : cx = .unit := Option.some.inj h.symm
    subst cx
    cases x <;> rfl
  pcore_idem := by
    intro x cx h
    have : cx = .unit := Option.some.inj h.symm
    subst cx
    rfl
  pcore_op_mono := by
    intro x cx h y
    have : cx = .unit := Option.some.inj h.symm
    subst cx
    exact ⟨.unit, by cases x <;> cases y <;> rfl⟩
  extend := by
    intro n x y₁ y₂ hx hdist
    cases y₁ with
    | unit =>
      exact {
        left := .unit
        right := x
        decompose := rfl
        left_dist := OFE.refl n (GuardedExcl.unit : GuardedExcl α)
        right_dist := hdist
      }
    | own a =>
      cases y₂ with
      | unit =>
        exact {
          left := x
          right := .unit
          decompose := by cases x <;> rfl
          left_dist := hdist
          right_dist := OFE.refl n (GuardedExcl.unit : GuardedExcl α)
        }
      | own b =>
        change valid x at hx
        change Dist n x .invalid at hdist
        cases x <;> simp [Dist, valid] at hx hdist
      | invalid =>
        change valid x at hx
        change Dist n x .invalid at hdist
        cases x <;> simp [Dist, valid] at hx hdist
    | invalid =>
      cases y₂ with
      | unit =>
        exact {
          left := x
          right := .unit
          decompose := by cases x <;> rfl
          left_dist := hdist
          right_dist := OFE.refl n (GuardedExcl.unit : GuardedExcl α)
        }
      | own b =>
        change valid x at hx
        change Dist n x .invalid at hdist
        cases x <;> simp [Dist, valid] at hx hdist
      | invalid =>
        change valid x at hx
        change Dist n x .invalid at hdist
        cases x <;> simp [Dist, valid] at hx hdist

instance [OFE α] : UCMRA (GuardedExcl α) where
  unit := .unit
  unit_valid := trivial
  unit_left := by intro x; rfl
  pcore_unit := rfl

instance [OFE α] : TotalCore (GuardedExcl α) where
  core _ := .unit
  core_spec _ := rfl

def map (f : α → β) : GuardedExcl α → GuardedExcl β
  | .unit => .unit
  | .own x => .own (Later.map f x)
  | .invalid => .invalid

theorem map_nonExpansive [OFE α] [OFE β] (f : α → β) (hf : NonExpansive f) :
    NonExpansive (map f) := by
  intro n x y h
  change Dist n x y at h
  change Dist n (map f x) (map f y)
  cases x <;> cases y <;> simp [Dist, map] at h ⊢
  exact Later.map_nonExpansive f hf n h

theorem map_validN [OFE α] [OFE β] (f : α → β) {n : Nat} {x : GuardedExcl α} :
    CMRA.validN n x → CMRA.validN n (map f x) := by
  intro h
  change valid x at h
  change valid (map f x)
  cases x <;> simp [map, valid] at h ⊢

theorem map_op [OFE α] [OFE β] (f : α → β) (x y : GuardedExcl α) :
    map f (CMRA.op x y) = CMRA.op (map f x) (map f y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem map_id (x : GuardedExcl α) : map id x = x := by
  cases x <;> rfl

theorem map_comp (f : α → β) {γ : Type w} (g : β → γ) (x : GuardedExcl α) :
    map g (map f x) = map (g ∘ f) x := by
  cases x <;> rfl

theorem own_valid [OFE α] (a : Later α) : CMRA.valid (own a) := trivial

theorem own_conflict [OFE α] (a b : Later α) :
    ¬ CMRA.valid (CMRA.op (own a) (own b)) := by
  intro h; exact h

end GuardedExcl
end LeanIrisX
