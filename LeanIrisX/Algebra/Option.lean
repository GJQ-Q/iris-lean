import LeanIrisX.Algebra.CMRA

/-!
The standard option camera. `none` is the unit and `some a` embeds an element
of the underlying camera. This construction is needed by Iris' View camera to
represent an optional authoritative element.
-/

namespace LeanIrisX

namespace OptionCMRA

def Dist [OFE α] (n : Nat) : Option α → Option α → Prop
  | none, none => True
  | some x, some y => x ≡{n}≡ y
  | _, _ => False

instance instOFE [OFE α] : OFE (Option α) where
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
      exact OFE.eq_of_dist h
  dist_mono := by
    intro n m x y hnm h
    cases x <;> cases y <;> simp [Dist] at h ⊢
    exact OFE.mono hnm h

def op [OFE α] [CMRA α] : Option α → Option α → Option α
  | none, y => y
  | x, none => x
  | some x, some y => some (CMRA.op x y)

def pcore [OFE α] [CMRA α] : Option α → Option (Option α)
  | none => some none
  | some x => some (CMRA.pcore x)

def ValidN [OFE α] [CMRA α] (n : Nat) : Option α → Prop
  | none => True
  | some x => CMRA.validN n x

def Valid [OFE α] [CMRA α] : Option α → Prop
  | none => True
  | some x => CMRA.valid x

@[simp] theorem op_none_left [OFE α] [CMRA α] (x : Option α) : op none x = x := rfl
@[simp] theorem op_none_right [OFE α] [CMRA α] (x : Option α) : op x none = x := by
  cases x <;> rfl

instance instCMRA [OFE α] [CMRA α] : CMRA (Option α) where
  pcore := pcore
  op := op
  validN := ValidN
  valid := Valid
  op_ne x := by
    intro n y₁ y₂ hy
    change Dist n y₁ y₂ at hy
    change Dist n (op x y₁) (op x y₂)
    cases x with
    | none => exact hy
    | some a =>
      cases y₁ with
      | none =>
        cases y₂ with
        | none => exact OFE.refl n a
        | some y₂ => contradiction
      | some y₁ =>
        cases y₂ with
        | none => contradiction
        | some y₂ => exact (@CMRA.op_ne α _ _ a) n hy
  pcore_ne := by
    intro n x y cx hxy hx
    change Dist n x y at hxy
    cases x with
    | none =>
      cases y with
      | none => simp [pcore] at hx ⊢; subst cx; trivial
      | some y => contradiction
    | some x =>
      cases y with
      | none => contradiction
      | some y =>
        simp [pcore] at hx
        subst cx
        cases hcx : CMRA.pcore x with
        | none =>
          have hcy : CMRA.pcore y = none := CMRA.pcore_none_ne hxy hcx
          exact ⟨none, by simp [pcore, hcy], trivial⟩
        | some cx =>
          obtain ⟨cy, hcy, hd⟩ := CMRA.pcore_ne hxy hcx
          exact ⟨some cy, by simp [pcore, hcy], hd⟩
  pcore_none_ne := by intro n x y hxy hnone; cases x <;> simp [pcore] at hnone
  validN_ne := by
    intro n x y hxy hx
    change Dist n x y at hxy
    cases x <;> cases y <;> simp [Dist, ValidN] at hxy hx ⊢
    exact @CMRA.validN_ne α _ _ n _ _ hxy hx
  valid_iff_validN := by
    intro x; cases x <;> simp [Valid, ValidN, CMRA.valid_iff_validN]
  validN_succ := by
    intro n x h; cases x <;> simp [ValidN] at h ⊢
    exact @CMRA.validN_succ α _ _ n _ h
  validN_op_left := by
    intro n x y h
    cases x with
    | none => trivial
    | some x =>
      cases y with
      | none => exact h
      | some y => exact @CMRA.validN_op_left α _ _ n x y h
  assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [op, CMRA.assoc]
  comm := by
    intro x y
    cases x <;> cases y <;> simp [op, CMRA.comm]
  pcore_op_left := by
    intro x cx hx
    cases x with
    | none => simp [pcore] at hx ⊢; subst cx; rfl
    | some x =>
      simp [pcore] at hx
      subst cx
      cases hcore : CMRA.pcore x with
      | none => rfl
      | some core =>
        change some (CMRA.op core x) = some x
        rw [CMRA.pcore_op_left hcore]
  pcore_idem := by
    intro x cx hx
    cases x with
    | none => simp [pcore] at hx ⊢; subst cx; rfl
    | some x =>
      simp [pcore] at hx
      subst cx
      cases hcore : CMRA.pcore x with
      | none => rfl
      | some core =>
        change some (CMRA.pcore core) = some (some core)
        rw [CMRA.pcore_idem hcore]
  pcore_op_mono := by
    intro x cx hx y
    cases x with
    | none =>
      simp [pcore] at hx
      subst cx
      cases y with
      | none => exact ⟨none, rfl⟩
      | some y => exact ⟨CMRA.pcore y, rfl⟩
    | some x =>
      simp [pcore] at hx
      subst cx
      cases hcore : CMRA.pcore x with
      | none =>
        cases y with
        | none => exact ⟨none, by simp [pcore, op, hcore]⟩
        | some y => exact ⟨CMRA.pcore (CMRA.op x y), by simp [pcore, op]⟩
      | some core =>
        cases y with
        | none => exact ⟨none, by simp [pcore, op, hcore]⟩
        | some y =>
          obtain ⟨cy, hcy⟩ := CMRA.pcore_op_mono hcore y
          exact ⟨some cy, by simp [pcore, op, hcy]⟩
  extend := by
    intro n x y₁ y₂ hx hdist
    cases y₁ with
    | none =>
      exact {
        left := none
        right := x
        decompose := by simp [op]
        left_dist := by trivial
        right_dist := hdist
      }
    | some y₁ =>
      cases y₂ with
      | none =>
        exact {
          left := x
          right := none
          decompose := (op_none_right x).symm
          left_dist := hdist
          right_dist := by trivial
        }
      | some y₂ =>
        cases x with
        | none =>
          change Dist n none (some (CMRA.op y₁ y₂)) at hdist
          contradiction
        | some x =>
          change CMRA.validN n x at hx
          change x ≡{n}≡ CMRA.op y₁ y₂ at hdist
          rcases (@CMRA.extend α _ _ n x y₁ y₂ hx hdist) with ⟨x₁, x₂, hdecomp, h₁, h₂⟩
          exact {
            left := some x₁
            right := some x₂
            decompose := by simp [op, hdecomp]
            left_dist := h₁
            right_dist := h₂
          }

instance instUCMRA [OFE α] [CMRA α] : UCMRA (Option α) where
  unit := none
  unit_valid := trivial
  unit_left := op_none_left
  pcore_unit := rfl

theorem some_validN_iff [OFE α] [CMRA α] (n : Nat) (x : α) :
    CMRA.validN n (some x : Option α) ↔ CMRA.validN n x := Iff.rfl

theorem none_is_unit [OFE α] [CMRA α] (x : Option α) :
    CMRA.op none x = x := rfl

end OptionCMRA
end LeanIrisX
