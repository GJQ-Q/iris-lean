import LeanIrisX.Algebra.CMRA

namespace LeanIrisX

/-- An exclusive resource: `own a` is valid alone, but combining two owned
resources produces `invalid`. `unit` is the unital element. -/
inductive Excl (α : Type u) where
  | unit
  | own (value : α)
  | invalid
deriving Repr

namespace Excl

instance : OFE (Excl α) := OFE.ofDiscrete (Excl α)
instance : OFE.Discrete (Excl α) := ⟨fun h => h⟩

def op : Excl α → Excl α → Excl α
  | unit, y => y
  | x, unit => x
  | _, _ => invalid

def pcore : Excl α → Option (Excl α)
  | _ => some unit

def valid : Excl α → Prop
  | invalid => False
  | _ => True

instance : CMRA (Excl α) where
  pcore := pcore
  op := op
  validN _ x := valid x
  valid := valid
  op_ne x := by intro n y₁ y₂ h; cases h; rfl
  pcore_ne := by
    intro n x y cx hxy hcore
    cases hxy
    exact ⟨cx, hcore, rfl⟩
  pcore_none_ne := by intro n x y hxy hnone; contradiction
  validN_ne := by intro n x y hxy hx; cases hxy; exact hx
  valid_iff_validN := by
    intro x
    constructor
    · intro h n; exact h
    · intro h; exact h 0
  validN_succ := by intro n x h; exact h
  validN_op_left := by
    intro n x y h
    cases x <;> cases y <;> trivial
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by
    intro x cx h
    have : cx = unit := Option.some.inj h.symm
    subst cx
    cases x <;> rfl
  pcore_idem := by
    intro x cx h
    have : cx = unit := Option.some.inj h.symm
    subst cx
    rfl
  pcore_op_mono := by
    intro x cx h y
    have : cx = unit := Option.some.inj h.symm
    subst cx
    exact ⟨unit, by cases x <;> cases y <;> rfl⟩
  extend := by
    intro n x y₁ y₂ hx hdist
    cases hdist
    exact {
      left := y₁
      right := y₂
      decompose := rfl
      left_dist := rfl
      right_dist := rfl
    }

instance : UCMRA (Excl α) where
  unit := unit
  unit_valid := trivial
  unit_left := by intro x; rfl
  pcore_unit := rfl

theorem own_valid (a : α) : CMRA.valid (own a) := trivial

theorem own_op_own (a b : α) :
    CMRA.op (own a) (own b) = invalid := rfl

theorem own_conflict (a b : α) :
    ¬ CMRA.valid (CMRA.op (own a) (own b)) := by
  intro h
  exact h

theorem own_injective {a b : α} (h : own a = own b) : a = b := by
  injection h

end Excl
end LeanIrisX
