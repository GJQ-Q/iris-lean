import LeanIrisX.Algebra.TotalCore

/-! A nontrivial, duplicable marker resource. -/

namespace LeanIrisX

inductive PersistentToken where
  | unit
  | token
deriving DecidableEq, Repr

namespace PersistentToken

instance : OFE PersistentToken := OFE.ofDiscrete PersistentToken
instance : OFE.Discrete PersistentToken := ⟨fun h => h⟩

def op : PersistentToken → PersistentToken → PersistentToken
  | .unit, y => y
  | x, .unit => x
  | .token, .token => .token

instance : CMRA PersistentToken where
  pcore x := some x
  op := op
  validN _ _ := True
  valid _ := True
  op_ne x := by intro n y₁ y₂ h; cases h; exact OFE.refl n _
  pcore_ne := by
    intro n x y cx hxy hcore
    have hcx : cx = x := Option.some.inj hcore.symm
    subst cx
    exact ⟨y, rfl, hxy⟩
  pcore_none_ne := by intro n x y hxy h; contradiction
  validN_ne := by intros; trivial
  valid_iff_validN := by simp
  validN_succ := by intros; trivial
  validN_op_left := by intros; trivial
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by
    intro x cx h
    have hcx : cx = x := Option.some.inj h.symm
    subst cx
    cases x <;> rfl
  pcore_idem := by
    intro x cx h
    have hcx : cx = x := Option.some.inj h.symm
    subst cx
    rfl
  pcore_op_mono := by
    intro x cx h y
    have hcx : cx = x := Option.some.inj h.symm
    subst cx
    exact ⟨y, by cases x <;> cases y <;> rfl⟩
  extend := by
    intro n x y₁ y₂ hx h
    cases h
    exact ⟨y₁, y₂, rfl, OFE.refl n _, OFE.refl n _⟩

instance : UCMRA PersistentToken where
  unit := .unit
  unit_valid := trivial
  unit_left := by intro x; rfl
  pcore_unit := rfl

instance : TotalCore PersistentToken where
  core := id
  core_spec _ := rfl

theorem token_idem : CMRA.op token token = token := rfl
theorem token_ne_unit : token ≠ unit := by decide

end PersistentToken
end LeanIrisX
