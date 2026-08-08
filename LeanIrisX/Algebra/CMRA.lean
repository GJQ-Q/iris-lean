import LeanIrisX.Core.Fixpoint

/-!
The core CMRA interface, following the Iris camera laws. CMRA is a property of
an existing OFE instance; completeness is supplied separately when needed.
-/

namespace LeanIrisX

structure CMRAExtension {α : Type u} [OFE α]
    (op : α → α → α) (n : Nat) (x y₁ y₂ : α) where
  left : α
  right : α
  decompose : x = op left right
  left_dist : left ≡{n}≡ y₁
  right_dist : right ≡{n}≡ y₂

class CMRA (α : Type u) [OFE α] where
  pcore : α → Option α
  op : α → α → α
  validN : Nat → α → Prop
  valid : α → Prop

  op_ne : ∀ x, NonExpansive (op x)
  pcore_ne : ∀ {n x y cx}, x ≡{n}≡ y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy
  pcore_none_ne : ∀ {n x y}, x ≡{n}≡ y → pcore x = none → pcore y = none
  validN_ne : ∀ {n x y}, x ≡{n}≡ y → validN n x → validN n y

  valid_iff_validN : ∀ {x}, valid x ↔ ∀ n, validN n x
  validN_succ : ∀ {n x}, validN (n + 1) x → validN n x
  validN_op_left : ∀ {n x y}, validN n (op x y) → validN n x

  assoc : ∀ x y z, op x (op y z) = op (op x y) z
  comm : ∀ x y, op x y = op y x

  pcore_op_left : ∀ {x cx}, pcore x = some cx → op cx x = x
  pcore_idem : ∀ {x cx}, pcore x = some cx → pcore cx = some cx
  pcore_op_mono : ∀ {x cx}, pcore x = some cx → ∀ y,
    ∃ cy, pcore (op x y) = some (op cx cy)

  extend : ∀ {n x y₁ y₂}, validN n x → x ≡{n}≡ op y₁ y₂ →
    CMRAExtension op n x y₁ y₂

namespace CMRA

variable {α : Type u} [OFE α] [CMRA α]

infixl:60 " ⋅ " => CMRA.op
prefix:50 "✓ " => CMRA.valid
notation:50 "✓{" n "} " x:51 => CMRA.validN n x

def Included (x y : α) : Prop := ∃ z, y = x ⋅ z
infix:50 " ≼ " => Included

def IncludedN (n : Nat) (x y : α) : Prop := ∃ z, y ≡{n}≡ x ⋅ z
notation:50 x " ≼{" n "} " y:51 => IncludedN n x y

theorem op_assoc (x y z : α) : x ⋅ (y ⋅ z) = (x ⋅ y) ⋅ z :=
  CMRA.assoc x y z

theorem op_comm (x y : α) : x ⋅ y = y ⋅ x :=
  CMRA.comm x y

theorem op_ne_right (x : α) : NonExpansive (x ⋅ ·) :=
  CMRA.op_ne x

theorem op_ne_left (y : α) : NonExpansive (fun x => x ⋅ y) := by
  intro n x₁ x₂ h
  change x₁ ⋅ y ≡{n}≡ x₂ ⋅ y
  rw [op_comm x₁ y, op_comm x₂ y]
  exact CMRA.op_ne y n h

theorem op_ne₂ : NonExpansive₂ (CMRA.op : α → α → α) := by
  intro n x₁ x₂ hx y₁ y₂ hy
  exact OFE.trans (op_ne_left y₁ n hx) (op_ne_right x₂ n hy)

theorem validN_mono {n m : Nat} {x : α} (hnm : n ≤ m) :
    ✓{m} x → ✓{n} x := by
  intro hv
  induction hnm with
  | refl => exact hv
  | @step m hnm ih => exact ih (CMRA.validN_succ hv)

theorem validN_of_valid {x : α} (h : ✓ x) (n : Nat) : ✓{n} x :=
  CMRA.valid_iff_validN.mp h n

end CMRA

class UCMRA (α : Type u) [OFE α] [CMRA α] where
  unit : α
  unit_valid : CMRA.valid unit
  unit_left : ∀ x, CMRA.op unit x = x
  pcore_unit : CMRA.pcore unit = some unit

namespace UCMRA

variable {α : Type u} [OFE α] [CMRA α] [UCMRA α]

theorem unit_right (x : α) : CMRA.op x UCMRA.unit = x := by
  rw [CMRA.comm]
  exact UCMRA.unit_left x

end UCMRA

/-! A minimal but genuine CMRA instance used to test the complete interface. -/

instance unitCMRA : CMRA Unit where
  pcore _ := some ()
  op _ _ := ()
  validN _ _ := True
  valid _ := True
  op_ne _ := by intro n x y h; exact OFE.refl n ()
  pcore_ne := by
    intro n x y cx hxy hcore
    cases cx
    exact ⟨(), rfl, OFE.refl n ()⟩
  pcore_none_ne := by intro n x y hxy hnone; contradiction
  validN_ne := by intro n x y hxy hv; trivial
  valid_iff_validN := by
    intro x
    constructor
    · intro h n; trivial
    · intro h; trivial
  validN_succ := by intro n x h; trivial
  validN_op_left := by intro n x y h; trivial
  assoc := by intro x y z; rfl
  comm := by intro x y; rfl
  pcore_op_left := by intro x cx h; rfl
  pcore_idem := by intro x cx h; cases x; cases cx; rfl
  pcore_op_mono := by
    intro x cx h y
    exact ⟨(), rfl⟩
  extend := by
    intro n x y₁ y₂ hv heq
    exact {
      left := ()
      right := ()
      decompose := rfl
      left_dist := OFE.refl n ()
      right_dist := OFE.refl n ()
    }

instance unitUCMRA : UCMRA Unit where
  unit := ()
  unit_valid := trivial
  unit_left := by intro x; rfl
  pcore_unit := rfl

end LeanIrisX
