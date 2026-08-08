import LeanIrisX.Algebra.Agreement
import LeanIrisX.Algebra.Option
import LeanIrisX.Algebra.TotalCore
import LeanIrisX.Core.Later

/-! A registry cell for an invariant body: optional agreement over a delayed body. -/

namespace LeanIrisX

instance agreementTotalCore {α : Type u} [OFE α] : TotalCore (Agreement α) where
  core x := x
  core_spec _ := rfl

instance optionTotalCore {α : Type u} [OFE α] [CMRA α] [TotalCore α] :
    TotalCore (Option α) where
  core
    | none => none
    | some x => some (TotalCore.core x)
  core_spec := by
    intro x
    cases x with
    | none => rfl
    | some x =>
      change some (CMRA.pcore x) = some (some (TotalCore.core x))
      rw [TotalCore.core_spec]

abbrev InvariantEntry (PROP : Type u) [OFE PROP] :=
  Option (Agreement (Later PROP))

namespace InvariantEntry

variable {PROP : Type u} [OFE PROP]

def allocated (P : PROP) : InvariantEntry PROP :=
  some (Agreement.toAgreement (Later.next P))

theorem allocated_validN (n : Nat) (P : PROP) :
    CMRA.validN n (allocated P) :=
  Agreement.toAgreement_validN n (Later.next P)

theorem allocated_op_validN_iff {n : Nat} {P Q : PROP} :
    CMRA.validN n (CMRA.op (allocated P) (allocated Q)) ↔
      Later.next P ≡{n}≡ Later.next Q := by
  change CMRA.validN n (CMRA.op
    (Agreement.toAgreement (Later.next P))
    (Agreement.toAgreement (Later.next Q))) ↔ _
  exact Agreement.toAgreement_op_valid_iff

theorem allocated_op_valid_succ_iff {n : Nat} {P Q : PROP} :
    CMRA.validN (n + 1) (CMRA.op (allocated P) (allocated Q)) ↔
      P ≡{n}≡ Q := by
  rw [allocated_op_validN_iff]
  exact Later.dist_succ_iff

end InvariantEntry
end LeanIrisX
