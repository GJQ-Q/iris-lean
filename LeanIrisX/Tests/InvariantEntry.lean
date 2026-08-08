import LeanIrisX.Algebra.InvariantEntry

namespace LeanIrisX.Tests.InvariantEntry

open LeanIrisX

theorem registry_cell_forces_body_agreement {n : Nat} {P Q : Later Nat}
    (h : CMRA.validN (n + 1)
      (CMRA.op (InvariantEntry.allocated P) (InvariantEntry.allocated Q))) :
    P ≡{n}≡ Q :=
  InvariantEntry.allocated_op_valid_succ_iff.mp h

theorem registry_cell_allows_duplicate_same_body (n : Nat) (P : Later Nat) :
    CMRA.validN n
      (CMRA.op (InvariantEntry.allocated P) (InvariantEntry.allocated P)) := by
  rw [InvariantEntry.allocated_op_validN_iff]
  exact OFE.refl n _

end LeanIrisX.Tests.InvariantEntry
