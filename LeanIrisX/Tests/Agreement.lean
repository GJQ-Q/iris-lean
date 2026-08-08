import LeanIrisX.Algebra.Agreement

namespace LeanIrisX.Tests.Agreement

open LeanIrisX

def t : Agreement (Later Bool) := Agreement.toAgreement (Later.next true)
def f : Agreement (Later Bool) := Agreement.toAgreement (Later.next false)

example : OFE (Agreement (Later Bool)) := inferInstance
example : CMRA (Agreement (Later Bool)) := inferInstance

theorem op_commutes : CMRA.op t f = CMRA.op f t :=
  Agreement.op_comm _ _

theorem combined_valid_zero : CMRA.validN 0 (CMRA.op t f) := by
  apply Agreement.toAgreement_op_valid_iff.mpr
  exact Later.dist_zero _ _

theorem combined_invalid_one : ¬ CMRA.validN 1 (CMRA.op t f) := by
  intro h
  have htf : Later.next true ≡{1}≡ Later.next false :=
    Agreement.toAgreement_op_valid_iff.mp h
  have hbool : true ≡{0}≡ false :=
    (Later.dist_succ_iff (n := 0)).mp htf
  exact Bool.noConfusion (OFE.Discrete.eq_of_dist hbool)

theorem duplicate_valid (x : Agreement (Later Bool)) {n : Nat}
    (hx : CMRA.validN n x) : CMRA.validN n (CMRA.op x x) := by
  change Agreement.validN n x at hx
  change Agreement.validN n (Agreement.op x x)
  rw [Agreement.op_idem]
  exact hx

end LeanIrisX.Tests.Agreement
