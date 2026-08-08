import LeanIrisX.Algebra.InvariantIdentity

namespace LeanIrisX.Tests.InvariantIdentity

open LeanIrisX

def N : Namespace := [4, 2]

theorem two_invariants_can_share_namespace (P Q : Later Nat) :
    CMRA.valid (CMRA.op
      (LeanIrisX.InvariantIdentity.entry N 10 P)
      (LeanIrisX.InvariantIdentity.entry N 11 Q)) :=
  LeanIrisX.InvariantIdentity.same_namespace_distinct_ids_valid
    (by decide) N P Q

theorem public_handle_is_duplicable (P : Later Nat) :
    CMRA.op
      (LeanIrisX.InvariantIdentity.handle N 10 P)
      (LeanIrisX.InvariantIdentity.handle N 10 P) =
      LeanIrisX.InvariantIdentity.handle N 10 P :=
  LeanIrisX.InvariantIdentity.handle_op_idem N 10 P

theorem reused_identity_agrees {n : Nat} {P Q : Later Nat}
    (h : CMRA.validN (n + 1) (CMRA.op
      (LeanIrisX.InvariantIdentity.entry N 10 P)
      (LeanIrisX.InvariantIdentity.entry N 10 Q))) :
    P ≡{n}≡ Q :=
  LeanIrisX.InvariantIdentity.same_id_forces_body_agreement h

end LeanIrisX.Tests.InvariantIdentity
