import LeanIrisX.Algebra.Auth
import LeanIrisX.Algebra.LocalUpdate

/-! Lifting fragment local updates through View and Auth. -/

namespace LeanIrisX.View

variable {A : Type u} {B : Type v}
variable [OFE A] [OFE B] [CMRA B] [UCMRA B]
variable {R : ViewRel A B} [IsViewRel R]

private theorem cmraOp_eq (x y : View R) : CMRA.op x y = op x y := rfl

/-- Official-shaped View local-update lifting rule. -/
theorem localUpdate {a a' : A} {b0 b1 b0' b1' : B}
    (hup : CMRA.LocalUpdate (b0, b1) (b0', b1'))
    (hrel : ∀ n, R n a b0 → R n a' b0') :
    CMRA.LocalUpdate
      (op (FullAuth (R := R) a) (Frag (R := R) b0),
       op (FullAuth (R := R) a) (Frag (R := R) b1))
      (op (FullAuth (R := R) a') (Frag (R := R) b0'),
       op (FullAuth (R := R) a') (Frag (R := R) b1')) := by
  apply CMRA.localUpdate_iff_total.mpr
  intro n frame hv heq
  cases frame with
  | mk frameAuth frameFrag =>
    cases frameAuth with
    | none =>
      have hr : R n a b0 := (auth_one_frag_validN_iff n a b0).mp hv
      have hb0 : CMRA.validN n b0 := IsViewRel.rel_validN n a b0 hr
      have hop :
          (CMRA.op
            (op (FullAuth (R := R) a) (Frag (R := R) b1))
            { auth := none, frag := frameFrag }).frag =
          CMRA.op b1 frameFrag := by
        simp [cmraOp_eq, op, FullAuth, Auth, Frag, UCMRA.unit_left]
      have hleft :
          (op (FullAuth (R := R) a) (Frag (R := R) b0)).frag = b0 := by
        simp [op, FullAuth, Auth, Frag, UCMRA.unit_left]
      have hfrag := heq.2
      rw [hleft, hop] at hfrag
      obtain ⟨hb0', hfrag'⟩ :=
        CMRA.localUpdate_iff_total.mp hup n frameFrag hb0 hfrag
      constructor
      · exact (auth_one_frag_validN_iff n a' b0').mpr (hrel n hr)
      · refine ⟨OFE.refl n _, ?_⟩
        have hop' :
            (CMRA.op
              (op (FullAuth (R := R) a') (Frag (R := R) b1'))
              { auth := none, frag := frameFrag }).frag =
            CMRA.op b1' frameFrag := by
          simp [cmraOp_eq, op, FullAuth, Auth, Frag, UCMRA.unit_left]
        have hleft' :
            (op (FullAuth (R := R) a') (Frag (R := R) b0')).frag = b0' := by
          simp [op, FullAuth, Auth, Frag, UCMRA.unit_left]
        rw [hleft', hop']
        exact hfrag'
    | some frameAuth =>
      rcases frameAuth with ⟨dq, ag⟩
      have hcombined : CMRA.validN n
          (op (op (FullAuth (R := R) a) (Frag (R := R) b1))
            { auth := some (dq, ag), frag := frameFrag }) :=
        CMRA.validN_ne heq hv
      have hdq : CMRA.validN n (CMRA.op (DFrac.own DFrac.one) dq) :=
        hcombined.1
      exact False.elim (DFrac.full_op_invalidN n dq hdq)

end LeanIrisX.View

namespace LeanIrisX.Auth

variable {A : Type u} [OFE A] [CMRA A] [UCMRA A]

/-- Lift a fragment local update to the public authoritative camera. -/
theorem localUpdate {a a' b0 b1 b0' b1' : A}
    (hup : CMRA.LocalUpdate (b0, b1) (b0', b1'))
    (hrel : ∀ n, AuthViewRel n a b0 → AuthViewRel n a' b0') :
    CMRA.LocalUpdate
      (CMRA.op (authoritative a) (fragment b0),
       CMRA.op (authoritative a) (fragment b1))
      (CMRA.op (authoritative a') (fragment b0'),
       CMRA.op (authoritative a') (fragment b1')) :=
  View.localUpdate hup hrel

end LeanIrisX.Auth
