import LeanIrisX.Algebra.AgreementRaw

namespace LeanIrisX.Tests.AgreementRaw

open LeanIrisX

def t : Agreement.Raw (Later Bool) := Agreement.Raw.singleton (Later.next true)
def f : Agreement.Raw (Later Bool) := Agreement.Raw.singleton (Later.next false)

theorem each_valid_zero :
    Agreement.Raw.ValidN 0 t ∧ Agreement.Raw.ValidN 0 f :=
  ⟨Agreement.Raw.singleton_validN _ _, Agreement.Raw.singleton_validN _ _⟩

/-- Distinct delayed values still agree at depth zero. -/
theorem combined_valid_zero :
    Agreement.Raw.ValidN 0 (Agreement.Raw.op t f) := by
  intro a ha b hb
  simp [t, f, Agreement.Raw.op, Agreement.Raw.singleton] at ha hb
  rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
  all_goals exact Later.dist_zero _ _

/-- The same pair becomes inconsistent when one observation step is allowed. -/
theorem combined_invalid_one :
    ¬ Agreement.Raw.ValidN 1 (Agreement.Raw.op t f) := by
  intro hv
  have hd := Agreement.Raw.op_validN_implies_dist hv
  have htf : Later.next true ≡{1}≡ Later.next false :=
    Agreement.Raw.singleton_dist_iff.mp hd
  have hbool : true ≡{0}≡ false :=
    (Later.dist_succ_iff (n := 0)).mp htf
  exact Bool.noConfusion (OFE.Discrete.eq_of_dist hbool)

end LeanIrisX.Tests.AgreementRaw
