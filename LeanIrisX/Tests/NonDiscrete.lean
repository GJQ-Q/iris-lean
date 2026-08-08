import LeanIrisX.Core.Later

namespace LeanIrisX.Tests.NonDiscrete

open LeanIrisX

def laterTrue : Later Bool := ⟨true⟩
def laterFalse : Later Bool := ⟨false⟩

/-- At depth zero, a later value reveals nothing. -/
theorem hidden_at_zero : laterTrue ≡{0}≡ laterFalse :=
  Later.dist_zero _ _

/-- At depth one, the underlying discrete Boolean becomes observable. -/
theorem visible_at_one : ¬ laterTrue ≡{1}≡ laterFalse := by
  intro h
  have hbool : true ≡{0}≡ false :=
    (Later.dist_succ_iff (n := 0)).mp h
  exact Bool.noConfusion (OFE.Discrete.eq_of_dist hbool)

example : OFE (Later Bool) := inferInstance
example : COFE (Later Bool) := inferInstance
example : Contractive (Later.next : Bool → Later Bool) := Later.next_contractive

end LeanIrisX.Tests.NonDiscrete

