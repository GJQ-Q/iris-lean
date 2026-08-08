import LeanIrisX.Logic.UPredGhost

namespace LeanIrisX.Tests.GlobalResource
open LeanIrisX LeanIrisX.UPred LeanIrisX.UPredGhost

def unitAtSeven : GhostMap Unit := GhostMap.singleton 7 ()

theorem unitAtSeven_valid : CMRA.valid unitAtSeven := by
  intro γ
  trivial

theorem named_unit_composes :
    namedOwn (A := Unit) 7 (CMRA.op () ()) ⊢ᵤ
      UPred.sep (namedOwn 7 ()) (namedOwn 7 ()) :=
  namedOwn_op 7 () ()

theorem named_unit_is_step_valid :
    namedOwn (A := Unit) 7 () ⊢ᵤ validProp () :=
  namedOwn_valid 7 ()

end LeanIrisX.Tests.GlobalResource
