import LeanIrisX.Algebra.LocalUpdate

namespace LeanIrisX.Tests.LocalUpdate

open LeanIrisX

theorem unit_local_update :
    CMRA.LocalUpdate (((), ()) : Unit × Unit) (((), ()) : Unit × Unit) :=
  CMRA.localUpdate_unit _ _

theorem local_update_composes {x y z : Unit × Unit}
    (hxy : CMRA.LocalUpdate x y) (hyz : CMRA.LocalUpdate y z) :
    CMRA.LocalUpdate x z :=
  CMRA.localUpdate_trans hxy hyz

theorem unital_characterization_available {x y : Unit × Unit}
    (h : CMRA.LocalUpdate x y) :
    ∀ n frame, CMRA.validN n x.1 →
      OFE.dist n x.1 (CMRA.op x.2 frame) →
      CMRA.validN n y.1 ∧ OFE.dist n y.1 (CMRA.op y.2 frame) :=
  CMRA.localUpdate_iff_total.mp h

end LeanIrisX.Tests.LocalUpdate
