import LeanIrisX.Algebra.ViewUpdate
import LeanIrisX.Tests.View

namespace LeanIrisX.Tests.ViewUpdate

open LeanIrisX
open LeanIrisX.Tests.View

theorem relation_stable (n : Nat) (frame : Unit)
    (h : AuthViewRel n (() : Unit) frame) :
    AuthViewRel n (() : Unit) frame := h

theorem authority_update_refl :
    CMRA.FramePreservingUpdate authority authority := by
  exact LeanIrisX.View.full_auth_update (R := AuthViewRel (A := Unit))
    (fun n frame h => relation_stable n frame h)

theorem allocate_unit_fragment :
    CMRA.FramePreservingUpdate authority
      (LeanIrisX.View.op authority fragment) := by
  apply LeanIrisX.View.full_auth_alloc (R := AuthViewRel (A := Unit))
  intro n frame h
  simpa using h

theorem deallocate_unit_fragment :
    CMRA.FramePreservingUpdate
      (LeanIrisX.View.op authority fragment) authority := by
  apply LeanIrisX.View.full_auth_dealloc (R := AuthViewRel (A := Unit))
  intro n frame h
  simpa using h

end LeanIrisX.Tests.ViewUpdate
