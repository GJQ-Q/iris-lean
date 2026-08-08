import LeanIrisX.Algebra.View

namespace LeanIrisX.Tests.View

open LeanIrisX

abbrev UnitView := LeanIrisX.View (AuthViewRel (A := Unit))

def authority : UnitView :=
  LeanIrisX.View.Auth (R := AuthViewRel (A := Unit)) (DFrac.own DFrac.one) ()

def fragment : UnitView :=
  LeanIrisX.View.Frag (R := AuthViewRel (A := Unit)) ()

theorem relation_holds (n : Nat) : AuthViewRel n (() : Unit) () := by
  exact ⟨trivial, ⟨(), OFE.refl n ()⟩⟩

theorem authority_fragment_validN (n : Nat) :
    LeanIrisX.View.ValidN n (LeanIrisX.View.op authority fragment) :=
  (LeanIrisX.View.auth_one_frag_validN_iff n () ()).2 (relation_holds n)

example : CMRA UnitView := inferInstance
example : UCMRA UnitView := inferInstance

theorem authority_fragment_cmra_validN (n : Nat) :
    CMRA.validN n (LeanIrisX.View.op authority fragment) :=
  authority_fragment_validN n

theorem view_unit_valid : CMRA.valid (UCMRA.unit : UnitView) :=
  UCMRA.unit_valid

theorem view_operation_commutes :
    LeanIrisX.View.op authority fragment =
      LeanIrisX.View.op fragment authority :=
  LeanIrisX.View.op_comm _ _

end LeanIrisX.Tests.View
