import LeanIrisX.Algebra.ViewRel

namespace LeanIrisX.Tests.ViewRel

open LeanIrisX

example : IsViewRel (AuthViewRel (A := Unit)) := inferInstance

theorem unit_authority_accepts_unit (n : Nat) :
    AuthViewRel n (() : Unit) () := by
  exact ⟨trivial, ⟨(), OFE.refl n ()⟩⟩

theorem related_fragment_is_valid {n : Nat} {a b : Unit}
    (h : AuthViewRel n a b) : CMRA.validN n b :=
  AuthViewRel.fragment_valid h

end LeanIrisX.Tests.ViewRel

