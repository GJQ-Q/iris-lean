import LeanIrisX.Algebra.Auth

namespace LeanIrisX.Tests.Auth

open LeanIrisX

def authoritativeUnit : Auth Unit := Auth.authoritative ()
def fragmentUnit : Auth Unit := Auth.fragment ()

example : CMRA (Auth Unit) := inferInstance
example : UCMRA (Auth Unit) := inferInstance

theorem authoritative_fragment_valid (n : Nat) :
    CMRA.validN n (CMRA.op authoritativeUnit fragmentUnit) := by
  apply Auth.authoritative_fragment_validN.mpr
  exact ⟨trivial, ⟨(), OFE.refl n ()⟩⟩

theorem fragment_is_included (n : Nat) :
    CMRA.IncludedN n (() : Unit) () :=
  Auth.fragment_includedN (authoritative_fragment_valid n)

theorem fragment_is_valid (n : Nat) : CMRA.validN n (() : Unit) :=
  Auth.fragment_validN (authoritative_fragment_valid n)

theorem authoritative_update_refl :
    CMRA.FramePreservingUpdate authoritativeUnit authoritativeUnit := by
  apply Auth.authoritative_update
  intro n frame h
  exact h

end LeanIrisX.Tests.Auth
