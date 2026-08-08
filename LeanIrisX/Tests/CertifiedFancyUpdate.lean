import LeanIrisX.Logic.CertifiedFancyUpdate

namespace LeanIrisX.Tests.CertifiedFancyUpdate

open LeanIrisX UPred

abbrev PROP := UPred Unit

def Elarge : Mask := Mask.full
def Esmall : Mask := Mask.empty

example : CertifiedFancyUpdate.Admissible Elarge Esmall := by
  intro N h
  exact False.elim h

theorem shrinking_update_is_available (P : PROP) :
    P ⊢ᵤ FancyUpdate.apply Elarge Esmall P := by
  intro n x hx hp
  exact ⟨by intro N h; exact False.elim h,
    UPred.basicUpdate_intro P n x hx hp⟩

theorem unsupported_enlargement_is_impossible (P : PROP) :
    ¬ ((FancyUpdate.apply Esmall Elarge P).holdsAt 0 ()
      (CMRA.validN_of_valid UCMRA.unit_valid 0)) := by
  intro h
  exact h.1 Namespace.root trivial

theorem certified_updates_compose (P : PROP) :
    FancyUpdate.apply Elarge Elarge (FancyUpdate.apply Elarge Esmall P)
      ⊢ᵤ FancyUpdate.apply Elarge Esmall P :=
  FancyUpdate.Laws.trans Elarge Elarge Esmall P

theorem certified_update_frames (P R : PROP) :
    UPred.sep (FancyUpdate.apply Elarge Esmall P) R
      ⊢ᵤ FancyUpdate.apply Elarge Esmall (UPred.sep P R) :=
  FancyUpdate.Laws.frame Elarge Esmall P R

end LeanIrisX.Tests.CertifiedFancyUpdate
