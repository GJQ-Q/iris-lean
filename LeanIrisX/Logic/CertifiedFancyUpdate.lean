import LeanIrisX.Logic.FancyUpdate
import LeanIrisX.Logic.Modalities

/-!
# Certified mask-changing updates

This module supplies the first concrete `FancyUpdate` instance.  A transition
from `E₁` to `E₂` carries an explicit proof that `E₂ ⊆ E₁`, together with a
frame-preserving basic update.  Thus masks are semantically relevant: an
unsupported mask enlargement denotes false, rather than being silently
ignored.

This is the conservative mask-transition core.  Opening an invariant and then
restoring its mask is deliberately left to the world-satisfaction layer; it is
not postulated here.
-/

namespace LeanIrisX

namespace CertifiedFancyUpdate

variable {M : Type u} [OFE M] [CMRA M] [UCMRA M]

/-- A mask change is admissible when the target mask is contained in the
source mask. -/
def Admissible (E₁ E₂ : Mask) : Prop := E₂ ⊆ₘ E₁

theorem admissible_refl (E : Mask) : Admissible E E := Mask.subset_refl E

theorem admissible_trans {E₁ E₂ E₃ : Mask}
    (h₁₂ : Admissible E₁ E₂) (h₂₃ : Admissible E₂ E₃) :
    Admissible E₁ E₃ := Mask.subset_trans h₂₃ h₁₂

theorem admissible_frame {E₁ E₂ Ef : Mask}
    (h : Admissible E₁ E₂) :
    Admissible (Mask.union E₁ Ef) (Mask.union E₂ Ef) := by
  intro N hN
  rcases hN with hN | hN
  · exact Or.inl (h N hN)
  · exact Or.inr hN

/-- A certified fancy update is a frame-preserving update guarded by a real
mask-transition certificate. -/
def fupd (E₁ E₂ : Mask) (P : UPred M) : UPred M where
  holds n x := Admissible E₁ E₂ ∧ (UPred.basicUpdate P).holds n x
  mono := by
    intro n₁ n₂ x₁ x₂ h hinc hle
    exact ⟨h.1, (UPred.basicUpdate P).mono h.2 hinc hle⟩

instance : FancyUpdate (UPred M) where
  fupd := fupd

theorem apply_eq (E₁ E₂ : Mask) (P : UPred M) :
    FancyUpdate.apply E₁ E₂ P = fupd E₁ E₂ P := rfl

theorem intro (E : Mask) (P : UPred M) :
    P ⊢ᵤ fupd E E P := by
  intro n x hx hp
  exact ⟨admissible_refl E, UPred.basicUpdate_intro P n x hx hp⟩

theorem mono {E₁ E₂ : Mask} {P Q : UPred M} (hPQ : P ⊢ᵤ Q) :
    fupd E₁ E₂ P ⊢ᵤ fupd E₁ E₂ Q := by
  intro n x hx h
  exact ⟨h.1, UPred.basicUpdate_mono hPQ n x hx h.2⟩

private theorem nested_admissible {E₂ E₃ : Mask} {P : UPred M}
    {n : Nat} {x : M} (hx : CMRA.validN n x)
    (h : (UPred.basicUpdate (fupd E₂ E₃ P)).holdsAt n x hx) :
    Admissible E₂ E₃ := by
  have hxunit : CMRA.validN n (CMRA.op x (UCMRA.unit : M)) := by
    simpa [UCMRA.unit_right] using hx
  obtain ⟨y, _, hy, hinner⟩ := h n (Nat.le_refl n) UCMRA.unit hxunit
  exact hinner.1

theorem trans (E₁ E₂ E₃ : Mask) (P : UPred M) :
    fupd E₁ E₂ (fupd E₂ E₃ P) ⊢ᵤ fupd E₁ E₃ P := by
  intro n x hx h
  have h₂₃ : Admissible E₂ E₃ :=
    nested_admissible (E₂ := E₂) (E₃ := E₃) hx h.2
  have hbb : (UPred.basicUpdate (UPred.basicUpdate P)).holdsAt n x hx :=
    UPred.basicUpdate_mono
      (show fupd E₂ E₃ P ⊢ᵤ UPred.basicUpdate P from
        fun _ _ _ hi => hi.2) n x hx h.2
  exact ⟨admissible_trans h.1 h₂₃,
    UPred.basicUpdate_trans P n x hx hbb⟩

theorem frame (E₁ E₂ : Mask) (P R : UPred M) :
    UPred.sep (fupd E₁ E₂ P) R ⊢ᵤ fupd E₁ E₂ (UPred.sep P R) := by
  intro n x hx h
  obtain ⟨a, b, hab, ha, hb, hfupd, hr⟩ := h
  have hsep : (UPred.sep (UPred.basicUpdate P) R).holdsAt n x hx :=
    ⟨a, b, hab, ha, hb, hfupd.2, hr⟩
  exact ⟨hfupd.1, UPred.basicUpdate_frame P R n x hx hsep⟩

theorem mask_frame {E₁ E₂ Ef : Mask} (_ : Mask.Disjoint E₁ Ef)
    (_ : Mask.Disjoint E₂ Ef) (P : UPred M) :
    fupd E₁ E₂ P ⊢ᵤ fupd (Mask.union E₁ Ef) (Mask.union E₂ Ef) P := by
  intro n x hx h
  exact ⟨admissible_frame h.1, h.2⟩

instance : FancyUpdate.Laws (UPred M) where
  intro := intro
  mono := mono
  trans := trans
  frame := frame
  mask_frame := mask_frame

end CertifiedFancyUpdate
end LeanIrisX
