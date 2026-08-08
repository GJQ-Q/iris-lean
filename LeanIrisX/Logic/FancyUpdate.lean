import LeanIrisX.Logic.Mask
import LeanIrisX.Logic.Classes

/-! Abstract fancy-update interface. An implementation must prove every law;
declaring this class does not postulate an instance for `UPred`. -/

namespace LeanIrisX
open BI

class FancyUpdate (PROP : Type u) where
  fupd : Mask → Mask → PROP → PROP

namespace FancyUpdate

variable {PROP : Type u} [BIBase PROP] [FancyUpdate PROP]

def apply (E₁ E₂ : Mask) (P : PROP) : PROP := FancyUpdate.fupd E₁ E₂ P

class Laws (PROP : Type u) [BIBase PROP] [FancyUpdate PROP] : Prop where
  intro : ∀ (E : Mask) (P : PROP), P ⊢ apply E E P
  mono : ∀ {E₁ E₂ : Mask} {P Q : PROP}, P ⊢ Q → apply E₁ E₂ P ⊢ apply E₁ E₂ Q
  trans : ∀ (E₁ E₂ E₃ : Mask) (P : PROP),
    apply E₁ E₂ (apply E₂ E₃ P) ⊢ apply E₁ E₃ P
  frame : ∀ (E₁ E₂ : Mask) (P R : PROP),
    BIBase.sep (apply E₁ E₂ P) R ⊢ apply E₁ E₂ (BIBase.sep P R)
  mask_frame : ∀ {E₁ E₂ Ef : Mask}, Mask.Disjoint E₁ Ef →
    Mask.Disjoint E₂ Ef → ∀ P : PROP,
      apply E₁ E₂ P ⊢ apply (Mask.union E₁ Ef) (Mask.union E₂ Ef) P

end FancyUpdate
end LeanIrisX
