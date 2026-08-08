import LeanIrisX.Algebra.MaskToken
import LeanIrisX.Logic.Ownership

/-! Concrete enabled/disabled mask ownership over the disjoint mask camera. -/

namespace LeanIrisX
namespace MaskOwnership

abbrev MaskProp := UPred MaskToken

noncomputable def ownE (E : Mask) : MaskProp :=
  UPred.own (MaskToken.ofMask E)

noncomputable def ownD (E : Mask) : MaskProp :=
  UPred.own (MaskToken.ofMask E)

theorem ownE_split {E F : Mask} (h : Mask.Disjoint E F) :
    ownE (Mask.union E F) ⊢ᵤ UPred.sep (ownE E) (ownE F) := by
  rw [ownE, MaskToken.ofMask_union E F h]
  exact UPred.own_op_sep _ _

theorem ownE_combine {E F : Mask} (h : Mask.Disjoint E F) :
    UPred.sep (ownE E) (ownE F) ⊢ᵤ ownE (Mask.union E F) := by
  change UPred.sep (UPred.own (MaskToken.ofMask E))
      (UPred.own (MaskToken.ofMask F)) ⊢ᵤ
    UPred.own (MaskToken.ofMask (Mask.union E F))
  rw [MaskToken.ofMask_union E F h]
  exact UPred.sep_own_op _ _

theorem ownD_split {E F : Mask} (h : Mask.Disjoint E F) :
    ownD (Mask.union E F) ⊢ᵤ UPred.sep (ownD E) (ownD F) := by
  rw [ownD, MaskToken.ofMask_union E F h]
  exact UPred.own_op_sep _ _

theorem ownD_combine {E F : Mask} (h : Mask.Disjoint E F) :
    UPred.sep (ownD E) (ownD F) ⊢ᵤ ownD (Mask.union E F) := by
  change UPred.sep (UPred.own (MaskToken.ofMask E))
      (UPred.own (MaskToken.ofMask F)) ⊢ᵤ
    UPred.own (MaskToken.ofMask (Mask.union E F))
  rw [MaskToken.ofMask_union E F h]
  exact UPred.sep_own_op _ _

end MaskOwnership
end LeanIrisX
