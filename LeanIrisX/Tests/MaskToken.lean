import LeanIrisX.Algebra.MaskToken

namespace LeanIrisX.Tests.MaskToken

open LeanIrisX

def left : Mask := Mask.singleton [1]
def right : Mask := Mask.singleton [2]

theorem left_right_disjoint : Mask.Disjoint left right := by
  intro N hL hR
  simp [left, right, Mask.singleton] at hL hR
  subst N
  contradiction

theorem disjoint_tokens_compose :
    CMRA.valid (CMRA.op (MaskToken.ofMask left) (MaskToken.ofMask right)) :=
  (MaskToken.ofMask_op_valid_iff_disjoint left right).2 left_right_disjoint

theorem union_token_splits :
    MaskToken.ofMask (Mask.union left right) =
      CMRA.op (MaskToken.ofMask left) (MaskToken.ofMask right) :=
  MaskToken.ofMask_union left right left_right_disjoint

theorem duplicate_token_conflicts :
    ¬ CMRA.valid (CMRA.op (MaskToken.ofMask left) (MaskToken.ofMask left)) :=
  MaskToken.singleton_conflict [1]

end LeanIrisX.Tests.MaskToken
