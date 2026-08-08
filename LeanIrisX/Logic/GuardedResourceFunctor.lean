import LeanIrisX.Logic.UPredFunctor
import LeanIrisX.Algebra.GuardedExclusive
import LeanIrisX.Core.COFETower

namespace LeanIrisX

universe u

/-- A resource functor whose recursive payload occurs strictly below `Later`. -/
abbrev GuardedResourceF : OFunctorPre := fun _ B _ _ _ _ => GuardedExcl B

namespace GuardedResourceF

instance instOFunctor : OFunctor GuardedResourceF where
  ofe _ B := inferInstanceAs (OFE (GuardedExcl B))
  cofe _ B := inferInstanceAs (COFE (GuardedExcl B))
  map _ g := {
    toFun := GuardedExcl.map g
    nonExpansive := GuardedExcl.map_nonExpansive g g.nonExpansive
  }
  map_ne n f₁ f₂ g₁ g₂ hf hg x := by
    cases x with
    | unit => simp [GuardedExcl.map, GuardedExcl.Dist]
    | invalid => simp [GuardedExcl.map, GuardedExcl.Dist]
    | own x =>
      change Later.map g₁ x ≡{n}≡ Later.map g₂ x
      intro m hm
      exact OFE.mono (Nat.le_of_lt hm) (hg x.prev)
  map_id x := GuardedExcl.map_id x
  map_comp f g f' g' x := by cases x <;> rfl

instance instContractive : OFunctorContractive GuardedResourceF where
  map_contractive n f₁ f₂ g₁ g₂ hf hg x := by
    cases x with
    | unit => exact OFE.refl n _
    | invalid => exact OFE.refl n _
    | own x =>
      change Later.map g₁ x ≡{n}≡ Later.map g₂ x
      intro m hm
      exact hg m hm x.prev

instance instUCMRAFunctor : UCMRAFunctor GuardedResourceF where
  cmra _ B := inferInstanceAs (CMRA (GuardedExcl B))
  ucmra _ B := inferInstanceAs (UCMRA (GuardedExcl B))
  map_validN _ g := GuardedExcl.map_validN g
  map_op _ g := GuardedExcl.map_op g

end GuardedResourceF

abbrev GuardedPropF : OFunctorPre := UPredOF GuardedResourceF

namespace RecursiveIProp

def seed : COFETower.Stage GuardedPropF 1 := UPred.top
abbrev IPre := COFETower.Fix GuardedPropF seed
abbrev IRes := GuardedExcl IPre
abbrev IProp := UPred IRes

def fold : IPre -n> IProp := COFETower.Fix.unfold GuardedPropF seed
def unfold : IProp -n> IPre := COFETower.Fix.fold GuardedPropF seed

theorem fold_unfold (P : IProp) : fold (unfold P) = P :=
  COFETower.Fix.unfold_fold GuardedPropF seed P

theorem unfold_fold (X : IPre) : unfold (fold X) = X :=
  COFETower.Fix.fold_unfold GuardedPropF seed X

end RecursiveIProp
end LeanIrisX
