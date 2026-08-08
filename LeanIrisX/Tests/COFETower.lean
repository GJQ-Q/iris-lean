import LeanIrisX.Core.COFETower

namespace LeanIrisX.Tests.COFETower

open LeanIrisX

abbrev F := OFunctor.Const Nat

theorem stage_zero_is_unit : COFETower.Stage F 0 = Unit := rfl
theorem stage_one_is_nat : COFETower.Stage F 1 = Nat := rfl

def seed : COFETower.Stage F 1 := cast stage_one_is_nat.symm 0

theorem base_retraction (x : COFETower.Stage F 0) :
    COFETower.down F seed 0 (COFETower.up F seed 0 x) = x :=
  COFETower.down_up_zero F seed x

theorem every_stage_retracts (n : Nat) (x : COFETower.Stage F n) :
    COFETower.down F seed n (COFETower.up F seed n x) = x :=
  COFETower.down_up F seed n x

theorem every_stage_approximates [OFunctorContractive F]
    (n : Nat) (x : COFETower.Stage F (n + 2)) :
    COFETower.up F seed (n + 1) (COFETower.down F seed (n + 1) x) ≡{n}≡ x :=
  COFETower.up_down F seed n x

#synth OFE (COFETower.Tower F seed)
#synth COFE (COFETower.Tower F seed)

theorem tower_limit_observed_at
    (c : OFEChain (COFETower.Tower F seed)) (n k : Nat) :
    COFE.lim c k ≡{n}≡ c n k :=
  COFE.lim_dist c n k

abbrev Solution := COFETower.Fix F seed

#synth OFE Solution
#synth COFE Solution
#synth Inhabited Solution

theorem fold_after_unfold_is_identity (X : Solution) :
    COFETower.Fix.fold F seed (COFETower.Fix.unfold F seed X) = X :=
  COFETower.Fix.fold_unfold F seed X

theorem unfold_after_fold_is_identity (x : Nat) :
    COFETower.Fix.unfold F seed (COFETower.Fix.fold F seed x) = x :=
  COFETower.Fix.unfold_fold F seed x

def solutionIso : OFEIso (F Solution Solution) Solution :=
  COFETower.towerIso F seed

end LeanIrisX.Tests.COFETower
