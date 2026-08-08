import LeanIrisX.Logic.UPredFunctor
import LeanIrisX.Core.COFETower

namespace LeanIrisX.Tests.UPredFunctor

open LeanIrisX

abbrev ResourceF := OFunctor.Const Unit
abbrev PropF := UPredOF ResourceF

#synth UCMRAFunctor ResourceF
#synth OFunctor PropF
#synth OFunctorContractive PropF

def seed : COFETower.Stage PropF 1 := UPred.top
abbrev RecursivePropDomain := COFETower.Fix PropF seed

#synth OFE RecursivePropDomain
#synth COFE RecursivePropDomain

theorem recursive_fold_unfold (P : RecursivePropDomain) :
    COFETower.Fix.fold PropF seed (COFETower.Fix.unfold PropF seed P) = P :=
  COFETower.Fix.fold_unfold PropF seed P

theorem recursive_unfold_fold (P : UPred Unit) :
    COFETower.Fix.unfold PropF seed (COFETower.Fix.fold PropF seed P) = P :=
  COFETower.Fix.unfold_fold PropF seed P

end LeanIrisX.Tests.UPredFunctor
