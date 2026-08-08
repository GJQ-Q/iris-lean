import LeanIrisX.Logic.ExtensibleResource

namespace LeanIrisX.Tests.ExtensibleResource

open LeanIrisX

#synth OFunctor UnitGhostPlugin
#synth OFunctorContractive UnitGhostPlugin
#synth UCMRAFunctor UnitGhostPlugin
#synth OFunctor (IrisResourceF UnitGhostPlugin)
#synth OFunctorContractive (IrisResourceF UnitGhostPlugin)
#synth UCMRAFunctor (IrisResourceF UnitGhostPlugin)
#synth OFE UnitGhostIris.IRes
#synth CMRA UnitGhostIris.IRes
#synth UCMRA UnitGhostIris.IRes

theorem core_and_plugin_compose (X : UnitGhostIris.IPre) (γ : GhostName) :
    CMRA.op (UnitGhostIris.guardedSlot X) (UnitGhostIris.pluginSlot γ) =
      (GuardedExcl.own (Later.next X), GhostMap.singleton γ ()) := by
  apply Prod.ext <;> rfl

theorem recursive_fold_unfold (P : UnitGhostIris.IProp) :
    UnitGhostIris.fold (UnitGhostIris.unfold P) = P :=
  UnitGhostIris.fold_unfold P

theorem recursive_unfold_fold (X : UnitGhostIris.IPre) :
    UnitGhostIris.unfold (UnitGhostIris.fold X) = X :=
  UnitGhostIris.unfold_fold X

end LeanIrisX.Tests.ExtensibleResource
