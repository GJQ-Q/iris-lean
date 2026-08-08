import LeanIrisX.Logic.GuardedResourceFunctor
import LeanIrisX.Core.OFunctorProduct
import LeanIrisX.Algebra.GhostMap

/-!
An extensible Iris resource signature. A client supplies a lawful, locally
contractive UCMRA functor `G`; the library combines it with the guarded core and
solves the resulting recursive proposition equation.
-/

namespace LeanIrisX

abbrev IrisResourceF (G : OFunctorPre) := ProductOF GuardedResourceF G
abbrev IrisPropF (G : OFunctorPre) [OFunctor G] [UCMRAFunctor G] :=
  UPredOF (IrisResourceF G)

namespace ExtensibleIris

variable (G : OFunctorPre) [OFunctor G] [OFunctorContractive G]
  [UCMRAFunctor G]

def seed : COFETower.Stage (IrisPropF G) 1 := UPred.top
abbrev IPre := COFETower.Fix (IrisPropF G) (seed G)
abbrev IRes := IrisResourceF G (IPre G) (IPre G)
abbrev IProp := UPred (IRes G)

def fold : IPre G -n> IProp G :=
  COFETower.Fix.unfold (IrisPropF G) (seed G)

def unfold : IProp G -n> IPre G :=
  COFETower.Fix.fold (IrisPropF G) (seed G)

theorem fold_unfold (P : IProp G) : fold G (unfold G P) = P :=
  COFETower.Fix.unfold_fold (IrisPropF G) (seed G) P

theorem unfold_fold (X : IPre G) : unfold G (fold G X) = X :=
  COFETower.Fix.fold_unfold (IrisPropF G) (seed G) X

end ExtensibleIris

/-! A concrete client plugin: a named map of duplicable unit tokens. -/
abbrev UnitGhostPlugin : OFunctorPre := OFunctor.Const (GhostMap Unit)

namespace UnitGhostIris

abbrev IPre := ExtensibleIris.IPre UnitGhostPlugin
abbrev IRes := ExtensibleIris.IRes UnitGhostPlugin
abbrev IProp := ExtensibleIris.IProp UnitGhostPlugin

def guardedSlot (x : IPre) : IRes :=
  (GuardedExcl.own (Later.next x), UCMRA.unit)

def pluginSlot (γ : GhostName) : IRes :=
  (UCMRA.unit, GhostMap.singleton γ ())

def fold : IPre -n> IProp := ExtensibleIris.fold UnitGhostPlugin
def unfold : IProp -n> IPre := ExtensibleIris.unfold UnitGhostPlugin

theorem fold_unfold (P : IProp) : fold (unfold P) = P :=
  ExtensibleIris.fold_unfold UnitGhostPlugin P

theorem unfold_fold (X : IPre) : unfold (fold X) = X :=
  ExtensibleIris.unfold_fold UnitGhostPlugin X

end UnitGhostIris
end LeanIrisX
