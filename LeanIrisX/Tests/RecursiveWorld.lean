import LeanIrisX.Logic.RecursiveWorld

namespace LeanIrisX.Tests.RecursiveWorld

open LeanIrisX

#synth OFunctor InvariantRegistryF
#synth OFunctorContractive InvariantRegistryF
#synth UCMRAFunctor InvariantRegistryF
#synth OFunctor WorldPlugin
#synth OFunctorContractive WorldPlugin
#synth UCMRAFunctor WorldPlugin
#synth OFE WorldIris.IRes
#synth CMRA WorldIris.IRes
#synth UCMRA WorldIris.IRes

def N₁ : Namespace := [1]
def N₂ : Namespace := [2]

theorem names_are_distinct : N₁ ≠ N₂ := by decide

theorem two_names_can_coexist (P Q : WorldIris.IPre) :
    CMRA.valid (CMRA.op (WorldIris.invariantSlot N₁ P)
      (WorldIris.invariantSlot N₂ Q)) :=
  WorldIris.distinct_invariants_compatible names_are_distinct P Q

theorem one_name_cannot_have_two_bodies (P Q : WorldIris.IPre) :
    ¬ CMRA.valid (CMRA.op (WorldIris.invariantSlot N₁ P)
      (WorldIris.invariantSlot N₁ Q)) :=
  WorldIris.same_invariant_conflicts N₁ P Q

theorem recursive_world_fold_unfold (P : WorldIris.IProp) :
    WorldIris.fold (WorldIris.unfold P) = P := WorldIris.fold_unfold P

end LeanIrisX.Tests.RecursiveWorld
