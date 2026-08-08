import LeanIrisX.Logic.RecursiveWorldV2

namespace LeanIrisX.Tests.RecursiveWorldV2

open LeanIrisX

def N : Namespace := [9]

#synth OFunctor NamedInvariantRegistryF
#synth OFunctorContractive NamedInvariantRegistryF
#synth UCMRAFunctor NamedInvariantRegistryF
#synth OFunctor WorldPluginV2
#synth OFunctorContractive WorldPluginV2
#synth UCMRAFunctor WorldPluginV2

theorem two_invariants_share_namespace (P Q : WorldIrisV2.IPre) :
    CMRA.valid (CMRA.op
      (WorldIrisV2.registrySlot N 20 P)
      (WorldIrisV2.registrySlot N 21 Q)) :=
  WorldIrisV2.same_namespace_distinct_ids_compatible (by decide) N P Q

theorem reused_identity_conflicts (P Q : WorldIrisV2.IPre) :
    ¬ CMRA.valid (CMRA.op
      (WorldIrisV2.registrySlot N 20 P)
      (WorldIrisV2.registrySlot N 20 Q)) :=
  WorldIrisV2.same_id_conflicts N 20 P Q

theorem public_handle_duplicates :
    CMRA.op (WorldIrisV2.handleSlot 20) (WorldIrisV2.handleSlot 20) =
      WorldIrisV2.handleSlot 20 :=
  WorldIrisV2.handle_slot_idem 20

end LeanIrisX.Tests.RecursiveWorldV2
