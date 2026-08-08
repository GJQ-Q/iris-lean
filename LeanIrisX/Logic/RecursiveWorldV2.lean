import LeanIrisX.Logic.NamedInvariantRegistryFunctor
import LeanIrisX.Logic.ExtensibleResource

/-! Corrected recursive world: namespace and invariant identity are separate. -/

namespace LeanIrisX

abbrev InvariantHandlePlugin : OFunctorPre :=
  OFunctor.Const (GhostMap Unit)

abbrev WorldPluginV2 : OFunctorPre :=
  ProductOF NamedInvariantRegistryF
    (ProductOF InvariantHandlePlugin UnitGhostPlugin)

namespace WorldIrisV2

abbrev IPre := ExtensibleIris.IPre WorldPluginV2
abbrev Registry := NamedInvariantRegistryF Unit IPre
abbrev IRes := ExtensibleIris.IRes WorldPluginV2
abbrev IProp := ExtensibleIris.IProp WorldPluginV2

def registrySlot (N : Namespace) (γ : GhostName) (P : IPre) : IRes :=
  (UCMRA.unit,
    (NamedInvariantRegistryF.singleton N γ P,
      (UCMRA.unit, UCMRA.unit)))

def handleSlot (γ : GhostName) : IRes :=
  (UCMRA.unit,
    (UCMRA.unit, (GhostMap.singleton γ (), UCMRA.unit)))

def ghostSlot (γ : GhostName) : IRes :=
  (UCMRA.unit,
    (UCMRA.unit, (UCMRA.unit, GhostMap.singleton γ ())))

def ownResource (a : IRes) : IProp := UPred.own a
def ownHandle (γ : GhostName) : IProp := ownResource (handleSlot γ)

def fold : IPre -n> IProp := ExtensibleIris.fold WorldPluginV2
def unfold : IProp -n> IPre := ExtensibleIris.unfold WorldPluginV2

theorem fold_unfold (P : IProp) : fold (unfold P) = P :=
  ExtensibleIris.fold_unfold WorldPluginV2 P

theorem unfold_fold (X : IPre) : unfold (fold X) = X :=
  ExtensibleIris.unfold_fold WorldPluginV2 X

theorem same_namespace_distinct_ids_compatible {γ δ : GhostName}
    (hγδ : γ ≠ δ) (N : Namespace) (P Q : IPre) :
    CMRA.valid (CMRA.op (registrySlot N γ P) (registrySlot N δ Q)) := by
  constructor
  · trivial
  · constructor
    · apply NamedInvariantRegistryF.distinct_ids_valid
      intro h
      exact hγδ (congrArg (fun k => k.id.ghost) h)
    · constructor <;> intro name <;> trivial

theorem same_id_conflicts (N : Namespace) (γ : GhostName) (P Q : IPre) :
    ¬ CMRA.valid (CMRA.op (registrySlot N γ P) (registrySlot N γ Q)) := by
  intro h
  exact NamedInvariantRegistryF.same_id_conflict N γ P Q h.2.1

theorem handle_slot_idem (γ : GhostName) :
    CMRA.op (handleSlot γ) (handleSlot γ) = handleSlot γ := by
  congr 3

end WorldIrisV2
end LeanIrisX
