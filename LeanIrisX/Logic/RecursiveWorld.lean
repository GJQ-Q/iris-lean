import LeanIrisX.Logic.InvariantRegistryFunctor
import LeanIrisX.Logic.ExtensibleResource
import LeanIrisX.Logic.WorldSatisfaction

namespace LeanIrisX

abbrev WorldPlugin : OFunctorPre :=
  ProductOF InvariantRegistryF UnitGhostPlugin

namespace WorldIris

abbrev IPre := ExtensibleIris.IPre WorldPlugin
abbrev Registry := InvariantRegistryF Unit IPre
abbrev IRes := ExtensibleIris.IRes WorldPlugin
abbrev IProp := ExtensibleIris.IProp WorldPlugin

def coreSlot (X : IPre) : IRes :=
  (GuardedExcl.own (Later.next X), (UCMRA.unit, UCMRA.unit))

def invariantSlot (N : Namespace) (P : IPre) : IRes :=
  (UCMRA.unit, (InvariantRegistryF.singleton N P, UCMRA.unit))

def ghostSlot (γ : GhostName) : IRes :=
  (UCMRA.unit, (UCMRA.unit, GhostMap.singleton γ ()))

def ownResource (a : IRes) : IProp := UPred.own a
def ownInvariant (N : Namespace) (P : IPre) : IProp :=
  ownResource (invariantSlot N P)

def fold : IPre -n> IProp := ExtensibleIris.fold WorldPlugin
def unfold : IProp -n> IPre := ExtensibleIris.unfold WorldPlugin

theorem fold_unfold (P : IProp) : fold (unfold P) = P :=
  ExtensibleIris.fold_unfold WorldPlugin P

theorem unfold_fold (X : IPre) : unfold (fold X) = X :=
  ExtensibleIris.unfold_fold WorldPlugin X

structure World where
  resource : IRes
  registered : Mask
  closed : Mask
  opened : Mask

def WSatAt (n : Nat) (w : World) : Prop :=
  CMRA.validN n w.resource ∧
    WorldSatisfaction.Partition w.registered w.closed w.opened

def openName (w : World) (N : Namespace) : World :=
  { w with closed := Mask.erase w.closed N
           opened := Mask.insert w.opened N }

def closeName (w : World) (N : Namespace) : World :=
  { w with closed := Mask.insert w.closed N
           opened := Mask.erase w.opened N }

theorem open_preserves_validN {n : Nat} {w : World} {N : Namespace}
    (h : WSatAt n w) : CMRA.validN n (openName w N).resource := h.1

theorem close_preserves_validN {n : Nat} {w : World} {N : Namespace}
    (h : WSatAt n w) : CMRA.validN n (closeName w N).resource := h.1

theorem distinct_invariants_compatible {N K : Namespace} (hNK : N ≠ K)
    (P Q : IPre) :
    CMRA.valid (CMRA.op (invariantSlot N P) (invariantSlot K Q)) := by
  constructor
  · trivial
  · constructor
    · exact InvariantRegistryF.distinct_singletons_valid hNK P Q
    · intro γ; trivial

theorem same_invariant_conflicts (N : Namespace) (P Q : IPre) :
    ¬ CMRA.valid (CMRA.op (invariantSlot N P) (invariantSlot N Q)) := by
  intro h
  have hN := h.2.1 N
  change CMRA.valid
    ((CMRA.op (InvariantRegistryF.singleton N P)
      (InvariantRegistryF.singleton N Q)) N) at hN
  change GuardedExcl.valid (GuardedExcl.op
    (InvariantRegistryF.singleton N P N)
    (InvariantRegistryF.singleton N Q N)) at hN
  rw [show InvariantRegistryF.singleton N P N =
      GuardedExcl.own (Later.next P) from InvariantRegistryF.singleton_same N P,
    show InvariantRegistryF.singleton N Q N =
      GuardedExcl.own (Later.next Q) from InvariantRegistryF.singleton_same N Q]
    at hN
  exact hN

end WorldIris
end LeanIrisX
