import LeanIrisX.Logic.NamedInvariantRegistryFunctor
import LeanIrisX.Logic.ExtensibleResource
import LeanIrisX.Algebra.PersistentToken
import LeanIrisX.Algebra.Exclusive

/-!
# Integrated invariant world resource

The resource separates guarded bodies, persistent public handles, exclusive
close permissions, and ordinary client ghost state.
-/

namespace LeanIrisX

namespace Excl

instance totalCoreExcl {α : Type u} : TotalCore (Excl α) where
  core := fun _ => .unit
  core_spec _ := rfl

end Excl

abbrev PersistentHandlePlugin : OFunctorPre :=
  OFunctor.Const (GhostMap PersistentToken)

abbrev CloseTokenPlugin : OFunctorPre :=
  OFunctor.Const (GhostMap (Excl Unit))

abbrev FinalWorldPlugin : OFunctorPre :=
  ProductOF NamedInvariantRegistryF
    (ProductOF PersistentHandlePlugin
      (ProductOF CloseTokenPlugin UnitGhostPlugin))

namespace FinalWorld

private theorem product_op {A : Type u} {B : Type v} [OFE A] [CMRA A]
    [OFE B] [CMRA B] (x y : A × B) :
    CMRA.op x y = (CMRA.op x.1 y.1, CMRA.op x.2 y.2) := rfl

abbrev IPre := ExtensibleIris.IPre FinalWorldPlugin
abbrev IRes := ExtensibleIris.IRes FinalWorldPlugin
abbrev IProp := ExtensibleIris.IProp FinalWorldPlugin

def registrySlot (N : Namespace) (γ : GhostName) (P : IPre) : IRes :=
  (UCMRA.unit,
    (NamedInvariantRegistryF.singleton N γ P,
      (UCMRA.unit, (UCMRA.unit, UCMRA.unit))))

def handleSlot (γ : GhostName) : IRes :=
  (UCMRA.unit,
    (UCMRA.unit,
      (GhostMap.singleton γ PersistentToken.token,
        (UCMRA.unit, UCMRA.unit))))

def closeSlot (γ : GhostName) : IRes :=
  (UCMRA.unit,
    (UCMRA.unit,
      (UCMRA.unit,
        (GhostMap.singleton γ (Excl.own ()), UCMRA.unit))))

def ghostSlot (γ : GhostName) : IRes :=
  (UCMRA.unit,
    (UCMRA.unit,
      (UCMRA.unit, (UCMRA.unit, GhostMap.singleton γ ()))))

def ownResource (a : IRes) : IProp := UPred.own a
def invariantHandle (γ : GhostName) : IProp := ownResource (handleSlot γ)
def closePermission (γ : GhostName) : IProp := ownResource (closeSlot γ)

def fold : IPre -n> IProp := ExtensibleIris.fold FinalWorldPlugin
def unfold : IProp -n> IPre := ExtensibleIris.unfold FinalWorldPlugin

theorem fold_unfold (P : IProp) : fold (unfold P) = P :=
  ExtensibleIris.fold_unfold FinalWorldPlugin P

theorem unfold_fold (X : IPre) : unfold (fold X) = X :=
  ExtensibleIris.unfold_fold FinalWorldPlugin X

/-- A registry body and its public handle form a valid authenticated package. -/
theorem registry_handle_valid (N : Namespace) (γ : GhostName) (P : IPre) :
    CMRA.valid (CMRA.op (registrySlot N γ P) (handleSlot γ)) := by
  constructor
  · trivial
  · constructor
    · intro k
      simp only [product_op]
      change CMRA.valid
        ((CMRA.op (NamedInvariantRegistryF.singleton N γ P) UCMRA.unit) k)
      rw [UCMRA.unit_right]
      by_cases hk : k = InvariantIdentity.key N γ
      · subst k
        simp only [NamedInvariantRegistryF.singleton,
          ResourceMap.singleton_same]
        exact GuardedExcl.own_valid _
      · simp only [NamedInvariantRegistryF.singleton,
          ResourceMap.singleton_other hk]
        exact UCMRA.unit_valid
    · constructor
      · intro δ; trivial
      · constructor <;> intro δ <;> trivial

/-- Public handles are genuinely non-unit and duplicable. -/
theorem handle_idem (γ : GhostName) :
    CMRA.op (handleSlot γ) (handleSlot γ) = handleSlot γ := by
  unfold handleSlot
  simp only [product_op]
  congr 3
  rw [← GhostMap.singleton_op]
  exact congrArg (GhostMap.singleton γ) (PersistentToken.token_idem)

theorem handle_nontrivial (γ : GhostName) :
    handleSlot γ ≠ (UCMRA.unit : IRes) := by
  intro h
  have hmap := congrArg (fun r => r.2.2.1 γ) h
  have hmap' : PersistentToken.token = PersistentToken.unit := by
    simpa [handleSlot, GhostMap.singleton] using hmap
  exact PersistentToken.token_ne_unit hmap'

/-- Close permissions are linear/exclusive. -/
theorem close_conflict (γ : GhostName) :
    ¬ CMRA.valid (CMRA.op (closeSlot γ) (closeSlot γ)) := by
  intro h
  have hm : CMRA.valid
      (CMRA.op (GhostMap.singleton γ (Excl.own ()))
        (GhostMap.singleton γ (Excl.own ()))) := by
    simpa only [product_op, closeSlot] using h.2.2.2.1
  rw [← GhostMap.singleton_op] at hm
  have hγ := hm γ
  have hγ' : CMRA.valid (CMRA.op (Excl.own ()) (Excl.own ())) := by
    simpa only [GhostMap.singleton_same] using hγ
  exact Excl.own_conflict () () hγ'

theorem handle_and_close_compatible (γ : GhostName) :
    CMRA.valid (CMRA.op (handleSlot γ) (closeSlot γ)) := by
  constructor
  · trivial
  · constructor
    · intro k; trivial
    · constructor
      · intro δ; trivial
      · constructor
        · intro δ
          simp only [product_op]
          change CMRA.valid
            ((CMRA.op UCMRA.unit (GhostMap.singleton γ (Excl.own ()))) δ)
          rw [UCMRA.unit_left]
          by_cases hδ : δ = γ
          · subst δ
            simp only [GhostMap.singleton_same]
            exact Excl.own_valid _
          · simp only [GhostMap.singleton_other hδ]
            exact UCMRA.unit_valid
        · intro δ; trivial

/-- Semantic authentication predicate used by world satisfaction: the guarded
body and persistent handle are present under the same internal identity. -/
def AuthenticatedAt (n : Nat) (r : IRes) (N : Namespace)
    (γ : GhostName) (P : IPre) : Prop :=
  r.2.1 (InvariantIdentity.key N γ) ≡{n}≡
      GuardedExcl.own (Later.next P) ∧
  r.2.2.1 γ = PersistentToken.token

theorem package_authenticated (n : Nat) (N : Namespace)
    (γ : GhostName) (P : IPre) :
    AuthenticatedAt n
      (CMRA.op (registrySlot N γ P) (handleSlot γ)) N γ P := by
  simp only [product_op]
  constructor
  · change
      (CMRA.op (NamedInvariantRegistryF.singleton N γ P) UCMRA.unit)
          (InvariantIdentity.key N γ) ≡{n}≡
        GuardedExcl.own (Later.next P)
    rw [UCMRA.unit_right]
    rw [NamedInvariantRegistryF.singleton_same]
    exact OFE.refl n
      (GuardedExcl.own (Later.next P) : GuardedExcl IPre)
  · change (CMRA.op UCMRA.unit
      (GhostMap.singleton γ PersistentToken.token)) γ = PersistentToken.token
    rw [UCMRA.unit_left]
    simp [AuthenticatedAt, registrySlot, handleSlot, GhostMap.singleton]

end FinalWorld
end LeanIrisX
