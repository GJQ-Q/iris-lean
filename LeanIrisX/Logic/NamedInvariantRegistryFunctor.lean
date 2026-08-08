import LeanIrisX.Logic.InvariantRegistryFunctor
import LeanIrisX.Algebra.InvariantIdentity

/-! Recursive invariant registry keyed by namespace plus a fresh identity. -/

namespace LeanIrisX

abbrev NamedInvariantRegistryF : OFunctorPre :=
  fun _ B _ _ _ _ => ResourceMap InvariantKey (GuardedExcl B)

namespace NamedInvariantRegistryF

instance instOFunctor : OFunctor NamedInvariantRegistryF where
  ofe _ B := inferInstanceAs
    (OFE (ResourceMap InvariantKey (GuardedExcl B)))
  cofe _ B := inferInstanceAs
    (COFE (ResourceMap InvariantKey (GuardedExcl B)))
  map _ g := {
    toFun := fun r k => GuardedExcl.map g (r k)
    nonExpansive := by
      intro n x y h k
      exact GuardedExcl.map_nonExpansive g g.nonExpansive n (h k)
  }
  map_ne n f₁ f₂ g₁ g₂ hf hg r k := by
    change GuardedExcl.Dist n
      (GuardedExcl.map g₁ (r k)) (GuardedExcl.map g₂ (r k))
    cases h : r k with
    | unit => simp [GuardedExcl.map, GuardedExcl.Dist]
    | invalid => simp [GuardedExcl.map, GuardedExcl.Dist]
    | own x =>
      change Later.map g₁ x ≡{n}≡ Later.map g₂ x
      intro m hm
      exact OFE.mono (Nat.le_of_lt hm) (hg x.prev)
  map_id r := by
    funext k
    exact GuardedExcl.map_id (r k)
  map_comp f g f' g' r := by
    funext k
    change GuardedExcl.map g' (GuardedExcl.map g (r k)) =
      GuardedExcl.map (g' ∘ g) (r k)
    exact GuardedExcl.map_comp g g' (r k)

instance instContractive : OFunctorContractive NamedInvariantRegistryF where
  map_contractive n f₁ f₂ g₁ g₂ hf hg r k := by
    change GuardedExcl.Dist n
      (GuardedExcl.map g₁ (r k)) (GuardedExcl.map g₂ (r k))
    cases h : r k with
    | unit => simp [GuardedExcl.map, GuardedExcl.Dist]
    | invalid => simp [GuardedExcl.map, GuardedExcl.Dist]
    | own x =>
      change Later.map g₁ x ≡{n}≡ Later.map g₂ x
      intro m hm
      exact hg m hm x.prev

instance instUCMRAFunctor : UCMRAFunctor NamedInvariantRegistryF where
  cmra _ B := inferInstanceAs
    (CMRA (ResourceMap InvariantKey (GuardedExcl B)))
  ucmra _ B := inferInstanceAs
    (UCMRA (ResourceMap InvariantKey (GuardedExcl B)))
  map_validN _ g := by
    intro n r h k
    exact GuardedExcl.map_validN g (h k)
  map_op _ g x y := by
    funext k
    exact GuardedExcl.map_op g (x k) (y k)

def singleton {B : Type} [OFE B] [COFE B]
    (N : Namespace) (γ : GhostName) (P : B) :
    NamedInvariantRegistryF Unit B :=
  ResourceMap.singleton (InvariantIdentity.key N γ)
    (GuardedExcl.own (Later.next P))

@[simp] theorem singleton_same {B : Type} [OFE B] [COFE B]
    (N : Namespace) (γ : GhostName) (P : B) :
    singleton N γ P (InvariantIdentity.key N γ) =
      GuardedExcl.own (Later.next P) := by
  simp [singleton]

theorem distinct_ids_valid {B : Type} [OFE B] [COFE B]
    {N K : Namespace} {γ δ : GhostName} (hkey :
      InvariantIdentity.key N γ ≠ InvariantIdentity.key K δ)
    (P Q : B) :
    CMRA.valid (CMRA.op (singleton N γ P) (singleton K δ Q)) := by
  intro key
  change GuardedExcl.valid (GuardedExcl.op
    (singleton N γ P key) (singleton K δ Q key))
  by_cases h₁ : key = InvariantIdentity.key N γ
  · subst key
    simp [singleton, hkey, GuardedExcl.valid, GuardedExcl.op]
  · by_cases h₂ : key = InvariantIdentity.key K δ
    · subst key
      have hrev : InvariantIdentity.key K δ ≠ InvariantIdentity.key N γ :=
        Ne.symm hkey
      simp [singleton, hrev, GuardedExcl.valid, GuardedExcl.op]
    · simp [singleton, h₁, h₂, GuardedExcl.valid, GuardedExcl.op]

theorem same_id_conflict {B : Type} [OFE B] [COFE B]
    (N : Namespace) (γ : GhostName) (P Q : B) :
    ¬ CMRA.valid (CMRA.op (singleton N γ P) (singleton N γ Q)) := by
  intro h
  have hk := h (InvariantIdentity.key N γ)
  change GuardedExcl.valid (GuardedExcl.op
    (singleton N γ P (InvariantIdentity.key N γ))
    (singleton N γ Q (InvariantIdentity.key N γ))) at hk
  rw [singleton_same, singleton_same] at hk
  exact hk

end NamedInvariantRegistryF
end LeanIrisX
