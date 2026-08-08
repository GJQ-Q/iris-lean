import LeanIrisX.Logic.GuardedResourceFunctor
import LeanIrisX.Algebra.ResourceMap
import LeanIrisX.Logic.Mask

/-! A namespace-indexed, guarded and exclusive invariant registry functor. -/

namespace LeanIrisX

abbrev InvariantRegistryF : OFunctorPre :=
  fun _ B _ _ _ _ => ResourceMap Namespace (GuardedExcl B)

namespace InvariantRegistryF

instance instOFunctor : OFunctor InvariantRegistryF where
  ofe _ B := inferInstanceAs (OFE (ResourceMap Namespace (GuardedExcl B)))
  cofe _ B := inferInstanceAs (COFE (ResourceMap Namespace (GuardedExcl B)))
  map _ g := {
    toFun := fun r N => GuardedExcl.map g (r N)
    nonExpansive := by
      intro n x y h N
      exact GuardedExcl.map_nonExpansive g g.nonExpansive n (h N)
  }
  map_ne n f₁ f₂ g₁ g₂ hf hg r N := by
    change GuardedExcl.map g₁ (r N) ≡{n}≡ GuardedExcl.map g₂ (r N)
    cases h : r N with
    | unit => simpa [h, GuardedExcl.map] using
        (OFE.refl n (GuardedExcl.unit : GuardedExcl _))
    | invalid => simpa [h, GuardedExcl.map] using
        (OFE.refl n (GuardedExcl.invalid : GuardedExcl _))
    | own x =>
      change Later.map g₁ x ≡{n}≡ Later.map g₂ x
      intro m hm
      exact OFE.mono (Nat.le_of_lt hm) (hg x.prev)
  map_id r := by
    funext N
    exact GuardedExcl.map_id (r N)
  map_comp f g f' g' r := by
    funext N
    change GuardedExcl.map g' (GuardedExcl.map g (r N)) =
      GuardedExcl.map (g' ∘ g) (r N)
    exact GuardedExcl.map_comp g g' (r N)

instance instContractive : OFunctorContractive InvariantRegistryF where
  map_contractive n f₁ f₂ g₁ g₂ hf hg r N := by
    change GuardedExcl.map g₁ (r N) ≡{n}≡ GuardedExcl.map g₂ (r N)
    cases h : r N with
    | unit => simpa [h, GuardedExcl.map] using
        (OFE.refl n (GuardedExcl.unit : GuardedExcl _))
    | invalid => simpa [h, GuardedExcl.map] using
        (OFE.refl n (GuardedExcl.invalid : GuardedExcl _))
    | own x =>
      change Later.map g₁ x ≡{n}≡ Later.map g₂ x
      intro m hm
      exact hg m hm x.prev

instance instUCMRAFunctor : UCMRAFunctor InvariantRegistryF where
  cmra _ B := inferInstanceAs
    (CMRA (ResourceMap Namespace (GuardedExcl B)))
  ucmra _ B := inferInstanceAs
    (UCMRA (ResourceMap Namespace (GuardedExcl B)))
  map_validN _ g := by
    intro n r h N
    exact GuardedExcl.map_validN g (h N)
  map_op _ g x y := by
    funext N
    exact GuardedExcl.map_op g (x N) (y N)

def singleton {B : Type} [OFE B] [COFE B]
    (N : Namespace) (P : B) : InvariantRegistryF Unit B :=
  ResourceMap.singleton N (GuardedExcl.own (Later.next P))

theorem singleton_same {B : Type} [OFE B] [COFE B]
    (N : Namespace) (P : B) :
    singleton N P N = GuardedExcl.own (Later.next P) := by
  simp [singleton]

theorem distinct_singletons_valid {B : Type} [OFE B] [COFE B]
    {N K : Namespace} (hNK : N ≠ K) (P Q : B) :
    CMRA.valid (CMRA.op (singleton N P) (singleton K Q)) := by
  change ∀ J, GuardedExcl.valid
    (GuardedExcl.op (singleton N P J) (singleton K Q J))
  intro J
  by_cases hJN : J = N
  · subst J
    simp [singleton, hNK, GuardedExcl.valid, GuardedExcl.op]
  · by_cases hJK : J = K
    · subst J
      have hKN : K ≠ N := Ne.symm hNK
      simp [singleton, hKN,
        GuardedExcl.valid, GuardedExcl.op]
    · simp [singleton, hJN, hJK,
        GuardedExcl.valid, GuardedExcl.op]

end InvariantRegistryF
end LeanIrisX
