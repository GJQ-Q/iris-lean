import LeanIrisX.Core.Morphism
import LeanIrisX.Core.Later

/-!
Mixed-variance OFE functors, the categorical interface required by the
contractive COFE domain-equation solver.  The first argument is contravariant
and the second covariant, matching Iris' `OFunctor` convention.
-/

namespace LeanIrisX

universe u

abbrev OFunctorPre :=
  (A B : Type u) → [OFE A] → [COFE A] → [OFE B] → [COFE B] → Type u

class OFunctor (F : OFunctorPre) where
  ofe (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] : OFE (F A B)
  cofe (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] : COFE (F A B)
  map {A B A' B' : Type u} [OFE A] [COFE A] [OFE B] [COFE B]
      [OFE A'] [COFE A'] [OFE B'] [COFE B'] :
    (A' -n> A) → (B -n> B') → (F A B -n> F A' B')
  map_ne {A B A' B' : Type u} [OFE A] [COFE A] [OFE B] [COFE B]
      [OFE A'] [COFE A'] [OFE B'] [COFE B'] :
    ∀ (n : Nat) (f₁ f₂ : A' -n> A) (g₁ g₂ : B -n> B'),
      f₁ ≡{n}≡ f₂ → g₁ ≡{n}≡ g₂ →
      ∀ x : F A B, map f₁ g₁ x ≡{n}≡ map f₂ g₂ x
  map_id {A B : Type u} [OFE A] [COFE A] [OFE B] [COFE B] (x : F A B) :
    map (OFEMor.id : A -n> A) (OFEMor.id : B -n> B) x = x
  map_comp {A B A' B' A'' B'' : Type u}
      [OFE A] [COFE A] [OFE B] [COFE B]
      [OFE A'] [COFE A'] [OFE B'] [COFE B']
      [OFE A''] [COFE A''] [OFE B''] [COFE B'']
      (f : A' -n> A) (g : B -n> B')
      (f' : A'' -n> A') (g' : B' -n> B'') (x : F A B) :
    map f' g' (map f g x) = map (OFEMor.comp f f') (OFEMor.comp g' g) x

/-- A mixed-variance OFE functor whose action gains one observation step. -/
class OFunctorContractive (F : OFunctorPre) [OFunctor F] : Prop where
  map_contractive {A B A' B' : Type u}
      [OFE A] [COFE A] [OFE B] [COFE B]
      [OFE A'] [COFE A'] [OFE B'] [COFE B'] :
    ∀ (n : Nat) (f₁ f₂ : A' -n> A) (g₁ g₂ : B -n> B'),
      OFE.DistLater n f₁ f₂ → OFE.DistLater n g₁ g₂ →
      ∀ x : F A B,
        @OFE.dist (F A' B') (OFunctor.ofe (F := F) A' B') n
          (OFunctor.map (F := F) f₁ g₁ x)
          (OFunctor.map (F := F) f₂ g₂ x)

namespace OFunctor

instance instOFE (F : OFunctorPre) [OFunctor F]
    (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] : OFE (F A B) := OFunctor.ofe A B

instance instCOFE (F : OFunctorPre) [OFunctor F]
    (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] : COFE (F A B) := OFunctor.cofe A B

def mapHom (F : OFunctorPre) [OFunctor F]
    {A B A' B' : Type u} [OFE A] [COFE A] [OFE B] [COFE B]
    [OFE A'] [COFE A'] [OFE B'] [COFE B']
    (f : A' -n> A) (g : B -n> B') : F A B -n> F A' B' :=
  OFunctor.map f g

abbrev Const (C : Type u) [OFE C] [COFE C] : OFunctorPre :=
  fun _ _ _ _ _ _ => C

instance constOFunctor (C : Type u) [OFE C] [COFE C] : OFunctor (Const C) where
  ofe _ _ := inferInstanceAs (OFE C)
  cofe _ _ := inferInstanceAs (COFE C)
  map _ _ := OFEMor.id
  map_ne n _ _ _ _ _ _ x := OFE.refl n x
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance constContractive (C : Type u) [OFE C] [COFE C] :
    OFunctorContractive (Const C) where
  map_contractive n _ _ _ _ _ _ x := OFE.refl n x

abbrev Id : OFunctorPre := fun _ B _ _ _ _ => B

instance idOFunctor : OFunctor Id where
  ofe _ B := inferInstanceAs (OFE B)
  cofe _ B := inferInstanceAs (COFE B)
  map _ g := g
  map_ne _ _ _ _ _ _ hg x := hg x
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

abbrev LaterF : OFunctorPre := fun _ B _ _ _ _ => Later B

instance laterOFunctor : OFunctor LaterF where
  ofe _ B := inferInstanceAs (OFE (Later B))
  cofe _ B := inferInstanceAs (COFE (Later B))
  map _ g := {
    toFun := Later.map g
    nonExpansive := Later.map_nonExpansive g g.nonExpansive
  }
  map_ne n _ _ _ _ _ hg x := by
    intro m hm
    exact OFE.mono (Nat.le_of_lt hm) (hg x.prev)
  map_id x := by cases x; rfl
  map_comp f g f' g' x := by cases x; rfl

instance laterContractive : OFunctorContractive LaterF where
  map_contractive n f₁ f₂ g₁ g₂ hf hg x := by
    intro m hm
    exact hg m hm x.prev

end OFunctor
end LeanIrisX
