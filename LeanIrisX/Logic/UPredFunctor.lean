import LeanIrisX.Logic.UPred
import LeanIrisX.Core.OFunctor
import LeanIrisX.Algebra.CMRAMorphism

/-!
Lifting a mixed-variance unital resource functor through `UPred`.

This is the semantic bridge required by the Iris recursive proposition model:
resource maps preserve validity and composition, while predicate reindexing is
contravariant in the resource map.
-/

namespace LeanIrisX

universe u

class UCMRAFunctor (F : OFunctorPre) [OFunctor F] where
  cmra (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] :
    @CMRA (F A B) (OFunctor.ofe A B)
  ucmra (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] :
    @UCMRA (F A B) (OFunctor.ofe A B) (cmra A B)
  map_validN {A B A' B' : Type u}
      [OFE A] [COFE A] [OFE B] [COFE B]
      [OFE A'] [COFE A'] [OFE B'] [COFE B']
      (f : A' -n> A) (g : B -n> B') {n : Nat} {x : F A B} :
    @CMRA.validN (F A B) (OFunctor.ofe A B) (cmra A B) n x →
      @CMRA.validN (F A' B') (OFunctor.ofe A' B') (cmra A' B') n
        (OFunctor.map f g x)
  map_op {A B A' B' : Type u}
      [OFE A] [COFE A] [OFE B] [COFE B]
      [OFE A'] [COFE A'] [OFE B'] [COFE B']
      (f : A' -n> A) (g : B -n> B') (x y : F A B) :
    OFunctor.map f g (@CMRA.op (F A B) (OFunctor.ofe A B) (cmra A B) x y) =
      @CMRA.op (F A' B') (OFunctor.ofe A' B') (cmra A' B')
        (OFunctor.map f g x) (OFunctor.map f g y)

namespace UCMRAFunctor

instance instCMRA (F : OFunctorPre) [OFunctor F] [UCMRAFunctor F]
    (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] : CMRA (F A B) :=
  UCMRAFunctor.cmra A B

instance instUCMRA (F : OFunctorPre) [OFunctor F] [UCMRAFunctor F]
    (A B : Type u) [OFE A] [COFE A] [OFE B] [COFE B] : UCMRA (F A B) :=
  UCMRAFunctor.ucmra A B

def mapCMRA (F : OFunctorPre) [OFunctor F] [UCMRAFunctor F]
    {A B A' B' : Type u}
    [OFE A] [COFE A] [OFE B] [COFE B]
    [OFE A'] [COFE A'] [OFE B'] [COFE B']
    (f : A' -n> A) (g : B -n> B') : F A B -c> F A' B' where
  toFun := OFunctor.map f g
  nonExpansive := (OFunctor.map f g).nonExpansive
  validN_map := UCMRAFunctor.map_validN f g
  op_map := UCMRAFunctor.map_op f g

instance constFunctor (C : Type u) [OFE C] [COFE C] [CMRA C] [UCMRA C] :
    UCMRAFunctor (OFunctor.Const C) where
  cmra _ _ := inferInstanceAs (CMRA C)
  ucmra _ _ := inferInstanceAs (UCMRA C)
  map_validN := by
    intro A B A' B' _ _ _ _ _ _ _ _ f g n x h
    exact h
  map_op := by
    intro A B A' B' _ _ _ _ _ _ _ _ f g x y
    rfl

end UCMRAFunctor

namespace UPred

variable {α : Type u} {β : Type u}
variable [OFE α] [CMRA α] [UCMRA α] [OFE β] [CMRA β] [UCMRA β]

theorem holds_ne (P : UPred α) {n : Nat} {x y : α}
    (hxy : x ≡{n}≡ y) (hx : CMRA.validN n x) (hy : CMRA.validN n y) :
    P.holdsAt n x hx ↔ P.holdsAt n y hy := by
  constructor
  · intro hp
    apply P.mono hp
    · exact ⟨UCMRA.unit, OFE.trans (OFE.symm hxy)
        (OFE.of_eq (UCMRA.unit_right x).symm)⟩
    · exact Nat.le_refl n
  · intro hp
    apply P.mono hp
    · exact ⟨UCMRA.unit, OFE.trans hxy
        (OFE.of_eq (UCMRA.unit_right y).symm)⟩
    · exact Nat.le_refl n

def map (f : β -c> α) : UPred α -n> UPred β where
  toFun P := {
    holds := fun n x => P.holdsAt n (f x.val) (f.validN_map x.property)
    mono := by
      intro n₁ n₂ x₁ x₂ hp hinc hle
      exact P.mono hp (f.includedN_map hinc) hle
  }
  nonExpansive := by
    intro n P Q hPQ m x hx hmn
    exact hPQ m (f x) (f.validN_map hx) hmn

@[simp] theorem map_id (P : UPred α) : map (CMRAHom.id : α -c> α) P = P := by
  apply UPred.ext
  intro n x hx
  exact Iff.rfl

theorem map_comp (g : β -c> α) {γ : Type u} [OFE γ] [CMRA γ] [UCMRA γ]
    (f : γ -c> β) (P : UPred α) : map f (map g P) = map (CMRAHom.comp g f) P := by
  apply UPred.ext
  intro n x hx
  exact Iff.rfl

end UPred

abbrev UPredOF (F : OFunctorPre) [OFunctor F] [UCMRAFunctor F] : OFunctorPre :=
  fun A B _ _ _ _ => UPred (F B A)

namespace UPredOF

instance instOFunctor (F : OFunctorPre) [OFunctor F] [UCMRAFunctor F] :
    OFunctor (UPredOF F) where
  ofe A B := inferInstanceAs (OFE (UPred (F B A)))
  cofe A B := inferInstanceAs (COFE (UPred (F B A)))
  map f g := UPred.map (UCMRAFunctor.mapCMRA F g f)
  map_ne n f₁ f₂ g₁ g₂ hf hg P := by
    intro m x hx hmn
    apply UPred.holds_ne P
    · exact OFE.mono hmn (OFunctor.map_ne n g₁ g₂ f₁ f₂ hg hf x)
  map_id P := by
    apply UPred.ext
    intro n x hx
    apply UPred.holds_ne P
    · exact OFE.of_eq (OFunctor.map_id x)
  map_comp f g f' g' P := by
    apply UPred.ext
    intro n x hx
    apply UPred.holds_ne P
    · exact OFE.of_eq (OFunctor.map_comp g' f' g f x)

instance instContractive (F : OFunctorPre) [OFunctor F] [UCMRAFunctor F]
    [OFunctorContractive F] : OFunctorContractive (UPredOF F) where
  map_contractive n f₁ f₂ g₁ g₂ hf hg P := by
    intro m x hx hmn
    apply UPred.holds_ne P
    · exact OFE.mono hmn
        (OFunctorContractive.map_contractive n g₁ g₂ f₁ f₂ hg hf x)

end UPredOF
end LeanIrisX
