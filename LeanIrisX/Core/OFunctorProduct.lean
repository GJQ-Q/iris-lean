import LeanIrisX.Logic.UPredFunctor
import LeanIrisX.Algebra.Product

/-! Products of resource functors provide the basic extensibility mechanism. -/

namespace LeanIrisX

universe u

abbrev ProductOF (F G : OFunctorPre) : OFunctorPre :=
  fun A B _ _ _ _ => F A B × G A B

namespace ProductOF

instance instOFunctor (F G : OFunctorPre) [OFunctor F] [OFunctor G] :
    OFunctor (ProductOF F G) where
  ofe A B := inferInstanceAs (OFE (F A B × G A B))
  cofe A B := inferInstanceAs (COFE (F A B × G A B))
  map f g := {
    toFun := fun x => (OFunctor.map f g x.1, OFunctor.map f g x.2)
    nonExpansive := by
      intro n x y h
      exact ⟨(OFunctor.map f g).nonExpansive n h.1,
        (OFunctor.map f g).nonExpansive n h.2⟩
  }
  map_ne n f₁ f₂ g₁ g₂ hf hg x :=
    ⟨OFunctor.map_ne n f₁ f₂ g₁ g₂ hf hg x.1,
      OFunctor.map_ne n f₁ f₂ g₁ g₂ hf hg x.2⟩
  map_id x := by
    apply Prod.ext
    · exact OFunctor.map_id x.1
    · exact OFunctor.map_id x.2
  map_comp f g f' g' x := by
    apply Prod.ext
    · exact OFunctor.map_comp f g f' g' x.1
    · exact OFunctor.map_comp f g f' g' x.2

instance instContractive (F G : OFunctorPre) [OFunctor F] [OFunctor G]
    [OFunctorContractive F] [OFunctorContractive G] :
    OFunctorContractive (ProductOF F G) where
  map_contractive n f₁ f₂ g₁ g₂ hf hg x :=
    ⟨OFunctorContractive.map_contractive n f₁ f₂ g₁ g₂ hf hg x.1,
      OFunctorContractive.map_contractive n f₁ f₂ g₁ g₂ hf hg x.2⟩

instance instUCMRAFunctor (F G : OFunctorPre)
    [OFunctor F] [OFunctor G] [UCMRAFunctor F] [UCMRAFunctor G] :
    UCMRAFunctor (ProductOF F G) where
  cmra A B := inferInstanceAs (CMRA (F A B × G A B))
  ucmra A B := inferInstanceAs (UCMRA (F A B × G A B))
  map_validN f g := by
    intro n x h
    exact ⟨UCMRAFunctor.map_validN f g h.1,
      UCMRAFunctor.map_validN f g h.2⟩
  map_op f g x y := by
    apply Prod.ext
    · exact UCMRAFunctor.map_op f g x.1 y.1
    · exact UCMRAFunctor.map_op f g x.2 y.2

end ProductOF
end LeanIrisX
