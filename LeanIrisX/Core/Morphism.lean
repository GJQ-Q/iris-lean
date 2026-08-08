import LeanIrisX.Core.Function

/-! Bundled non-expansive maps between OFEs. -/

namespace LeanIrisX

structure OFEMor (α : Type u) (β : Type v) [OFE α] [OFE β] where
  toFun : α → β
  nonExpansive : NonExpansive toFun

infixr:25 " -n> " => OFEMor

instance {α : Type u} {β : Type v} [OFE α] [OFE β] :
    CoeFun (α -n> β) (fun _ => α → β) := ⟨OFEMor.toFun⟩

namespace OFEMor

variable {α : Type u} {β : Type v} {γ : Type w}
variable [OFE α] [OFE β] [OFE γ]

def id : α -n> α where
  toFun x := x
  nonExpansive := NonExpansive.id

def const (b : β) : α -n> β where
  toFun _ := b
  nonExpansive := NonExpansive.const b

def comp (g : β -n> γ) (f : α -n> β) : α -n> γ where
  toFun x := g (f x)
  nonExpansive := NonExpansive.comp g.nonExpansive f.nonExpansive

@[simp] theorem id_apply (x : α) : id x = x := rfl
@[simp] theorem const_apply (b : β) (x : α) : const b x = b := rfl
@[simp] theorem comp_apply (g : β -n> γ) (f : α -n> β) (x : α) :
    comp g f x = g (f x) := rfl

end OFEMor

/-- An isomorphism in the category of OFEs: both directions are
non-expansive, and the two composites are propositionally the identity. -/
structure OFEIso (α : Type u) (β : Type v) [OFE α] [OFE β] where
  hom : α -n> β
  inv : β -n> α
  hom_inv : ∀ y, hom (inv y) = y
  inv_hom : ∀ x, inv (hom x) = x

instance ofeMorOFE {α : Type u} {β : Type v} [OFE α] [OFE β] :
    OFE (α -n> β) where
  dist n f g := ∀ x, f x ≡{n}≡ g x
  dist_equivalence n := by
    constructor
    · intro f x; exact OFE.refl n _
    · intro f g h x; exact OFE.symm (h x)
    · intro f g h hfg hgh x; exact OFE.trans (hfg x) (hgh x)
  eq_dist f g := by
    constructor
    · intro h n x; subst g; exact OFE.refl n _
    · intro h
      cases f with
      | mk ff hf =>
        cases g with
        | mk gg hg =>
          simp only [OFEMor.mk.injEq]
          apply funext
          intro x
          exact OFE.eq_of_dist (fun n => h n x)
  dist_mono hnm h x := OFE.mono hnm (h x)

def OFEChain.evalMor {α : Type u} {β : Type v} [OFE α] [OFE β]
    (c : OFEChain (α -n> β)) (x : α) : OFEChain β where
  approx n := c n x
  coherent := by intro n m hnm; exact c.coherent hnm x

instance ofeMorCOFE {α : Type u} {β : Type v}
    [OFE α] [OFE β] [COFE β] : COFE (α -n> β) where
  limit c := {
    toFun := fun x => COFE.lim (c.evalMor x)
    nonExpansive := by
      intro n x y hxy
      exact OFE.trans
        (COFE.lim_dist (c.evalMor x) n)
        (OFE.trans ((c n).nonExpansive n hxy)
          (OFE.symm (COFE.lim_dist (c.evalMor y) n)))
  }
  limit_spec := by intro c n x; exact COFE.lim_dist (c.evalMor x) n

end LeanIrisX
