import LeanIrisX.Core.COFE

/-! Pointwise OFE and COFE structures on function spaces. -/

namespace LeanIrisX

instance functionOFE {α : Type u} {β : Type v} [OFE β] : OFE (α → β) where
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
      apply funext
      intro x
      exact OFE.eq_of_dist (fun n => h n x)
  dist_mono hnm h x := OFE.mono hnm (h x)

def OFEChain.eval {α : Type u} {β : Type v} [OFE β]
    (c : OFEChain (α → β)) (x : α) : OFEChain β where
  approx n := c n x
  coherent := by intro n m hnm; exact c.coherent hnm x

instance functionCOFE {α : Type u} {β : Type v} [OFE β] [COFE β] :
    COFE (α → β) where
  limit c x := COFE.lim (c.eval x)
  limit_spec := by intro c n x; exact COFE.lim_dist (c.eval x) n

theorem function_dist_apply {α : Type u} {β : Type v} [OFE β]
    {n : Nat} {f g : α → β} (h : f ≡{n}≡ g) (x : α) :
    f x ≡{n}≡ g x := h x

end LeanIrisX

