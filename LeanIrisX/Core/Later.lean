import LeanIrisX.Core.COFE

/-! The standard one-step-later OFE/COFE construction. -/

namespace LeanIrisX

structure Later (α : Type u) where
  prev : α
deriving Repr

namespace Later

variable {α : Type u} {β : Type v}

instance [OFE α] : OFE (Later α) where
  dist n x y := OFE.DistLater n x.prev y.prev
  dist_equivalence n := by
    constructor
    · intro x; exact OFE.distLater_refl n x.prev
    · intro x y h; exact OFE.distLater_symm h
    · intro x y z hxy hyz; exact OFE.distLater_trans hxy hyz
  eq_dist x y := by
    constructor
    · intro h n; subst y; exact OFE.distLater_refl n x.prev
    · intro h
      cases x with
      | mk x =>
        cases y with
        | mk y =>
          congr
          apply OFE.eq_of_dist
          intro n
          exact h (n + 1) n (Nat.lt_succ_self n)
  dist_mono hnm h k hk := h k (Nat.lt_of_lt_of_le hk hnm)

/-- Introduce one observation delay. -/
def next (x : α) : Later α := ⟨x⟩

/-- `next` gains one observation step and is therefore contractive. -/
theorem next_contractive [OFE α] : Contractive (next : α → Later α) := by
  intro n x y hxy
  exact hxy

def map (f : α → β) (x : Later α) : Later β := ⟨f x.prev⟩

theorem map_nonExpansive [OFE α] [OFE β] (f : α → β) (hf : NonExpansive f) :
    NonExpansive (map f) := by
  intro n x y hxy m hm
  exact hf m (hxy m hm)

def shiftedChain [OFE α] (c : OFEChain (Later α)) : OFEChain α where
  approx n := (c (n + 1)).prev
  coherent := by
    intro n m hnm
    have hc := c.coherent (Nat.succ_le_succ hnm)
    exact hc n (Nat.lt_succ_self n)

instance [OFE α] [COFE α] : COFE (Later α) where
  limit c := ⟨COFE.lim (shiftedChain c)⟩
  limit_spec := by
    intro c n m hmn
    have hlim : COFE.lim (shiftedChain c) ≡{m}≡ (c (m + 1)).prev :=
      COFE.lim_dist (shiftedChain c) m
    have hchain : (c (m + 1)).prev ≡{m}≡ (c n).prev := by
      have hsucc : m + 1 ≤ n := hmn
      have hc := c.coherent hsucc
      exact hc m (Nat.lt_succ_self m)
    exact OFE.trans hlim hchain

theorem dist_zero [OFE α] (x y : Later α) : x ≡{0}≡ y :=
  OFE.distLater_zero x.prev y.prev

theorem dist_succ_iff [OFE α] {n : Nat} {x y : Later α} :
    x ≡{n + 1}≡ y ↔ x.prev ≡{n}≡ y.prev :=
  OFE.distLater_succ_iff

end Later
end LeanIrisX
