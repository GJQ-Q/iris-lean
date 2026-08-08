import LeanIrisX.Core.Morphism

/-!
Guarded fixed points of contractive endomaps on complete OFEs.

The approximation chain starts at `f seed`, not `seed`: a standard OFE does
not require arbitrary values to be distance-0 equivalent, while contractiveness
does guarantee that any two outputs of `f` are distance-0 equivalent.
-/

namespace LeanIrisX

namespace GuardedFix

variable {α : Type u}

def iterate (f : α → α) (seed : α) : Nat → α
  | 0 => seed
  | n + 1 => f (iterate f seed n)

@[simp] theorem iterate_zero (f : α → α) (seed : α) :
    iterate f seed 0 = seed := rfl

@[simp] theorem iterate_succ (f : α → α) (seed : α) (n : Nat) :
    iterate f seed (n + 1) = f (iterate f seed n) := rfl

/-- Consecutive image iterates agree at the observation depth of the earlier
chain element. -/
theorem image_iterate_dist_succ [OFE α]
    (f : α → α) (hf : Contractive f) (seed : α) :
    ∀ n, iterate f seed (n + 1) ≡{n}≡ iterate f seed (n + 2) := by
  intro n
  induction n with
  | zero =>
      exact hf 0 (OFE.distLater_zero _ _)
  | succ n ih =>
      exact Contractive.succ hf ih

theorem image_iterate_coherent [OFE α]
    (f : α → α) (hf : Contractive f) (seed : α) :
    ∀ ⦃n m : Nat⦄, n ≤ m →
      iterate f seed (n + 1) ≡{n}≡ iterate f seed (m + 1) := by
  intro n m hnm
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact OFE.refl 0 _
  | succ m ih =>
      by_cases heq : n = m + 1
      · subst n
        exact OFE.refl (m + 1) _
      · have hlt : n < m + 1 := Nat.lt_of_le_of_ne hnm heq
        have hnle : n ≤ m := Nat.lt_succ_iff.mp hlt
        exact OFE.trans (ih hnle)
          (OFE.mono hnle (image_iterate_dist_succ f hf seed m))

def chain [OFE α] (f : α → α) (hf : Contractive f) (seed : α) : OFEChain α where
  approx n := iterate f seed (n + 1)
  coherent := image_iterate_coherent f hf seed

def fix [OFE α] [COFE α] (f : α → α) (hf : Contractive f) [Inhabited α] : α :=
  COFE.lim (chain f hf default)

/-- The COFE limit is a genuine Lean fixed point, using OFE soundness
`x = y ↔ ∀ n, x ≡{n}≡ y`. -/
theorem fix_eq [OFE α] [COFE α]
    (f : α → α) (hf : Contractive f) [Inhabited α] :
    f (fix f hf) = fix f hf := by
  apply OFE.eq_of_dist
  intro n
  let c := chain f hf default
  have hInput : OFE.DistLater n (COFE.lim c) (c n) :=
    OFE.dist_to_distLater (COFE.lim_dist c n)
  have hOutput : f (COFE.lim c) ≡{n}≡ f (c n) := hf n hInput
  have hChain : c n ≡{n}≡ c (n + 1) := c.coherent (Nat.le_succ n)
  have hLimitNext : COFE.lim c ≡{n}≡ c (n + 1) :=
    OFE.trans (COFE.lim_dist c n) hChain
  exact OFE.trans hOutput (OFE.symm hLimitNext)

/-- Contractive fixed points are unique. -/
theorem fix_unique [OFE α] [COFE α]
    (f : α → α) (hf : Contractive f) [Inhabited α]
    (x : α) (hx : f x = x) : x = fix f hf := by
  apply OFE.eq_of_dist
  intro n
  induction n with
  | zero =>
      exact OFE.trans (OFE.of_eq hx.symm)
        (OFE.trans (hf 0 (OFE.distLater_zero _ _)) (OFE.of_eq (fix_eq f hf)))
  | succ n ih =>
      exact OFE.trans (OFE.of_eq hx.symm)
        (OFE.trans (Contractive.succ hf ih) (OFE.of_eq (fix_eq f hf)))

end GuardedFix

end LeanIrisX
