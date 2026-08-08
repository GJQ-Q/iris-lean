import LeanIrisX.Core.OFE

/-!
Copyright (c) 2026 LeanIrisX contributors.
Released under Apache 2.0.

Cauchy chains and completeness for OFEs.
-/

namespace LeanIrisX

structure OFEChain (α : Type u) [OFE α] where
  approx : Nat → α
  coherent : ∀ ⦃n m : Nat⦄, n ≤ m → (approx n ≡{n}≡ approx m)

instance {α : Type u} [OFE α] : CoeFun (OFEChain α) (fun _ => Nat → α) :=
  ⟨OFEChain.approx⟩

/-- Completeness is a property of an already chosen OFE instance. -/
class COFE (α : Type u) [OFE α] where
  limit : OFEChain α → α
  limit_spec : ∀ (c : OFEChain α) n, limit c ≡{n}≡ c n

namespace COFE

variable {α : Type u} [OFE α] [COFE α]

def lim (c : OFEChain α) : α := COFE.limit c

theorem lim_dist (c : OFEChain α) (n : Nat) : lim c ≡{n}≡ c n :=
  COFE.limit_spec c n

theorem lim_unique (c : OFEChain α) {x : α}
    (hx : ∀ n, x ≡{n}≡ c n) : x = lim c := by
  apply OFE.eq_of_dist
  intro n
  exact OFE.trans (hx n) (OFE.symm (lim_dist c n))

end COFE

/-- Every discrete OFE is complete. -/
instance discreteCOFE (α : Type u) [OFE α] [OFE.Discrete α] : COFE α where
  limit c := c 0
  limit_spec := by
    intro c n
    exact OFE.of_eq (OFE.Discrete.eq_of_dist (c.coherent (Nat.zero_le n)))

def OFEChain.fst {α : Type u} {β : Type v} [OFE α] [OFE β]
    (c : OFEChain (α × β)) : OFEChain α where
  approx n := (c n).1
  coherent := by intro n m hnm; exact (c.coherent hnm).1

def OFEChain.snd {α : Type u} {β : Type v} [OFE α] [OFE β]
    (c : OFEChain (α × β)) : OFEChain β where
  approx n := (c n).2
  coherent := by intro n m hnm; exact (c.coherent hnm).2

instance prodCOFE {α : Type u} {β : Type v}
    [OFE α] [OFE β] [COFE α] [COFE β] : COFE (α × β) where
  limit c := (COFE.lim c.fst, COFE.lim c.snd)
  limit_spec := by
    intro c n
    exact ⟨COFE.lim_dist c.fst n, COFE.lim_dist c.snd n⟩

end LeanIrisX

