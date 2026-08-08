import LeanIrisX.Algebra.InvariantRegistry
import LeanIrisX.Algebra.MaskToken

/-!
The structural world-satisfaction invariant used before solving the recursive
`IProp` domain equation.  It connects the registry with the mutually exclusive
closed/enabled and opened/disabled name sets.
-/

namespace LeanIrisX

structure WorldSnapshot (PROP : Type u) [OFE PROP] where
  registry : InvariantRegistry PROP
  registered : Mask
  closed : Mask
  opened : Mask

namespace WorldSatisfaction

variable {PROP : Type u} [OFE PROP]

def Partition (all closed opened : Mask) : Prop :=
  (∀ N, all N ↔ closed N ∨ opened N) ∧ Mask.Disjoint closed opened

def RegistryCoversAt (n : Nat) (r : InvariantRegistry PROP) (names : Mask) : Prop :=
  ∀ N, names N → ∃ P, r N ≡{n}≡ InvariantEntry.allocated P

def WSatAt (n : Nat) (w : WorldSnapshot PROP) : Prop :=
  CMRA.validN n w.registry ∧
  Partition w.registered w.closed w.opened ∧
  RegistryCoversAt n w.registry w.registered

theorem closed_opened_tokens_valid {all closed opened : Mask}
    (h : Partition all closed opened) :
    CMRA.valid (CMRA.op (MaskToken.ofMask closed) (MaskToken.ofMask opened)) :=
  (MaskToken.ofMask_op_valid_iff_disjoint closed opened).2 h.2

theorem registered_is_exactly_one_state {all closed opened : Mask}
    (h : Partition all closed opened) {N : Namespace} (hN : all N) :
    (closed N ∧ ¬ opened N) ∨ (opened N ∧ ¬ closed N) := by
  rcases (h.1 N).mp hN with hc | ho
  · exact Or.inl ⟨hc, fun ho => h.2 N hc ho⟩
  · exact Or.inr ⟨ho, fun hc => h.2 N hc ho⟩

end WorldSatisfaction
end LeanIrisX
