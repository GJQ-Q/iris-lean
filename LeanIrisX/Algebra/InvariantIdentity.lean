import LeanIrisX.Algebra.Auth
import LeanIrisX.Algebra.ResourceMap
import LeanIrisX.Algebra.Option
import LeanIrisX.Logic.GhostState

/-!
# Invariant identities and persistent handles

Namespaces group invariants for masking; they are not invariant identities.
This module introduces a separate internal ghost name and stores persistent
agreement handles in an authoritative catalog.
-/

namespace LeanIrisX

namespace Agreement

instance totalCoreAgreement {α : Type u} [OFE α] : TotalCore (Agreement α) where
  core := id
  core_spec _ := rfl

end Agreement

namespace OptionCMRA

instance totalCoreOption {α : Type u} [OFE α] [CMRA α] [TotalCore α] :
    TotalCore (Option α) where
  core
    | none => none
    | some x => some (TotalCore.core x)
  core_spec x := by
    cases x with
    | none => rfl
    | some x =>
      change some (CMRA.pcore x) = some (some (TotalCore.core x))
      rw [TotalCore.core_spec]

end OptionCMRA

/-- The internal identity is distinct from its namespace. -/
structure InvariantId where
  ghost : GhostName
deriving DecidableEq, Repr

/-- Catalog keys keep the mask namespace and the fresh internal identity
separate.  Distinct identities may intentionally share one namespace. -/
structure InvariantKey where
  ns : Namespace
  id : InvariantId
deriving DecidableEq, Repr

namespace InvariantIdentity

variable {PROP : Type u} [OFE PROP]

abbrev Cell := Option (Agreement (Later PROP))
abbrev Catalog := ResourceMap InvariantKey (Cell (PROP := PROP))
abbrev Ghost := Auth (Catalog (PROP := PROP))

def key (N : Namespace) (γ : GhostName) : InvariantKey :=
  ⟨N, ⟨γ⟩⟩

def cell (P : PROP) : Cell (PROP := PROP) :=
  some (Agreement.toAgreement (Later.next P))

def entry (N : Namespace) (γ : GhostName) (P : PROP) :
    Catalog (PROP := PROP) :=
  ResourceMap.singleton (key N γ) (cell P)

@[simp] theorem entry_same (N : Namespace) (γ : GhostName) (P : PROP) :
    entry N γ P (key N γ) = cell P := by
  simp [entry]

@[simp] theorem entry_other {N : Namespace} {γ : GhostName} {P : PROP}
    {k : InvariantKey} (h : k ≠ key N γ) : entry N γ P k = UCMRA.unit := by
  simp [entry, h]

def authoritative (r : Catalog (PROP := PROP)) : Ghost (PROP := PROP) :=
  Auth.authoritative r

def handle (N : Namespace) (γ : GhostName) (P : PROP) : Ghost (PROP := PROP) :=
  Auth.fragment (entry N γ P)

theorem cell_validN (n : Nat) (P : PROP) :
    CMRA.validN n (cell P) :=
  Agreement.toAgreement_validN n (Later.next P)

theorem entry_valid (N : Namespace) (γ : GhostName) (P : PROP) :
    CMRA.valid (entry N γ P) := by
  rw [CMRA.valid_iff_validN]
  intro n k
  change CMRA.validN n (entry N γ P k)
  by_cases hk : k = key N γ
  · subst k
    rw [entry_same]
    exact cell_validN n P
  · rw [entry_other hk]
    exact CMRA.validN_of_valid UCMRA.unit_valid n

theorem entry_op_idem (N : Namespace) (γ : GhostName) (P : PROP) :
    CMRA.op (entry N γ P) (entry N γ P) = entry N γ P := by
  funext k
  change CMRA.op (entry N γ P k) (entry N γ P k) = entry N γ P k
  by_cases hk : k = key N γ
  · subst k
    rw [entry_same]
    change some (CMRA.op (Agreement.toAgreement (Later.next P))
      (Agreement.toAgreement (Later.next P))) =
      some (Agreement.toAgreement (Later.next P))
    congr 1
    exact Agreement.op_idem _
  · rw [entry_other hk]
    exact UCMRA.unit_left _

/-- Public invariant handles are duplicable at the camera level. -/
theorem handle_op_idem (N : Namespace) (γ : GhostName) (P : PROP) :
    CMRA.op (handle N γ P) (handle N γ P) = handle N γ P := by
  change View.op (View.Frag (entry N γ P)) (View.Frag (entry N γ P)) =
    View.Frag (entry N γ P)
  change View.mk none (CMRA.op (entry N γ P) (entry N γ P)) =
    View.mk none (entry N γ P)
  rw [entry_op_idem]

/-- Two invariants may share a namespace when their internal identities are
different. -/
theorem same_namespace_distinct_ids_valid
    {γ₁ γ₂ : GhostName} (hγ : γ₁ ≠ γ₂)
    (N : Namespace) (P Q : PROP) :
    CMRA.valid (CMRA.op (entry N γ₁ P) (entry N γ₂ Q)) := by
  rw [CMRA.valid_iff_validN]
  intro n k
  change CMRA.validN n
    (CMRA.op (entry N γ₁ P k) (entry N γ₂ Q k))
  by_cases h₁ : k = key N γ₁
  · subst k
    have h₂ : key N γ₁ ≠ key N γ₂ := by
      intro h
      exact hγ (congrArg (fun x => x.id.ghost) h)
    rw [entry_same, entry_other h₂]
    simpa [UCMRA.unit_right] using cell_validN n P
  · by_cases h₂ : k = key N γ₂
    · subst k
      rw [entry_other h₁, entry_same]
      simpa [UCMRA.unit_left] using cell_validN n Q
    · rw [entry_other h₁, entry_other h₂]
      exact CMRA.validN_of_valid UCMRA.unit_valid n

/-- Reusing one internal identity forces agreement of the guarded bodies. -/
theorem same_id_forces_body_agreement {n : Nat} {N : Namespace}
    {γ : GhostName} {P Q : PROP}
    (h : CMRA.validN (n + 1)
      (CMRA.op (entry N γ P) (entry N γ Q))) :
    P ≡{n}≡ Q := by
  have hk := h (key N γ)
  change CMRA.validN (n + 1)
    (CMRA.op (entry N γ P (key N γ))
      (entry N γ Q (key N γ))) at hk
  rw [entry_same, entry_same] at hk
  change CMRA.validN (n + 1)
    (CMRA.op (Agreement.toAgreement (Later.next P))
      (Agreement.toAgreement (Later.next Q))) at hk
  have hLater : Later.next P ≡{n + 1}≡ Later.next Q :=
    Agreement.toAgreement_op_valid_iff.mp hk
  exact hLater n (Nat.lt_succ_self n)

end InvariantIdentity
end LeanIrisX
