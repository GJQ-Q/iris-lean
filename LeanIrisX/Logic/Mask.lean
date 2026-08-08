/-! Concrete namespaces and masks used by invariants and fancy updates. -/

namespace LeanIrisX

/-- Hierarchical Iris namespace components. -/
abbrev Namespace := List Nat

namespace Namespace

def root : Namespace := []
def child (N : Namespace) (i : Nat) : Namespace := N ++ [i]
def Prefix (N K : Namespace) : Prop := ∃ suffix, K = N ++ suffix

theorem prefix_refl (N : Namespace) : Prefix N N := ⟨[], by simp⟩

theorem prefix_trans {N K L : Namespace} (hNK : Prefix N K)
    (hKL : Prefix K L) : Prefix N L := by
  obtain ⟨a, rfl⟩ := hNK
  obtain ⟨b, rfl⟩ := hKL
  exact ⟨a ++ b, by simp [List.append_assoc]⟩

theorem prefix_child (N : Namespace) (i : Nat) : Prefix N (child N i) :=
  ⟨[i], rfl⟩

end Namespace

/-- A mask is a set of namespace names. Functions give extensional set
semantics without introducing a finite-set implementation dependency. -/
abbrev Mask := Namespace → Prop

namespace Mask

def empty : Mask := fun _ => False
def full : Mask := fun _ => True
def singleton (N : Namespace) : Mask := fun K => K = N
def union (E F : Mask) : Mask := fun N => E N ∨ F N
def inter (E F : Mask) : Mask := fun N => E N ∧ F N
def diff (E F : Mask) : Mask := fun N => E N ∧ ¬ F N
/-- Insert one exact namespace name. -/
def insert (E : Mask) (N : Namespace) : Mask := fun K => E K ∨ K = N
/-- Erase one exact namespace name (unlike `without`, which erases a subtree). -/
def erase (E : Mask) (N : Namespace) : Mask := fun K => E K ∧ K ≠ N
/-- Remove an entire namespace subtree from a mask. -/
def without (E : Mask) (N : Namespace) : Mask :=
  fun K => E K ∧ ¬ Namespace.Prefix N K

def Subset (E F : Mask) : Prop := ∀ N, E N → F N
def Disjoint (E F : Mask) : Prop := ∀ N, E N → F N → False

infix:50 " ⊆ₘ " => Subset
infix:55 " ∪ₘ " => union
infix:55 " ∩ₘ " => inter

theorem subset_refl (E : Mask) : E ⊆ₘ E := by intro N h; exact h
theorem subset_trans {E F G : Mask} (hEF : E ⊆ₘ F) (hFG : F ⊆ₘ G) :
    E ⊆ₘ G := by intro N h; exact hFG N (hEF N h)
theorem without_subset (E : Mask) (N : Namespace) : without E N ⊆ₘ E :=
  by intro K h; exact h.1
theorem singleton_subset_full (N : Namespace) : singleton N ⊆ₘ full :=
  by intro K h; trivial
theorem without_excludes_prefix (E : Mask) {N K : Namespace}
    (hNK : Namespace.Prefix N K) : ¬ without E N K := by
  intro h
  exact h.2 hNK

@[simp] theorem insert_self (E : Mask) (N : Namespace) : insert E N N :=
  Or.inr rfl

@[simp] theorem erase_self (E : Mask) (N : Namespace) : ¬ erase E N N := by
  intro h
  exact h.2 rfl

theorem erase_insert_cancel {E : Mask} {N : Namespace} :
    erase (insert E N) N = erase E N := by
  funext K
  apply propext
  constructor <;> intro h
  · exact ⟨h.1.elim id (fun hKN => False.elim (h.2 hKN)), h.2⟩
  · exact ⟨Or.inl h.1, h.2⟩

theorem insert_erase_cancel {E : Mask} {N : Namespace} (hN : E N) :
    insert (erase E N) N = E := by
  funext K
  apply propext
  constructor
  · intro h
    rcases h with h | rfl
    · exact h.1
    · exact hN
  · intro hK
    by_cases hKN : K = N
    · exact Or.inr hKN
    · exact Or.inl ⟨hK, hKN⟩

end Mask
end LeanIrisX
