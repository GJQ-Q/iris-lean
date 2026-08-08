/-!
Copyright (c) 2026 LeanIrisX contributors.
Released under Apache 2.0.

An independent Lean 4 implementation of Iris ordered families of
equivalences. The interface follows the Iris OFE specification: every indexed
distance is an equivalence, equality is agreement at every index, and indexed
distance is downward closed.
-/

namespace LeanIrisX

class OFE (α : Type u) where
  dist : Nat → α → α → Prop
  dist_equivalence : ∀ n, Equivalence (dist n)
  eq_dist : ∀ x y, x = y ↔ ∀ n, dist n x y
  dist_mono : ∀ {n m x y}, n ≤ m → dist m x y → dist n x y

notation:50 x:51 " ≡{" n "}≡ " y:51 => OFE.dist n x y

namespace OFE

variable {α : Type u} [OFE α]

theorem refl (n : Nat) (x : α) : x ≡{n}≡ x :=
  (OFE.dist_equivalence n).1 x

theorem symm {n : Nat} {x y : α} (h : x ≡{n}≡ y) : y ≡{n}≡ x :=
  (OFE.dist_equivalence n).2 h

theorem trans {n : Nat} {x y z : α}
    (hxy : x ≡{n}≡ y) (hyz : y ≡{n}≡ z) : x ≡{n}≡ z :=
  (OFE.dist_equivalence n).3 hxy hyz

theorem mono {n m : Nat} (hnm : n ≤ m) {x y : α}
    (h : x ≡{m}≡ y) : x ≡{n}≡ y :=
  OFE.dist_mono hnm h

theorem of_eq {n : Nat} {x y : α} (h : x = y) : x ≡{n}≡ y := by
  subst y
  exact refl n x

theorem eq_iff_dist (x y : α) : x = y ↔ ∀ n, x ≡{n}≡ y :=
  OFE.eq_dist x y

theorem eq_of_dist {x y : α} (h : ∀ n, x ≡{n}≡ y) : x = y :=
  (eq_iff_dist x y).2 h

/-- Inputs agree at all indices strictly smaller than `n`. -/
def DistLater (n : Nat) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

theorem distLater_zero (x y : α) : DistLater 0 x y := by
  intro m hm
  exact False.elim (Nat.not_lt_zero m hm)

theorem distLater_refl (n : Nat) (x : α) : DistLater n x x := by
  intro m hm
  exact refl m x

theorem distLater_symm {n : Nat} {x y : α} (h : DistLater n x y) :
    DistLater n y x := by
  intro m hm
  exact symm (h m hm)

theorem distLater_trans {n : Nat} {x y z : α}
    (hxy : DistLater n x y) (hyz : DistLater n y z) : DistLater n x z := by
  intro m hm
  exact trans (hxy m hm) (hyz m hm)

theorem dist_to_distLater {n : Nat} {x y : α} (h : x ≡{n}≡ y) :
    DistLater n x y := by
  intro m hm
  exact mono (Nat.le_of_lt hm) h

theorem distLater_succ_iff {n : Nat} {x y : α} :
    DistLater (n + 1) x y ↔ x ≡{n}≡ y := by
  constructor
  · intro h
    exact h n (Nat.lt_succ_self n)
  · intro h m hm
    exact mono (Nat.le_of_lt_succ hm) h

/-- Canonical discrete OFE: indexed distance is Lean equality at every index. -/
@[reducible] def ofDiscrete (α : Type u) : OFE α where
  dist _ x y := x = y
  dist_equivalence _ := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  eq_dist x y := by
    constructor
    · intro h n; exact h
    · intro h; exact h 0
  dist_mono _ h := h

/-- An OFE is discrete when distance at any index implies Lean equality. -/
class Discrete (α : Type u) [OFE α] : Prop where
  eq_of_dist : ∀ {n} {x y : α}, x ≡{n}≡ y → x = y

theorem Discrete.dist_iff [Discrete α] (n : Nat) (x y : α) :
    x ≡{n}≡ y ↔ x = y :=
  ⟨Discrete.eq_of_dist, of_eq⟩

end OFE

/-- A function preserving indexed distance. -/
def NonExpansive {α : Type u} {β : Type v} [OFE α] [OFE β] (f : α → β) : Prop :=
  ∀ n ⦃x y : α⦄, (x ≡{n}≡ y) → (f x ≡{n}≡ f y)

/-- A binary function preserving indexed distance in both arguments. -/
def NonExpansive₂ {α : Type u} {β : Type v} {γ : Type w}
    [OFE α] [OFE β] [OFE γ] (f : α → β → γ) : Prop :=
  ∀ n ⦃x₁ x₂ : α⦄, (x₁ ≡{n}≡ x₂) →
    ∀ ⦃y₁ y₂ : β⦄, (y₁ ≡{n}≡ y₂) → f x₁ y₁ ≡{n}≡ f x₂ y₂

/-- A function mapping `DistLater n` inputs to `n`-equivalent outputs. -/
def Contractive {α : Type u} {β : Type v} [OFE α] [OFE β] (f : α → β) : Prop :=
  ∀ n ⦃x y : α⦄, OFE.DistLater n x y → (f x ≡{n}≡ f y)

namespace NonExpansive

variable {α : Type u} {β : Type v} {γ : Type w}
variable [OFE α] [OFE β] [OFE γ]

theorem id : NonExpansive (fun x : α => x) := by
  intro n x y h
  exact h

theorem const (b : β) : NonExpansive (fun _ : α => b) := by
  intro n x y h
  exact OFE.refl n b

theorem comp {f : α → β} {g : β → γ}
    (hg : NonExpansive g) (hf : NonExpansive f) : NonExpansive (g ∘ f) := by
  intro n x y h
  exact hg n (hf n h)

end NonExpansive

namespace NonExpansive₂

variable {α : Type u} {β : Type v} {γ : Type w}
variable [OFE α] [OFE β] [OFE γ]

theorem right {f : α → β → γ} (hf : NonExpansive₂ f) (x : α) :
    NonExpansive (f x) := by
  intro n y₁ y₂ hy
  exact hf n (OFE.refl n x) hy

theorem left {f : α → β → γ} (hf : NonExpansive₂ f) (y : β) :
    NonExpansive (fun x => f x y) := by
  intro n x₁ x₂ hx
  exact hf n hx (OFE.refl n y)

end NonExpansive₂

namespace Contractive

variable {α : Type u} {β : Type v} [OFE α] [OFE β]

theorem const (b : β) : Contractive (fun _ : α => b) := by
  intro n x y h
  exact OFE.refl n b

theorem nonExpansive {f : α → β} (hf : Contractive f) : NonExpansive f := by
  intro n x y hxy
  exact hf n (OFE.dist_to_distLater hxy)

theorem succ {f : α → β} (hf : Contractive f) {n : Nat} {x y : α}
    (hxy : x ≡{n}≡ y) : f x ≡{n + 1}≡ f y :=
  hf (n + 1) (OFE.distLater_succ_iff.2 hxy)

end Contractive

/-! Canonical discrete instances used by examples. These are explicit by
type, rather than a blanket `DecidableEq → OFE` instance. -/

instance natOFE : OFE Nat := OFE.ofDiscrete Nat
instance boolOFE : OFE Bool := OFE.ofDiscrete Bool
instance unitOFE : OFE Unit := OFE.ofDiscrete Unit

instance natDiscrete : OFE.Discrete Nat := ⟨fun h => h⟩
instance boolDiscrete : OFE.Discrete Bool := ⟨fun h => h⟩
instance unitDiscrete : OFE.Discrete Unit := ⟨fun h => h⟩

instance prodOFE {α : Type u} {β : Type v} [OFE α] [OFE β] : OFE (α × β) where
  dist n x y := (x.1 ≡{n}≡ y.1) ∧ (x.2 ≡{n}≡ y.2)
  dist_equivalence n := by
    constructor
    · intro x; exact ⟨OFE.refl n _, OFE.refl n _⟩
    · intro x y h; exact ⟨OFE.symm h.1, OFE.symm h.2⟩
    · intro x y z hxy hyz
      exact ⟨OFE.trans hxy.1 hyz.1, OFE.trans hxy.2 hyz.2⟩
  eq_dist x y := by
    constructor
    · intro h n; subst y; exact ⟨OFE.refl n _, OFE.refl n _⟩
    · intro h
      apply Prod.ext
      · exact OFE.eq_of_dist (fun n => (h n).1)
      · exact OFE.eq_of_dist (fun n => (h n).2)
  dist_mono hnm h := ⟨OFE.mono hnm h.1, OFE.mono hnm h.2⟩

theorem fst_nonExpansive {α : Type u} {β : Type v} [OFE α] [OFE β] :
    NonExpansive (Prod.fst : α × β → α) := by
  intro n x y h
  exact h.1

theorem snd_nonExpansive {α : Type u} {β : Type v} [OFE α] [OFE β] :
    NonExpansive (Prod.snd : α × β → β) := by
  intro n x y h
  exact h.2

end LeanIrisX
