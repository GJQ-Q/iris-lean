import LeanIrisX.Algebra.Product

/-!
Semantically aligned uniform predicates.

The important differences from the prototype are:
* predicates are only evaluated on resources valid at the current step;
* resource monotonicity uses step-indexed inclusion `IncludedN`;
* UPred itself carries the standard step-indexed OFE and COFE structures.
-/

namespace LeanIrisX

/-- A resource together with evidence that it is valid at step `n`. -/
structure ValidAt (M : Type u) [OFE M] [CMRA M] (n : Nat) where
  val : M
  property : CMRA.validN n val

namespace ValidAt

variable {M : Type u} [OFE M] [CMRA M]

def lower {n m : Nat} (x : ValidAt M n) (h : m ≤ n) : ValidAt M m :=
  ⟨x.val, CMRA.validN_mono h x.property⟩

end ValidAt

/-- Iris-style uniform predicates over a unital camera. -/
structure UPred (M : Type u) [OFE M] [CMRA M] [UCMRA M] where
  holds : (n : Nat) → ValidAt M n → Prop
  mono : ∀ {n₁ n₂} {x₁ : ValidAt M n₁} {x₂ : ValidAt M n₂},
    holds n₁ x₁ → CMRA.IncludedN n₂ x₁.val x₂.val → n₂ ≤ n₁ → holds n₂ x₂

namespace UPred

variable {M : Type u} [OFE M] [CMRA M] [UCMRA M]

def holdsAt (P : UPred M) (n : Nat) (x : M) (hx : CMRA.validN n x) : Prop :=
  P.holds n ⟨x, hx⟩

theorem includedN_refl (n : Nat) (x : M) : CMRA.IncludedN n x x :=
  ⟨UCMRA.unit, by simpa [UCMRA.unit_right] using OFE.refl n x⟩

omit [UCMRA M] in theorem includedN_mono {n m : Nat} (h : m ≤ n) {x y : M}
    (hxy : CMRA.IncludedN n x y) : CMRA.IncludedN m x y := by
  obtain ⟨z, hz⟩ := hxy
  exact ⟨z, OFE.mono h hz⟩

omit [UCMRA M] in theorem includedN_trans {n : Nat} {x y z : M}
    (hxy : CMRA.IncludedN n x y) (hyz : CMRA.IncludedN n y z) :
    CMRA.IncludedN n x z := by
  obtain ⟨f, hf⟩ := hxy
  obtain ⟨g, hg⟩ := hyz
  refine ⟨CMRA.op f g, ?_⟩
  exact OFE.trans hg (OFE.trans (CMRA.op_ne_left g n hf)
    (OFE.of_eq (CMRA.op_assoc x f g).symm))

@[ext] theorem ext {P Q : UPred M}
    (h : ∀ n (x : M) (hx : CMRA.validN n x),
      P.holdsAt n x hx ↔ Q.holdsAt n x hx) : P = Q := by
  cases P with
  | mk ph pm =>
    cases Q with
    | mk qh qm =>
      have hpq : ph = qh := by
        funext n x
        apply propext
        exact h n x.val x.property
      cases hpq
      rfl

instance : OFE (UPred M) where
  dist n P Q := ∀ m (x : M) (hx : CMRA.validN m x), m ≤ n →
    (P.holdsAt m x hx ↔ Q.holdsAt m x hx)
  dist_equivalence n := by
    constructor
    · intro P m x hx hmn; exact Iff.rfl
    · intro P Q h m x hx hmn; exact (h m x hx hmn).symm
    · intro P Q R hpq hqr m x hx hmn
      exact (hpq m x hx hmn).trans (hqr m x hx hmn)
  eq_dist P Q := by
    constructor
    · intro h n m x hx hmn; subst Q; exact Iff.rfl
    · intro h
      apply ext
      intro n x hx
      exact h n n x hx (Nat.le_refl n)
  dist_mono hnm h m x hx hmn := h m x hx (Nat.le_trans hmn hnm)

instance : COFE (UPred M) where
  limit c := {
    holds := fun n x => (c n).holds n x
    mono := by
      intro n₁ n₂ x₁ x₂ hp hinc hle
      have hp' : (c n₁).holds n₂ x₂ := (c n₁).mono hp hinc hle
      have hc : c n₂ ≡{n₂}≡ c n₁ := c.coherent hle
      exact (hc n₂ x₂.val x₂.property (Nat.le_refl n₂)).mpr hp'
  }
  limit_spec := by
    intro c n m x hx hmn
    change ((c m).holdsAt m x hx ↔ (c n).holdsAt m x hx)
    exact c.coherent hmn m x hx (Nat.le_refl m)

def Entails (P Q : UPred M) : Prop :=
  ∀ n (x : M) (hx : CMRA.validN n x), P.holdsAt n x hx → Q.holdsAt n x hx

infix:45 " ⊢ᵤ " => Entails

def pure (φ : Prop) : UPred M where
  holds _ _ := φ
  mono h _ _ := h

def top : UPred M := pure True
def bot : UPred M := pure False

/-- Step-indexed ownership. -/
def own (a : M) : UPred M where
  holds n x := CMRA.IncludedN n a x.val
  mono := by
    intro n₁ n₂ x₁ x₂ ha h₁₂ hle
    exact includedN_trans (includedN_mono hle ha) h₁₂

/-- Separating conjunction. Resource decomposition is observed at the current
step index, rather than by Lean equality. -/
def sep (P Q : UPred M) : UPred M where
  holds n x := ∃ a b,
    x.val ≡{n}≡ CMRA.op a b ∧
    ∃ ha : CMRA.validN n a, ∃ hb : CMRA.validN n b,
      P.holdsAt n a ha ∧ Q.holdsAt n b hb
  mono := by
    intro n₁ n₂ x₁ x₂ hp hinc hle
    obtain ⟨a, b, hab, ha, hb, hpa, hqb⟩ := hp
    obtain ⟨f, hframe⟩ := hinc
    have hab' : x₁.val ≡{n₂}≡ CMRA.op a b := OFE.mono hle hab
    have hx₂split : x₂.val ≡{n₂}≡ CMRA.op a (CMRA.op b f) :=
      OFE.trans hframe <| OFE.trans (CMRA.op_ne_left f n₂ hab') <|
        OFE.of_eq (CMRA.op_assoc a b f).symm
    have hvSplit : CMRA.validN n₂ (CMRA.op a (CMRA.op b f)) :=
      CMRA.validN_ne hx₂split x₂.property
    have hva : CMRA.validN n₂ a := CMRA.validN_op_left hvSplit
    have hvbf : CMRA.validN n₂ (CMRA.op b f) := by
      apply CMRA.validN_op_left (x := CMRA.op b f) (y := a)
      simpa [CMRA.op_comm] using hvSplit
    refine ⟨a, CMRA.op b f, hx₂split, hva, hvbf, ?_, ?_⟩
    · exact P.mono hpa (includedN_refl n₂ a) hle
    · apply Q.mono hqb
      · exact ⟨f, OFE.refl n₂ (CMRA.op b f)⟩
      · exact hle

def later (P : UPred M) : UPred M where
  holds n x := match n with
    | 0 => True
    | k + 1 => P.holds k (x.lower (Nat.le_succ k))
  mono := by
    intro n₁ n₂ x₁ x₂ hp hinc hle
    cases n₂ with
    | zero => trivial
    | succ n₂ =>
      cases n₁ with
      | zero => exact False.elim (Nat.not_succ_le_zero n₂ hle)
      | succ n₁ =>
        apply P.mono hp
        · exact includedN_mono (Nat.le_succ n₂) hinc
        · exact Nat.succ_le_succ_iff.mp hle

theorem entails_refl (P : UPred M) : P ⊢ᵤ P := by
  intro n x hx hp; exact hp

theorem entails_trans {P Q R : UPred M} (hpq : P ⊢ᵤ Q) (hqr : Q ⊢ᵤ R) :
    P ⊢ᵤ R := by
  intro n x hx hp
  exact hqr n x hx (hpq n x hx hp)

theorem own_mono {a b : M} (h : ∀ n, CMRA.IncludedN n a b) :
    own b ⊢ᵤ own a := by
  intro n x hx hbx
  exact includedN_trans (h n) hbx

theorem sep_comm (P Q : UPred M) : sep P Q ⊢ᵤ sep Q P := by
  intro n x hx hp
  obtain ⟨a, b, hab, ha, hb, hpa, hqb⟩ := hp
  exact ⟨b, a, OFE.trans hab (OFE.of_eq (CMRA.op_comm a b)), hb, ha, hqb, hpa⟩

theorem later_intro (P : UPred M) : P ⊢ᵤ later P := by
  intro n x hx hp
  cases n with
  | zero => trivial
  | succ n =>
    exact P.mono hp (includedN_refl n x) (Nat.le_succ n)

end UPred
end LeanIrisX
