import LeanIrisX.Core.Later

/-!
Raw semantic layer of the Iris agreement construction.

The carrier is a nonempty list. Distance is the Hausdorff lifting of the
underlying OFE distance and validity requires pairwise agreement at a step.
The quotient by same elements is deliberately deferred to the next stage.
-/

namespace LeanIrisX.Agreement

structure Raw (α : Type u) where
  values : List α
  nonempty : values ≠ []

namespace Raw

variable {α : Type u}

def singleton (a : α) : Raw α := ⟨[a], by simp⟩

def op (x y : Raw α) : Raw α :=
  ⟨x.values ++ y.values, List.append_ne_nil_of_left_ne_nil x.nonempty _⟩

def SameElems (x y : Raw α) : Prop :=
  (∀ a ∈ x.values, a ∈ y.values) ∧
  (∀ b ∈ y.values, b ∈ x.values)

theorem sameElems_equivalence : Equivalence (SameElems (α := α)) where
  refl _ := ⟨fun _ h => h, fun _ h => h⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ :=
    ⟨fun a ha => h₂.1 a (h₁.1 a ha), fun c hc => h₁.2 c (h₂.2 c hc)⟩

instance : Setoid (Raw α) := ⟨SameElems, sameElems_equivalence⟩

theorem op_sameElems {a b c d : Raw α}
    (hac : SameElems a c) (hbd : SameElems b d) :
    SameElems (op a b) (op c d) := by
  constructor <;> intro x hx <;> simp only [op, List.mem_append] at hx ⊢
  · exact hx.elim (Or.inl ∘ hac.1 x) (Or.inr ∘ hbd.1 x)
  · exact hx.elim (Or.inl ∘ hac.2 x) (Or.inr ∘ hbd.2 x)

variable [OFE α]

def Dist (n : Nat) (x y : Raw α) : Prop :=
  (∀ a ∈ x.values, ∃ b ∈ y.values, a ≡{n}≡ b) ∧
  (∀ b ∈ y.values, ∃ a ∈ x.values, a ≡{n}≡ b)

def ValidN (n : Nat) (x : Raw α) : Prop :=
  ∀ a ∈ x.values, ∀ b ∈ x.values, a ≡{n}≡ b

theorem dist_congr {n : Nat} {a b c d : Raw α}
    (hac : SameElems a c) (hbd : SameElems b d) :
    Dist n a b ↔ Dist n c d := by
  constructor
  · intro h
    exact ⟨fun x hx => (h.1 x (hac.2 x hx)).imp fun y p => ⟨hbd.1 y p.1, p.2⟩,
      fun y hy => (h.2 y (hbd.2 y hy)).imp fun x p => ⟨hac.1 x p.1, p.2⟩⟩
  · intro h
    exact ⟨fun x hx => (h.1 x (hac.1 x hx)).imp fun y p => ⟨hbd.2 y p.1, p.2⟩,
      fun y hy => (h.2 y (hbd.1 y hy)).imp fun x p => ⟨hac.2 x p.1, p.2⟩⟩

theorem validN_congr {n : Nat} {x y : Raw α} (h : SameElems x y) :
    ValidN n x ↔ ValidN n y := by
  constructor
  · intro hv a ha b hb; exact hv a (h.2 a ha) b (h.2 b hb)
  · intro hv a ha b hb; exact hv a (h.1 a ha) b (h.1 b hb)

theorem dist_refl (n : Nat) (x : Raw α) : Dist n x x := by
  constructor <;> intro a ha <;> exact ⟨a, ha, OFE.refl n a⟩

theorem dist_symm {n : Nat} {x y : Raw α} (h : Dist n x y) : Dist n y x := by
  constructor
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h.2 b hb
    exact ⟨a, ha, OFE.symm hab⟩
  · intro a ha
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    exact ⟨b, hb, OFE.symm hab⟩

theorem dist_trans {n : Nat} {x y z : Raw α}
    (hxy : Dist n x y) (hyz : Dist n y z) : Dist n x z := by
  constructor
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hxy.1 a ha
    obtain ⟨c, hc, hbc⟩ := hyz.1 b hb
    exact ⟨c, hc, OFE.trans hab hbc⟩
  · intro c hc
    obtain ⟨b, hb, hbc⟩ := hyz.2 c hc
    obtain ⟨a, ha, hab⟩ := hxy.2 b hb
    exact ⟨a, ha, OFE.trans hab hbc⟩

theorem dist_mono {n m : Nat} (hmn : m ≤ n) {x y : Raw α}
    (h : Dist n x y) : Dist m x y := by
  constructor
  · intro a ha
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    exact ⟨b, hb, OFE.mono hmn hab⟩
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h.2 b hb
    exact ⟨a, ha, OFE.mono hmn hab⟩

theorem op_comm_dist (n : Nat) (x y : Raw α) : Dist n (op x y) (op y x) := by
  constructor <;> intro a ha
  · exact ⟨a, by simpa [op, or_comm] using ha, OFE.refl n a⟩
  · exact ⟨a, by simpa [op, or_comm] using ha, OFE.refl n a⟩

theorem op_assoc_dist (n : Nat) (x y z : Raw α) :
    Dist n (op x (op y z)) (op (op x y) z) := by
  constructor <;> intro a ha
  · exact ⟨a, by simpa [op, List.append_assoc] using ha, OFE.refl n a⟩
  · exact ⟨a, by simpa [op, List.append_assoc] using ha, OFE.refl n a⟩

theorem op_idem_dist (n : Nat) (x : Raw α) : Dist n (op x x) x := by
  constructor
  · intro a ha
    simp only [op, List.mem_append] at ha
    exact ⟨a, ha.elim id id, OFE.refl n a⟩
  · intro a ha
    exact ⟨a, by simp [op, ha], OFE.refl n a⟩

theorem validN_mono {n m : Nat} (hmn : m ≤ n) {x : Raw α}
    (h : ValidN n x) : ValidN m x := by
  intro a ha b hb
  exact OFE.mono hmn (h a ha b hb)

theorem validN_ne {n : Nat} {x y : Raw α}
    (hxy : Dist n x y) (hx : ValidN n x) : ValidN n y := by
  intro a ha b hb
  obtain ⟨a', ha', haa'⟩ := hxy.2 a ha
  obtain ⟨b', hb', hbb'⟩ := hxy.2 b hb
  exact OFE.trans (OFE.symm haa') (OFE.trans (hx a' ha' b' hb') hbb')

theorem validN_succ {n : Nat} {x : Raw α}
    (h : ValidN (n + 1) x) : ValidN n x := by
  intro a ha b hb
  exact OFE.mono (Nat.le_succ n) (h a ha b hb)

theorem op_ne {n : Nat} {x y₁ y₂ : Raw α} (h : Dist n y₁ y₂) :
    Dist n (op x y₁) (op x y₂) := by
  constructor
  · intro a ha
    simp only [op, List.mem_append] at ha ⊢
    rcases ha with hx | hy
    · exact ⟨a, Or.inl hx, OFE.refl n a⟩
    · obtain ⟨b, hb, hab⟩ := h.1 a hy
      exact ⟨b, Or.inr hb, hab⟩
  · intro a ha
    simp only [op, List.mem_append] at ha ⊢
    rcases ha with hx | hy
    · exact ⟨a, Or.inl hx, OFE.refl n a⟩
    · obtain ⟨b, hb, hab⟩ := h.2 a hy
      exact ⟨b, Or.inr hb, hab⟩

theorem singleton_validN (n : Nat) (a : α) : ValidN n (singleton a) := by
  intro x hx y hy
  simp [singleton] at hx hy
  subst x; subst y
  exact OFE.refl n a

theorem singleton_dist_iff {n : Nat} {a b : α} :
    Dist n (singleton a) (singleton b) ↔ a ≡{n}≡ b := by
  constructor
  · intro h
    obtain ⟨b', hb', hab⟩ := h.1 a (by simp [singleton])
    simp [singleton] at hb'
    subst b'
    exact hab
  · intro hab
    constructor
    · intro x hx
      simp [singleton] at hx
      subst x
      exact ⟨b, by simp [singleton], hab⟩
    · intro y hy
      simp [singleton] at hy
      subst y
      exact ⟨a, by simp [singleton], hab⟩

theorem op_validN_left {n : Nat} {x y : Raw α}
    (h : ValidN n (op x y)) : ValidN n x := by
  intro a ha b hb
  apply h a (by simp [op, ha]) b (by simp [op, hb])

theorem op_validN_implies_dist {n : Nat} {x y : Raw α}
    (h : ValidN n (op x y)) : Dist n x y := by
  have get (z : Raw α) : ∃ a, a ∈ z.values := by
    cases z with
    | mk values hn =>
      cases values with
      | nil => contradiction
      | cons a as => exact ⟨a, by simp⟩
  constructor
  · intro a ha
    obtain ⟨b, hb⟩ := get y
    exact ⟨b, hb, h a (by simp [op, ha]) b (by simp [op, hb])⟩
  · intro b hb
    obtain ⟨a, ha⟩ := get x
    exact ⟨a, ha, h a (by simp [op, ha]) b (by simp [op, hb])⟩

theorem op_same_validN {n : Nat} {x : Raw α} (hx : ValidN n x) :
    ValidN n (op x x) := by
  intro a ha b hb
  simp only [op, List.mem_append] at ha hb
  exact hx a (ha.elim id id) b (hb.elim id id)

end Raw
end LeanIrisX.Agreement
