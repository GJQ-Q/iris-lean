import LeanIrisX.Logic.UPred

/-! BI connectives for the semantically aligned UPred model. -/

namespace LeanIrisX.UPred

variable {M : Type u} [OFE M] [CMRA M] [UCMRA M]

def and (P Q : UPred M) : UPred M where
  holds n x := P.holds n x ∧ Q.holds n x
  mono hp hinc hle := ⟨P.mono hp.1 hinc hle, Q.mono hp.2 hinc hle⟩

def or (P Q : UPred M) : UPred M where
  holds n x := P.holds n x ∨ Q.holds n x
  mono hp hinc hle := hp.elim
    (Or.inl ∘ fun h => P.mono h hinc hle)
    (Or.inr ∘ fun h => Q.mono h hinc hle)

/-- Ordinary intuitionistic implication over all smaller indices and resource
extensions. This is distinct from separating implication. -/
def imp (P Q : UPred M) : UPred M where
  holds n x := ∀ m, m ≤ n → ∀ y (hy : CMRA.validN m y),
    CMRA.IncludedN m x.val y → P.holdsAt m y hy → Q.holdsAt m y hy
  mono := by
    intro n₁ n₂ x₁ x₂ himp hinc hle
    intro m hmn y hy hx₂y hp
    exact himp m (Nat.le_trans hmn hle) y hy
      (includedN_trans (includedN_mono hmn hinc) hx₂y) hp

def all {ι : Sort v} (P : ι → UPred M) : UPred M where
  holds n x := ∀ i, (P i).holds n x
  mono hp hinc hle i := (P i).mono (hp i) hinc hle

def exist {ι : Sort v} (P : ι → UPred M) : UPred M where
  holds n x := ∃ i, (P i).holds n x
  mono hp hinc hle := by
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, (P i).mono hi hinc hle⟩

theorem and_intro {P Q R : UPred M} (hP : R ⊢ᵤ P) (hQ : R ⊢ᵤ Q) :
    R ⊢ᵤ and P Q := by
  intro n x hx hr
  exact ⟨hP n x hx hr, hQ n x hx hr⟩

theorem or_intro_left (P Q : UPred M) : P ⊢ᵤ or P Q := by
  intro n x hx hp
  exact Or.inl hp

theorem or_intro_right (P Q : UPred M) : Q ⊢ᵤ or P Q := by
  intro n x hx hq
  exact Or.inr hq

theorem or_elim {P Q R : UPred M} (hP : P ⊢ᵤ R) (hQ : Q ⊢ᵤ R) :
    or P Q ⊢ᵤ R := by
  intro n x hx h
  exact h.elim (hP n x hx) (hQ n x hx)

theorem imp_intro {P Q R : UPred M} (h : and R P ⊢ᵤ Q) :
    R ⊢ᵤ imp P Q := by
  intro n x hx hr m hmn y hy hxy hp
  exact h m y hy ⟨R.mono hr hxy hmn, hp⟩

theorem imp_elim (P Q : UPred M) : and P (imp P Q) ⊢ᵤ Q := by
  intro n x hx h
  exact h.2 n (Nat.le_refl n) x hx (includedN_refl n x) h.1

theorem all_intro {ι : Sort v} {P : ι → UPred M} {Q : UPred M}
    (h : ∀ i, Q ⊢ᵤ P i) : Q ⊢ᵤ all P := by
  intro n x hx hq i
  exact h i n x hx hq

theorem all_elim {ι : Sort v} (P : ι → UPred M) (i : ι) : all P ⊢ᵤ P i := by
  intro n x hx h
  exact h i

theorem exist_intro {ι : Sort v} (P : ι → UPred M) (i : ι) :
    P i ⊢ᵤ exist P := by
  intro n x hx h
  exact ⟨i, h⟩

theorem exist_elim {ι : Sort v} {P : ι → UPred M} {Q : UPred M}
    (h : ∀ i, P i ⊢ᵤ Q) : exist P ⊢ᵤ Q := by
  intro n x hx hp
  obtain ⟨i, hi⟩ := hp
  exact h i n x hx hi

def emp : UPred M := own UCMRA.unit

/-- Separating implication, restricted to valid resource extensions at every
smaller observation depth. -/
def wand (P Q : UPred M) : UPred M where
  holds n x := ∀ m, m ≤ n → ∀ y (hy : CMRA.validN m y)
    (hxy : CMRA.validN m (CMRA.op x.val y)),
      P.holdsAt m y hy → Q.holdsAt m (CMRA.op x.val y) hxy
  mono := by
    intro n₁ n₂ x₁ x₂ hw hinc hle
    intro m hmn₂ y hy hx₂y hp
    obtain ⟨f, hx₂⟩ := includedN_mono hmn₂ hinc
    have hx₂yEq : CMRA.op x₂.val y ≡{m}≡ CMRA.op (CMRA.op x₁.val y) f := by
      exact OFE.trans (CMRA.op_ne_left y m hx₂) <| OFE.trans
        (OFE.of_eq (CMRA.op_assoc x₁.val f y).symm) <| OFE.trans
          (CMRA.op_ne_right x₁.val m (OFE.of_eq (CMRA.op_comm f y))) <|
            OFE.of_eq (CMRA.op_assoc x₁.val y f)
    have hcombined : CMRA.validN m (CMRA.op (CMRA.op x₁.val y) f) :=
      CMRA.validN_ne hx₂yEq hx₂y
    have hx₁y : CMRA.validN m (CMRA.op x₁.val y) :=
      CMRA.validN_op_left hcombined
    have hq := hw m (Nat.le_trans hmn₂ hle) y hy hx₁y hp
    exact Q.mono hq ⟨f, hx₂yEq⟩ (Nat.le_refl m)

/-- Iris-style basic update. At every smaller step and against every compatible
frame, an updated resource can be chosen that preserves that frame. -/
def basicUpdate (P : UPred M) : UPred M where
  holds n x := ∀ m, m ≤ n → ∀ frame,
    CMRA.validN m (CMRA.op x.val frame) →
    ∃ y, CMRA.validN m (CMRA.op y frame) ∧
      ∃ hy : CMRA.validN m y, P.holdsAt m y hy
  mono := by
    intro n₁ n₂ x₁ x₂ hup hinc hle
    intro m hmn₂ frame hx₂frame
    obtain ⟨f, hx₂⟩ := includedN_mono hmn₂ hinc
    have hx₂frameEq : CMRA.op x₂.val frame ≡{m}≡
        CMRA.op x₁.val (CMRA.op f frame) :=
      OFE.trans (CMRA.op_ne_left frame m hx₂)
        (OFE.of_eq (CMRA.op_assoc x₁.val f frame).symm)
    have hx₁frame : CMRA.validN m (CMRA.op x₁.val (CMRA.op f frame)) :=
      CMRA.validN_ne hx₂frameEq hx₂frame
    obtain ⟨y, hyv, hy, hp⟩ :=
      hup m (Nat.le_trans hmn₂ hle) (CMRA.op f frame) hx₁frame
    refine ⟨CMRA.op y f, ?_, ?_⟩
    · exact CMRA.validN_ne (OFE.of_eq (CMRA.op_assoc y f frame)) hyv
    · have hyv' : CMRA.validN m (CMRA.op (CMRA.op y f) frame) := by
        rw [← CMRA.op_assoc]
        exact hyv
      have hyf : CMRA.validN m (CMRA.op y f) := CMRA.validN_op_left hyv'
      exact ⟨hyf, P.mono hp ⟨f, OFE.refl m (CMRA.op y f)⟩ (Nat.le_refl m)⟩

theorem and_left (P Q : UPred M) : and P Q ⊢ᵤ P := by
  intro n x hx hp; exact hp.1

theorem and_right (P Q : UPred M) : and P Q ⊢ᵤ Q := by
  intro n x hx hp; exact hp.2

theorem sep_comm_equiv (P Q : UPred M) :
    sep P Q ⊢ᵤ sep Q P ∧ sep Q P ⊢ᵤ sep P Q :=
  ⟨sep_comm P Q, sep_comm Q P⟩

theorem sep_assoc_forward (P Q R : UPred M) :
    sep (sep P Q) R ⊢ᵤ sep P (sep Q R) := by
  intro n x hx h
  obtain ⟨ab, c, habc, habv, hc, hpq, hr⟩ := h
  obtain ⟨a, b, hab, ha, hb, hp, hq⟩ := hpq
  have hxsplit : x ≡{n}≡ CMRA.op a (CMRA.op b c) :=
    OFE.trans habc <| OFE.trans (CMRA.op_ne_left c n hab) <|
      OFE.of_eq (CMRA.op_assoc a b c).symm
  have hvsplit : CMRA.validN n (CMRA.op a (CMRA.op b c)) :=
    CMRA.validN_ne hxsplit hx
  have hvbc : CMRA.validN n (CMRA.op b c) := by
    apply CMRA.validN_op_left (x := CMRA.op b c) (y := a)
    simpa [CMRA.op_comm] using hvsplit
  exact ⟨a, CMRA.op b c, hxsplit, ha, hvbc, hp,
    ⟨b, c, OFE.refl n _, hb, hc, hq, hr⟩⟩

theorem sep_assoc_backward (P Q R : UPred M) :
    sep P (sep Q R) ⊢ᵤ sep (sep P Q) R := by
  intro n x hx h
  obtain ⟨a, bc, habc, ha, hbcv, hp, hqr⟩ := h
  obtain ⟨b, c, hbc, hb, hc, hq, hr⟩ := hqr
  have hxsplit : x ≡{n}≡ CMRA.op (CMRA.op a b) c :=
    OFE.trans habc <| OFE.trans (CMRA.op_ne_right a n hbc) <|
      OFE.of_eq (CMRA.op_assoc a b c)
  have hvsplit : CMRA.validN n (CMRA.op (CMRA.op a b) c) :=
    CMRA.validN_ne hxsplit hx
  have hvab : CMRA.validN n (CMRA.op a b) := CMRA.validN_op_left hvsplit
  exact ⟨CMRA.op a b, c, hxsplit, hvab, hc,
    ⟨a, b, OFE.refl n _, ha, hb, hp, hq⟩, hr⟩

theorem sep_assoc (P Q R : UPred M) :
    sep (sep P Q) R ⊢ᵤ sep P (sep Q R) ∧
    sep P (sep Q R) ⊢ᵤ sep (sep P Q) R :=
  ⟨sep_assoc_forward P Q R, sep_assoc_backward P Q R⟩

theorem sep_emp_right_forward (P : UPred M) : sep P emp ⊢ᵤ P := by
  intro n x hx h
  obtain ⟨a, b, hab, ha, hb, hp, hemp⟩ := h
  exact P.mono hp ⟨b, hab⟩ (Nat.le_refl n)

theorem sep_emp_right_backward (P : UPred M) : P ⊢ᵤ sep P emp := by
  intro n x hx hp
  have hu : CMRA.validN n (UCMRA.unit : M) := CMRA.validN_of_valid UCMRA.unit_valid n
  exact ⟨x, UCMRA.unit, OFE.of_eq (UCMRA.unit_right x).symm, hx, hu, hp,
    includedN_refl n UCMRA.unit⟩

theorem sep_emp_right (P : UPred M) :
    sep P emp ⊢ᵤ P ∧ P ⊢ᵤ sep P emp :=
  ⟨sep_emp_right_forward P, sep_emp_right_backward P⟩

theorem wand_intro {P Q R : UPred M} (h : sep R P ⊢ᵤ Q) : R ⊢ᵤ wand P Q := by
  intro n x hx hr m hmn y hy hxy hp
  apply h m (CMRA.op x y) hxy
  exact ⟨x, y, OFE.refl m _, CMRA.validN_mono hmn hx, hy,
    R.mono hr (includedN_refl m x) hmn, hp⟩

theorem wand_elim (P Q : UPred M) : sep P (wand P Q) ⊢ᵤ Q := by
  intro n x hx hpw
  obtain ⟨a, b, hab, ha, hb, hp, hw⟩ := hpw
  have hvalidBA : CMRA.validN n (CMRA.op b a) := by
    apply CMRA.validN_ne (OFE.trans hab (OFE.of_eq (CMRA.op_comm a b)))
    exact hx
  have hq := hw n (Nat.le_refl n) a ha hvalidBA hp
  apply Q.mono hq
  · exact ⟨UCMRA.unit, OFE.trans (OFE.trans hab (OFE.of_eq (CMRA.op_comm a b)))
      (OFE.symm (OFE.of_eq (UCMRA.unit_right (CMRA.op b a))))⟩
  · exact Nat.le_refl n

theorem basicUpdate_intro (P : UPred M) : P ⊢ᵤ basicUpdate P := by
  intro n x hx hp m hmn frame hvalid
  have hxm : CMRA.validN m x := CMRA.validN_mono hmn hx
  exact ⟨x, hvalid, hxm, P.mono hp (includedN_refl m x) hmn⟩

theorem basicUpdate_mono {P Q : UPred M} (hpq : P ⊢ᵤ Q) :
    basicUpdate P ⊢ᵤ basicUpdate Q := by
  intro n x hx hup m hmn frame hvalid
  obtain ⟨y, hyframe, hy, hp⟩ := hup m hmn frame hvalid
  exact ⟨y, hyframe, hy, hpq m y hy hp⟩


end LeanIrisX.UPred
