import LeanIrisX.Algebra.AgreementRaw
import LeanIrisX.Algebra.CMRA

namespace LeanIrisX

def Agreement (α : Type u) : Type u := Quotient (Agreement.Raw.instSetoid (α := α))

namespace Agreement

variable {α : Type u}

def mk (x : Raw α) : Agreement α := Quotient.mk _ x

def lift {γ : Sort w} (f : Raw α → γ)
    (resp : ∀ x y, Raw.SameElems x y → f x = f y) : Agreement α → γ :=
  Quotient.lift f resp

def lift₂ {γ : Sort w} (f : Raw α → Raw α → γ)
    (resp : ∀ a b c d, Raw.SameElems a c → Raw.SameElems b d → f a b = f c d) :
    Agreement α → Agreement α → γ := Quotient.lift₂ f resp

def op : Agreement α → Agreement α → Agreement α :=
  lift₂ (fun x y => mk (Raw.op x y))
    (fun _ _ _ _ hac hbd => Quotient.sound (Raw.op_sameElems hac hbd))

def toAgreement (a : α) : Agreement α := mk (Raw.singleton a)

variable [OFE α]

def dist (n : Nat) : Agreement α → Agreement α → Prop :=
  lift₂ (Raw.Dist n)
    (fun _ _ _ _ hac hbd => propext (Raw.dist_congr hac hbd))

private theorem exists_forall_dist {a : α} {l : List α}
    (h : ∀ n, ∃ b ∈ l, a ≡{n}≡ b) :
    ∃ b ∈ l, ∀ n, a ≡{n}≡ b := by
  induction l with
  | nil => simpa using h 0
  | cons c l ih =>
    by_cases hc : ∀ n, a ≡{n}≡ c
    · exact ⟨c, by simp, hc⟩
    · obtain ⟨n₀, hn₀⟩ := Classical.not_forall.mp hc
      have hl : ∀ n, ∃ b ∈ l, a ≡{n}≡ b := by
        intro n
        obtain ⟨b, hb, hd⟩ := h (max n n₀)
        rcases List.mem_cons.mp hb with rfl | hb
        · exact False.elim (hn₀ (OFE.mono (Nat.le_max_right n n₀) hd))
        · exact ⟨b, hb, OFE.mono (Nat.le_max_left n n₀) hd⟩
      obtain ⟨b, hb, hd⟩ := ih hl
      exact ⟨b, by simp [hb], hd⟩

private theorem sameElems_of_all_dist {x y : Raw α}
    (h : ∀ n, Raw.Dist n x y) : Raw.SameElems x y := by
  have key {x y : Raw α} (h : ∀ n, Raw.Dist n x y) :
      ∀ a ∈ x.values, a ∈ y.values := by
    intro a ha
    obtain ⟨b, hb, hd⟩ := exists_forall_dist (fun n => (h n).1 a ha)
    have : a = b := OFE.eq_of_dist hd
    simpa [this] using hb
  exact ⟨key h, key (fun n => Raw.dist_symm (h n))⟩

instance : OFE (Agreement α) where
  dist := dist
  dist_equivalence n := by
    constructor
    · intro x
      induction x using Quotient.ind with | _ a => exact Raw.dist_refl n a
    · intro x y h
      induction x, y using Quotient.ind₂ with | _ a b => exact Raw.dist_symm h
    · intro x y z hxy hyz
      induction x, y using Quotient.ind₂ with
      | _ a b =>
        induction z using Quotient.ind with
        | _ c => exact Raw.dist_trans hxy hyz
  eq_dist x y := by
    induction x, y using Quotient.ind₂ with
    | _ a b =>
      constructor
      · intro h n
        have he : Raw.SameElems a b := Quotient.exact h
        exact (Raw.dist_congr (Raw.sameElems_equivalence.refl a) he).mp
          (Raw.dist_refl n a)
      · intro h
        exact Quotient.sound (sameElems_of_all_dist h)
  dist_mono := by
    intro n m x y hmn h
    induction x, y using Quotient.ind₂ with
    | _ a b => exact Raw.dist_mono hmn h

def validN (n : Nat) : Agreement α → Prop :=
  lift (Raw.ValidN n) (fun _ _ h => propext (Raw.validN_congr h))

def valid (x : Agreement α) : Prop := ∀ n, validN n x

theorem op_comm (x y : Agreement α) : op x y = op y x := by
  apply OFE.eq_of_dist
  intro n
  induction x, y using Quotient.ind₂ with
  | _ a b => exact Raw.op_comm_dist n a b

theorem op_assoc (x y z : Agreement α) : op x (op y z) = op (op x y) z := by
  apply OFE.eq_of_dist
  intro n
  induction x, y using Quotient.ind₂ with
  | _ a b =>
    induction z using Quotient.ind with
    | _ c => exact Raw.op_assoc_dist n a b c

theorem op_idem (x : Agreement α) : op x x = x := by
  apply OFE.eq_of_dist
  intro n
  induction x using Quotient.ind with
  | _ a => exact Raw.op_idem_dist n a

theorem validN_ne {n : Nat} {x y : Agreement α}
    (hxy : x ≡{n}≡ y) (hx : validN n x) : validN n y := by
  induction x, y using Quotient.ind₂ with
  | _ a b =>
    change Raw.Dist n a b at hxy
    change Raw.ValidN n a at hx
    exact Raw.validN_ne hxy hx

theorem validN_succ {n : Nat} {x : Agreement α}
    (h : validN (n + 1) x) : validN n x := by
  induction x using Quotient.ind with
  | _ a => exact Raw.validN_succ h

theorem validN_op_left {n : Nat} {x y : Agreement α}
    (h : validN n (op x y)) : validN n x := by
  induction x, y using Quotient.ind₂ with
  | _ a b => exact Raw.op_validN_left h

theorem op_ne (x : Agreement α) : NonExpansive (op x) := by
  intro n y₁ y₂ h
  induction x using Quotient.ind with
  | _ a =>
    induction y₁, y₂ using Quotient.ind₂ with
    | _ b c => exact Raw.op_ne h

theorem op_invN {n : Nat} {x y : Agreement α}
    (h : validN n (op x y)) : x ≡{n}≡ y := by
  induction x, y using Quotient.ind₂ with
  | _ a b => exact Raw.op_validN_implies_dist h

instance : CMRA (Agreement α) where
  pcore x := some x
  op := op
  validN := validN
  valid := valid
  op_ne := op_ne
  pcore_ne := by
    intro n x y cx hxy hcore
    have hcx : cx = x := Option.some.inj hcore.symm
    subst cx
    exact ⟨y, rfl, hxy⟩
  pcore_none_ne := by intro n x y hxy hnone; contradiction
  validN_ne := validN_ne
  valid_iff_validN := Iff.rfl
  validN_succ := validN_succ
  validN_op_left := validN_op_left
  assoc := op_assoc
  comm := op_comm
  pcore_op_left := by
    intro x cx h
    have : cx = x := Option.some.inj h.symm
    subst cx
    exact op_idem x
  pcore_idem := by
    intro x cx h
    have : cx = x := Option.some.inj h.symm
    subst cx
    rfl
  pcore_op_mono := by
    intro x cx h y
    have : cx = x := Option.some.inj h.symm
    subst cx
    exact ⟨y, rfl⟩
  extend := by
    intro n x y₁ y₂ hvalid heq
    have hopenValid : validN n (op y₁ y₂) := validN_ne heq hvalid
    have hy : y₁ ≡{n}≡ y₂ := op_invN hopenValid
    have hopenLeft : op y₁ y₂ ≡{n}≡ y₁ :=
      OFE.trans (op_ne y₁ n (OFE.symm hy)) (OFE.of_eq (op_idem y₁))
    exact {
      left := x
      right := x
      decompose := (op_idem x).symm
      left_dist := OFE.trans heq hopenLeft
      right_dist := OFE.trans (OFE.trans heq hopenLeft) hy
    }

theorem toAgreement_validN (n : Nat) (a : α) :
    CMRA.validN n (toAgreement a) := Raw.singleton_validN n a

theorem toAgreement_dist_iff {n : Nat} {a b : α} :
    toAgreement a ≡{n}≡ toAgreement b ↔ a ≡{n}≡ b := by
  change Raw.Dist n (Raw.singleton a) (Raw.singleton b) ↔ a ≡{n}≡ b
  exact Raw.singleton_dist_iff

theorem toAgreement_op_valid_iff {n : Nat} {a b : α} :
    CMRA.validN n (CMRA.op (toAgreement a) (toAgreement b)) ↔ a ≡{n}≡ b := by
  constructor
  · intro h
    exact Raw.singleton_dist_iff.mp (op_invN h)
  · intro hab
    change Raw.ValidN n (Raw.op (Raw.singleton a) (Raw.singleton b))
    intro x hx y hy
    simp [Raw.op, Raw.singleton] at hx hy
    rcases hx with (rfl | rfl) <;> rcases hy with (rfl | rfl)
    · exact OFE.refl n _
    · exact hab
    · exact OFE.symm hab
    · exact OFE.refl n _

end Agreement
end LeanIrisX
