import Lean
import LeanIrisX.Algebra.CMRA

/-!
Iris discardable fractional permissions. This follows the three-constructor
model used by Iris: owned, discarded knowledge, and owned-plus-discarded.
-/

namespace LeanIrisX

structure PosRat where
  val : Rat
  positive : 0 < val
deriving DecidableEq, Repr

namespace PosRat

theorem ext {p q : PosRat} (h : p.val = q.val) : p = q := by
  cases p; cases q; cases h; rfl

private theorem add_positive (p q : PosRat) : 0 < p.val + q.val := by
  apply Rat.not_le.mp
  intro hsum
  have hp_le_sum : p.val ≤ p.val + q.val := by
    simpa [Rat.add_zero] using
      (Rat.add_le_add_left (a := 0) (b := q.val) (c := p.val)).2
        (Rat.le_of_lt q.positive)
  exact (Rat.not_le.mpr p.positive) (Rat.le_trans hp_le_sum hsum)

instance : Add PosRat where add p q := ⟨p.val + q.val, add_positive p q⟩

@[simp] theorem add_val (p q : PosRat) : (p + q).val = p.val + q.val := rfl

theorem left_le_add (p q : PosRat) : p.val ≤ p.val + q.val := by
  simpa [Rat.add_zero] using
    (Rat.add_le_add_left (a := 0) (b := q.val) (c := p.val)).2
      (Rat.le_of_lt q.positive)

theorem left_lt_add (p q : PosRat) : p.val < p.val + q.val := by
  simpa [Rat.add_zero] using
      (Rat.add_lt_add_left (a := 0) (b := q.val) (c := p.val)).2 q.positive

theorem add_assoc (p q r : PosRat) : p + (q + r) = (p + q) + r := by
  apply ext
  exact (Rat.add_assoc p.val q.val r.val).symm

theorem add_comm (p q : PosRat) : p + q = q + p := by
  apply ext
  exact Rat.add_comm p.val q.val

theorem lt_of_lt_of_le {a b c : Rat} (hab : a < b) (hbc : b ≤ c) : a < c := by
  apply Rat.not_le.mp
  intro hca
  exact (Rat.not_le.mpr hab) (Rat.le_trans hbc hca)

end PosRat

inductive DFrac where
  | own (q : PosRat)
  | discard
  | ownDiscard (q : PosRat)
deriving DecidableEq, Repr

namespace DFrac

instance : OFE DFrac := OFE.ofDiscrete DFrac
instance : OFE.Discrete DFrac where eq_of_dist h := h

def op : DFrac → DFrac → DFrac
  | discard, discard => discard
  | own p, discard | discard, own p => ownDiscard p
  | ownDiscard p, discard | discard, ownDiscard p => ownDiscard p
  | own p, own q => own (p + q)
  | own p, ownDiscard q | ownDiscard p, own q | ownDiscard p, ownDiscard q =>
      ownDiscard (p + q)

def Valid : DFrac → Prop
  | own q => q.val ≤ 1
  | discard => True
  | ownDiscard q => q.val < 1

def pcore : DFrac → Option DFrac
  | own _ => none
  | discard | ownDiscard _ => some discard

theorem op_assoc (x y z : DFrac) : op x (op y z) = op (op x y) z := by
  cases x <;> cases y <;> cases z <;> simp [op, PosRat.add_assoc]

theorem op_comm (x y : DFrac) : op x y = op y x := by
  cases x <;> cases y <;> simp [op, PosRat.add_comm]

instance instCMRA : CMRA DFrac where
  pcore := pcore
  op := op
  validN _ x := Valid x
  valid := Valid
  op_ne _ := by intro n x y h; subst y; exact OFE.refl n _
  pcore_ne := by
    intro n x y cx hxy hx
    subst y
    exact ⟨cx, hx, OFE.refl n cx⟩
  pcore_none_ne := by
    intro n x y hxy hx
    subst y
    exact hx
  validN_ne := by intro n x y hxy hx; subst y; exact hx
  valid_iff_validN := by simp
  validN_succ := by simp
  validN_op_left := by
    intro n x y h
    cases x with
    | discard => trivial
    | own p =>
      cases y with
      | discard => exact Rat.le_of_lt h
      | own q => exact Rat.le_trans (PosRat.left_le_add p q) h
      | ownDiscard q =>
        exact Rat.le_of_lt (PosRat.lt_of_lt_of_le (PosRat.left_lt_add p q) (Rat.le_of_lt h))
    | ownDiscard p =>
      cases y with
      | discard => exact h
      | own q => exact PosRat.lt_of_lt_of_le (PosRat.left_lt_add p q) (Rat.le_of_lt h)
      | ownDiscard q => exact PosRat.lt_of_lt_of_le (PosRat.left_lt_add p q) (Rat.le_of_lt h)
  assoc := op_assoc
  comm := op_comm
  pcore_op_left := by
    intro x cx h
    cases x <;> simp [pcore] at h ⊢ <;> subst cx <;> rfl
  pcore_idem := by
    intro x cx h
    cases x <;> simp [pcore] at h ⊢ <;> subst cx <;> rfl
  pcore_op_mono := by
    intro x cx hx y
    cases x with
    | own p => simp [pcore] at hx
    | discard =>
      simp [pcore] at hx
      subst cx
      exact ⟨discard, by cases y <;> rfl⟩
    | ownDiscard p =>
      simp [pcore] at hx
      subst cx
      exact ⟨discard, by cases y <;> rfl⟩
  extend := by
    intro n x y₁ y₂ hx hdist
    have heq : x = op y₁ y₂ := hdist
    exact {
      left := y₁
      right := y₂
      decompose := heq
      left_dist := OFE.refl n y₁
      right_dist := OFE.refl n y₂
    }

def half : PosRat := ⟨mkRat 1 2, by simp [Rat.lt_iff, Rat.num_mkRat]⟩
def one : PosRat := ⟨1, by simp [Rat.lt_iff]⟩

theorem half_add_half : half.val + half.val = (1 : Rat) := by
  change mkRat 1 2 + mkRat 1 2 = (1 : Rat)
  rw [Rat.mkRat_add_mkRat 1 1 (by decide) (by decide)]
  change mkRat 4 4 = mkRat 1 1
  exact (Rat.mkRat_eq_iff (by decide) (by decide)).2 (by decide)

theorem halves_valid : CMRA.valid (CMRA.op (own half) (own half)) := by
  change half.val + half.val ≤ 1
  rw [half_add_half]
  exact Rat.le_refl

theorem one_valid : CMRA.valid (own one) := by
  change (1 : Rat) ≤ 1
  exact Rat.le_refl

theorem full_plus_half_invalid :
    ¬ CMRA.valid (CMRA.op (own one) (own half)) := by
  change ¬ (one.val + half.val ≤ 1)
  change ¬ ((1 : Rat) + mkRat 1 2 ≤ 1)
  apply Rat.not_le.mpr
  simpa [Rat.add_zero] using
    (Rat.add_lt_add_left (a := 0) (b := mkRat 1 2) (c := 1)).2 half.positive

theorem discard_valid : CMRA.valid discard := trivial
theorem discard_idempotent : CMRA.op discard discard = discard := rfl
theorem own_op_discard (q : PosRat) : CMRA.op (own q) discard = ownDiscard q := rfl

theorem full_op_invalid (dq : DFrac) :
    ¬ CMRA.valid (CMRA.op (own one) dq) := by
  cases dq with
  | discard =>
    change ¬ ((1 : Rat) < 1)
    exact Rat.lt_irrefl
  | own q =>
    change ¬ ((1 : Rat) + q.val ≤ 1)
    apply Rat.not_le.mpr
    simpa [Rat.add_zero] using
      (Rat.add_lt_add_left (a := 0) (b := q.val) (c := 1)).2 q.positive
  | ownDiscard q =>
    change ¬ ((1 : Rat) + q.val < 1)
    intro h
    have hgt : (1 : Rat) < 1 + q.val := by
      simpa [Rat.add_zero] using
        (Rat.add_lt_add_left (a := 0) (b := q.val) (c := 1)).2 q.positive
    exact (Rat.not_le.mpr hgt) (Rat.le_of_lt h)

theorem full_op_invalidN (n : Nat) (dq : DFrac) :
    ¬ CMRA.validN n (CMRA.op (own one) dq) :=
  full_op_invalid dq

end DFrac
end LeanIrisX
