import LeanIrisX.Algebra.ViewRel
import LeanIrisX.Algebra.DFrac
import LeanIrisX.Algebra.Option
import LeanIrisX.Algebra.Product

/-!
The public View carrier and its semantic operations. This release deliberately
stops before claiming a CMRA instance: the carrier, OFE, operation and validity
are aligned first, so the later CMRA proof cannot hide a simplified model.
-/

namespace LeanIrisX

structure View {A B : Type _} (R : ViewRel A B) where
  auth : Option (DFrac × Agreement A)
  frag : B

namespace View

variable {A : Type u} {B : Type v}
variable [OFE A] [OFE B] [CMRA B] [UCMRA B]
variable {R : ViewRel A B} [IsViewRel R]

def Auth (dq : DFrac) (a : A) : View R :=
  ⟨some (dq, Agreement.toAgreement a), UCMRA.unit⟩

def Frag (b : B) : View R := ⟨none, b⟩

def Dist (n : Nat) (x y : View R) : Prop :=
  x.auth ≡{n}≡ y.auth ∧ x.frag ≡{n}≡ y.frag

instance instOFE : OFE (View R) where
  dist := Dist
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
      cases x with
      | mk xa xf =>
        cases y with
        | mk ya yf =>
          simp only [View.mk.injEq]
          exact ⟨OFE.eq_of_dist (fun n => (h n).1),
            OFE.eq_of_dist (fun n => (h n).2)⟩
  dist_mono hnm h := ⟨OFE.mono hnm h.1, OFE.mono hnm h.2⟩

def ValidN (n : Nat) (v : View R) : Prop :=
  match v.auth with
  | some (dq, ag) =>
      CMRA.validN n dq ∧ ∃ a, ag ≡{n}≡ Agreement.toAgreement a ∧ R n a v.frag
  | none => ∃ a, R n a v.frag

def Valid (v : View R) : Prop := ∀ n, ValidN n v

def op (x y : View R) : View R :=
  ⟨CMRA.op x.auth y.auth, CMRA.op x.frag y.frag⟩

def unit : View R := ⟨none, UCMRA.unit⟩

omit [UCMRA B] [IsViewRel R] in
theorem op_comm (x y : View R) : op x y = op y x := by
  cases x; cases y
  simp [op, CMRA.comm]

omit [UCMRA B] [IsViewRel R] in
theorem op_assoc (x y z : View R) : op x (op y z) = op (op x y) z := by
  cases x; cases y; cases z
  simp [op, CMRA.assoc]

omit [IsViewRel R] in
theorem unit_left (x : View R) : op unit x = x := by
  cases x with
  | mk xa xf =>
    cases xa with
    | none =>
      change View.mk (OptionCMRA.op none none) (CMRA.op UCMRA.unit xf) =
        View.mk none xf
      rw [UCMRA.unit_left]
      rfl
    | some a =>
      change View.mk (OptionCMRA.op none (some a)) (CMRA.op UCMRA.unit xf) =
        View.mk (some a) xf
      rw [UCMRA.unit_left]
      rfl

theorem auth_frag_validN_iff (n : Nat) (dq : DFrac) (a : A) (b : B) :
    ValidN n (op (Auth (R := R) dq a) (Frag (R := R) b)) ↔
      CMRA.validN n dq ∧ R n a b := by
  simp only [op, Auth, Frag, ValidN, UCMRA.unit_left]
  constructor
  · rintro ⟨hdq, a', hag, hr⟩
    have haa' : a ≡{n}≡ a' := Agreement.toAgreement_dist_iff.mp hag
    exact ⟨hdq, IsViewRel.mono hr (OFE.symm haa')
      (CMRA.includedN_of_dist (OFE.refl n b)) (Nat.le_refl n)⟩
  · rintro ⟨hdq, hr⟩
    exact ⟨hdq, a, OFE.refl n _, hr⟩

theorem auth_one_frag_validN_iff (n : Nat) (a : A) (b : B) :
    ValidN n (op (Auth (R := R) (DFrac.own DFrac.one) a) (Frag (R := R) b)) ↔
      R n a b := by
  rw [auth_frag_validN_iff]
  exact and_iff_right (CMRA.validN_of_valid DFrac.one_valid n)

omit [UCMRA B] in
private theorem frag_included_op_left (n : Nat) (b₁ b₂ : B) :
    CMRA.IncludedN n b₁ (CMRA.op b₁ b₂) :=
  ⟨b₂, OFE.refl n _⟩

def Pcore (v : View R) : Option (View R) :=
  some ⟨CMRA.core v.auth, CMRA.core v.frag⟩

instance instCMRA : CMRA (View R) where
  pcore := Pcore
  op := op
  validN := ValidN
  valid := Valid
  op_ne x := by
    intro n y₁ y₂ hy
    exact ⟨CMRA.op_ne x.auth n hy.1, CMRA.op_ne x.frag n hy.2⟩
  pcore_ne := by
    intro n x y cx hxy hx
    simp [Pcore] at hx
    subst cx
    exact ⟨⟨CMRA.core y.auth, CMRA.core y.frag⟩, rfl,
      ⟨CMRA.core_ne hxy.1, CMRA.core_ne hxy.2⟩⟩
  pcore_none_ne := by intro n x y hxy hnone; simp [Pcore] at hnone
  validN_ne := by
    intro n x y hxy hx
    cases x with
    | mk xa xf =>
      cases y with
      | mk ya yf =>
        change xa ≡{n}≡ ya ∧ xf ≡{n}≡ yf at hxy
        cases xa with
        | none =>
          cases ya with
          | none =>
            rcases hx with ⟨a, hr⟩
            exact ⟨a, (ViewRel.iff_of_dist (OFE.refl n a) hxy.2).mp hr⟩
          | some ya =>
            exact False.elim hxy.1
        | some xa =>
          cases ya with
          | none =>
            exact False.elim hxy.1
          | some ya =>
            rcases xa with ⟨dq₁, ag₁⟩
            rcases ya with ⟨dq₂, ag₂⟩
            rcases hx with ⟨hdq, a, hag, hr⟩
            exact ⟨CMRA.validN_ne hxy.1.1 hdq, a,
              OFE.trans (OFE.symm hxy.1.2) hag,
              (ViewRel.iff_of_dist (OFE.refl n a) hxy.2).mp hr⟩
  valid_iff_validN := Iff.rfl
  validN_succ := by
    intro n x hx
    cases x with
    | mk xa xf =>
      cases xa with
      | none =>
        rcases hx with ⟨a, hr⟩
        exact ⟨a, IsViewRel.mono hr (OFE.refl n a)
          (CMRA.includedN_of_dist (OFE.refl n xf)) (Nat.le_succ n)⟩
      | some xa =>
        rcases xa with ⟨dq, ag⟩
        rcases hx with ⟨hdq, a, hag, hr⟩
        exact ⟨CMRA.validN_succ hdq, a, OFE.mono (Nat.le_succ n) hag,
          IsViewRel.mono hr (OFE.refl n a)
            (CMRA.includedN_of_dist (OFE.refl n xf)) (Nat.le_succ n)⟩
  validN_op_left := by
    intro n x y h
    cases x with
    | mk xa xf =>
      cases y with
      | mk ya yf =>
        cases xa with
        | none =>
          cases ya with
          | none =>
            rcases h with ⟨a, hr⟩
            exact ⟨a, IsViewRel.mono hr (OFE.refl n a)
              (frag_included_op_left n xf yf) (Nat.le_refl n)⟩
          | some ya =>
            rcases ya with ⟨dq₂, ag₂⟩
            rcases h with ⟨hdq, a, hag, hr⟩
            exact ⟨a, IsViewRel.mono hr (OFE.refl n a)
              (frag_included_op_left n xf yf) (Nat.le_refl n)⟩
        | some xa =>
          rcases xa with ⟨dq₁, ag₁⟩
          cases ya with
          | none =>
            rcases h with ⟨hdq, a, hag, hr⟩
            exact ⟨hdq, a, hag, IsViewRel.mono hr (OFE.refl n a)
              (frag_included_op_left n xf yf) (Nat.le_refl n)⟩
          | some ya =>
            rcases ya with ⟨dq₂, ag₂⟩
            rcases h with ⟨hdq, a, hag, hr⟩
            have hagValid : CMRA.validN n (CMRA.op ag₁ ag₂) :=
              Agreement.validN_ne (OFE.symm hag) (Agreement.toAgreement_validN n a)
            have h₁₂ : ag₁ ≡{n}≡ ag₂ := Agreement.op_invN hagValid
            have hleft : ag₁ ≡{n}≡ CMRA.op ag₁ ag₂ :=
              OFE.trans (OFE.of_eq (Agreement.op_idem ag₁).symm)
                (Agreement.op_ne ag₁ n h₁₂)
            exact ⟨CMRA.validN_op_left hdq, a, OFE.trans hleft hag,
              IsViewRel.mono hr (OFE.refl n a)
                (frag_included_op_left n xf yf) (Nat.le_refl n)⟩
  assoc := op_assoc
  comm := op_comm
  pcore_op_left := by
    intro x cx hx
    simp [Pcore] at hx
    subst cx
    cases x
    simp [op, CMRA.core_op]
  pcore_idem := by
    intro x cx hx
    simp [Pcore] at hx
    subst cx
    cases x
    simp [Pcore, CMRA.core_idem]
  pcore_op_mono := by
    intro x cx hx y
    simp [Pcore] at hx
    subst cx
    obtain ⟨cya, ha⟩ := CMRA.pcore_op_mono (CMRA.pcore_core x.auth) y.auth
    obtain ⟨cyf, hf⟩ := CMRA.pcore_op_mono (CMRA.pcore_core x.frag) y.frag
    have ha' : CMRA.core (CMRA.op x.auth y.auth) =
        CMRA.op (CMRA.core x.auth) cya :=
      Option.some.inj ((CMRA.pcore_core _).symm.trans ha)
    have hf' : CMRA.core (CMRA.op x.frag y.frag) =
        CMRA.op (CMRA.core x.frag) cyf :=
      Option.some.inj ((CMRA.pcore_core _).symm.trans hf)
    exact ⟨⟨cya, cyf⟩, by
      simp only [Pcore, op, Option.some.injEq, View.mk.injEq]
      exact ⟨ha', hf'⟩⟩
  extend := by
    intro n x y₁ y₂ hx hdist
    cases x with
    | mk xa xf =>
      have hprod : CMRA.validN n (xa, xf) := by
        cases xa with
        | none =>
          rcases hx with ⟨a, hr⟩
          exact ⟨trivial, IsViewRel.rel_validN n a xf hr⟩
        | some da =>
          rcases da with ⟨dq, ag⟩
          rcases hx with ⟨hdq, a, hag, hr⟩
          exact ⟨⟨hdq, Agreement.validN_ne (OFE.symm hag)
            (Agreement.toAgreement_validN n a)⟩,
            IsViewRel.rel_validN n a xf hr⟩
      obtain e := CMRA.extend (x := (xa, xf))
        (y₁ := (y₁.auth, y₁.frag)) (y₂ := (y₂.auth, y₂.frag)) hprod hdist
      exact {
        left := ⟨e.left.1, e.left.2⟩
        right := ⟨e.right.1, e.right.2⟩
        decompose := by
          apply congrArg (fun p => (⟨p.1, p.2⟩ : View R)) e.decompose
        left_dist := e.left_dist
        right_dist := e.right_dist
      }

instance instUCMRA : UCMRA (View R) where
  unit := unit
  unit_valid := by
    intro n
    exact IsViewRel.rel_unit n
  unit_left := unit_left
  pcore_unit := by
    have ha : CMRA.core (none : Option (DFrac × Agreement A)) = none :=
      Option.some.inj ((CMRA.pcore_core none).symm.trans UCMRA.pcore_unit)
    have hf : CMRA.core (UCMRA.unit : B) = UCMRA.unit :=
      Option.some.inj ((CMRA.pcore_core UCMRA.unit).symm.trans UCMRA.pcore_unit)
    change some (⟨CMRA.core (none : Option (DFrac × Agreement A)),
      CMRA.core (UCMRA.unit : B)⟩ : View R) =
      some (⟨none, UCMRA.unit⟩ : View R)
    rw [ha, hf]

end View
end LeanIrisX
