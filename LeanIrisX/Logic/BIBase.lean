/-! Abstract public interface for bunched implications. -/

namespace LeanIrisX

class BIBase (PROP : Type u) where
  Entails : PROP → PROP → Prop
  emp : PROP
  pure : Prop → PROP
  and : PROP → PROP → PROP
  or : PROP → PROP → PROP
  imp : PROP → PROP → PROP
  sep : PROP → PROP → PROP
  wand : PROP → PROP → PROP
  later : PROP → PROP
  persistently : PROP → PROP
  plainly : PROP → PROP
  basicUpdate : PROP → PROP

class BIQuantifiers (PROP : Type u) where
  all : {α : Sort v} → (α → PROP) → PROP
  exist : {α : Sort v} → (α → PROP) → PROP

namespace BI

variable {PROP : Type u} [BIBase PROP]

infix:45 " ⊢ " => BIBase.Entails
infixr:52 " ∗ " => BIBase.sep
infixr:51 " -∗ " => BIBase.wand
infixr:54 " ∧ᵢ " => BIBase.and
infixr:53 " ∨ᵢ " => BIBase.or
infixr:50 " →ᵢ " => BIBase.imp
prefix:60 "▷ " => BIBase.later
prefix:60 "□ " => BIBase.persistently
prefix:60 "■ " => BIBase.plainly
prefix:60 "|==> " => BIBase.basicUpdate

def biEmp : PROP := BIBase.emp
def biPure (φ : Prop) : PROP := BIBase.pure φ

def biAll [BIQuantifiers PROP] {α : Sort v} (P : α → PROP) : PROP :=
  BIQuantifiers.all P

def biExist [BIQuantifiers PROP] {α : Sort v} (P : α → PROP) : PROP :=
  BIQuantifiers.exist P

class Laws (PROP : Type u) [BIBase PROP] : Prop where
  entails_refl : ∀ P : PROP, P ⊢ P
  entails_trans : ∀ {P Q R : PROP}, P ⊢ Q → Q ⊢ R → P ⊢ R
  sep_comm : ∀ P Q : PROP, P ∗ Q ⊢ Q ∗ P
  sep_assoc : ∀ P Q R : PROP, (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)
  sep_emp_left : ∀ P : PROP, BIBase.emp ∗ P ⊢ P
  sep_emp_right : ∀ P : PROP, P ∗ BIBase.emp ⊢ P
  wand_intro : ∀ {P Q R : PROP}, R ∗ P ⊢ Q → R ⊢ P -∗ Q
  wand_elim : ∀ P Q : PROP, P ∗ (P -∗ Q) ⊢ Q
  later_intro : ∀ P : PROP, P ⊢ ▷ P
  persistently_elim : ∀ P : PROP, □ P ⊢ P
  persistently_dup : ∀ P : PROP, □ P ⊢ □ P ∗ □ P
  bupd_intro : ∀ P : PROP, P ⊢ |==> P
  bupd_trans : ∀ P : PROP, |==> (|==> P) ⊢ |==> P

end BI
end LeanIrisX
