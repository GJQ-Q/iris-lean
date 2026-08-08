import LeanIrisX

namespace LeanIrisX.Tests.SemanticCore

open LeanIrisX LeanIrisX.UPred

example : COFE (UPred Unit) := inferInstance
example : OFE (UPred Unit) := inferInstance

example : UPred.own (() : Unit) ⊢ᵤ UPred.own () :=
  UPred.entails_refl _

example (P : UPred Unit) : P ⊢ᵤ UPred.later P :=
  UPred.later_intro P

example (P Q : UPred Unit) : UPred.sep P Q ⊢ᵤ UPred.sep Q P :=
  UPred.sep_comm P Q

example (P Q R : UPred Unit) :
    UPred.sep (UPred.sep P Q) R ⊢ᵤ UPred.sep P (UPred.sep Q R) :=
  UPred.sep_assoc_forward P Q R

example (P : UPred Unit) : UPred.sep P UPred.emp ⊢ᵤ P :=
  UPred.sep_emp_right_forward P

example (P Q : UPred Unit) (h : P ⊢ᵤ Q) :
    UPred.basicUpdate P ⊢ᵤ UPred.basicUpdate Q :=
  UPred.basicUpdate_mono h

example (P : UPred Unit) : UPred.plainly P ⊢ᵤ P :=
  UPred.plainly_elim P

example (P : UPred Unit) :
    UPred.persistently P ⊢ᵤ UPred.sep (UPred.persistently P) (UPred.persistently P) :=
  UPred.persistently_dup P

example :
    UPred.own (Excl.own 0 : Excl Nat) ⊢ᵤ
      UPred.basicUpdate (UPred.own (Excl.own 1 : Excl Nat)) :=
  UPred.own_update (Excl.update_own 0 1)

example (P R : UPred Unit) :
    UPred.sep (UPred.basicUpdate P) R ⊢ᵤ
      UPred.basicUpdate (UPred.sep P R) :=
  UPred.basicUpdate_frame P R

example : Contractive (UPred.later : UPred Unit → UPred Unit) :=
  UPred.later_contractive

example : NonExpansive (UPred.persistently : UPred Unit → UPred Unit) :=
  UPred.persistently_nonExpansive

namespace GenericBI

open LeanIrisX.BI

theorem sep_swap {PROP : Type u} [BIBase PROP] [BI.Laws PROP]
    (P Q : PROP) : P ∗ Q ⊢ Q ∗ P :=
  BI.Laws.sep_comm P Q

end GenericBI

end LeanIrisX.Tests.SemanticCore
