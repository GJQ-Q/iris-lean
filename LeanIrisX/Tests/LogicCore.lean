import LeanIrisX.Logic.Classes

namespace LeanIrisX.Tests.LogicCore

open LeanIrisX LeanIrisX.UPred

theorem quantified_choice {M : Type u} [OFE M] [CMRA M] [UCMRA M]
    {α : Sort v} (P : α → UPred M) (i : α) :
    P i ⊢ᵤ UPred.exist P :=
  UPred.exist_intro P i

theorem intuitionistic_modus_ponens {M : Type u} [OFE M] [CMRA M] [UCMRA M]
    (P Q : UPred M) :
    UPred.and P (UPred.imp P Q) ⊢ᵤ Q :=
  UPred.imp_elim P Q

def generic_implication_available {PROP : Type u}
    [BIBase PROP] [BIQuantifiers PROP] (P Q : PROP) : PROP :=
  BIBase.imp P Q

#synth BIBase (UPred Unit)
#synth BIQuantifiers (UPred Unit)

end LeanIrisX.Tests.LogicCore
