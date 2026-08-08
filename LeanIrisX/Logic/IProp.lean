import LeanIrisX.Logic.BIInstance

/-! Stable user-facing proposition API. -/

namespace LeanIrisX

abbrev IProp (M : Type u) [OFE M] [CMRA M] [UCMRA M] := UPred M

namespace IProp

variable {M : Type u} [OFE M] [CMRA M] [UCMRA M]

def entails : IProp M → IProp M → Prop := UPred.Entails
def emp : IProp M := UPred.emp
def pure (φ : Prop) : IProp M := UPred.pure φ
def and (P Q : IProp M) : IProp M := UPred.and P Q
def or (P Q : IProp M) : IProp M := UPred.or P Q
def imp (P Q : IProp M) : IProp M := UPred.imp P Q
def sep (P Q : IProp M) : IProp M := UPred.sep P Q
def wand (P Q : IProp M) : IProp M := UPred.wand P Q
def later (P : IProp M) : IProp M := UPred.later P
def persistently (P : IProp M) : IProp M := UPred.persistently P
def plainly (P : IProp M) : IProp M := UPred.plainly P
def basicUpdate (P : IProp M) : IProp M := UPred.basicUpdate P
def own (a : M) : IProp M := UPred.own a
def all {α : Sort v} (P : α → IProp M) : IProp M := UPred.all P
def exist {α : Sort v} (P : α → IProp M) : IProp M := UPred.exist P

end IProp
end LeanIrisX
