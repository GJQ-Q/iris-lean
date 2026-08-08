import LeanIrisX.Logic.IProp

/-! Standard Iris proposition-property classes. -/

namespace LeanIrisX
open BI

class Persistent {PROP : Type u} [BIBase PROP] (P : PROP) : Prop where
  persistent : P ⊢ BIBase.persistently P

class Affine {PROP : Type u} [BIBase PROP] (P : PROP) : Prop where
  affine : P ⊢ BIBase.emp

def absorbingly {PROP : Type u} [BIBase PROP] (P : PROP) : PROP :=
  BIBase.sep (BIBase.pure True) P

class Absorbing {PROP : Type u} [BIBase PROP] (P : PROP) : Prop where
  absorbing : absorbingly P ⊢ P

def except0 {PROP : Type u} [BIBase PROP] (P : PROP) : PROP :=
  BIBase.or (BIBase.later (BIBase.pure False)) P

class Timeless {PROP : Type u} [BIBase PROP] (P : PROP) : Prop where
  timeless : BIBase.later P ⊢ except0 P

end LeanIrisX
