import LeanIrisX.Logic.GhostState

namespace LeanIrisX
open BI

class Invariant (PROP : Type u) where
  inv : Namespace → PROP → PROP

namespace Invariant

variable {PROP : Type u} [BIBase PROP] [FancyUpdate PROP] [Invariant PROP]

def invProp (N : Namespace) (P : PROP) : PROP := Invariant.inv N P

/-- The close token is a wand that consumes the later body and restores the
mask. This prevents an opened invariant from being silently discarded. -/
def closeToken (E : Mask) (N : Namespace) (P : PROP) : PROP :=
  BIBase.wand (BIBase.later P)
    (FancyUpdate.apply (Mask.without E N) E BIBase.emp)

class Laws : Prop where
  persistent : ∀ (N : Namespace) (P : PROP),
    invProp (PROP := PROP) N P ⊢
      BIBase.persistently (invProp (PROP := PROP) N P)
  alloc : ∀ (E : Mask) (N : Namespace) (P : PROP),
    P ⊢ FancyUpdate.apply E E (invProp (PROP := PROP) N P)
  openInvariant : ∀ (E : Mask) (N : Namespace) (P : PROP),
    invProp (PROP := PROP) N P ⊢ FancyUpdate.apply E (Mask.without E N)
      (BIBase.sep (BIBase.later P) (closeToken (PROP := PROP) E N P))

end Invariant
end LeanIrisX
