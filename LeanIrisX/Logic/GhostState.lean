import LeanIrisX.Logic.FancyUpdate
import LeanIrisX.Algebra.Update

namespace LeanIrisX
open BI

abbrev GhostName := Nat

/-- Typed named ghost ownership. Different ghost algebras obtain different
instances; no universal untyped store is assumed here. -/
class GhostOwn (PROP : Type u) (A : Type v) where
  own : GhostName → A → PROP
  validProp : A → PROP

namespace GhostOwn

variable {PROP : Type u} {A : Type v} [BIBase PROP] [BIQuantifiers PROP]
  [FancyUpdate PROP] [GhostOwn PROP A]

def owns (γ : GhostName) (a : A) : PROP := GhostOwn.own γ a
def valid (a : A) : PROP := GhostOwn.validProp a

class Laws [OFE A] [CMRA A] : Prop where
  op : ∀ (γ : GhostName) (a b : A),
    owns (PROP := PROP) γ (CMRA.op a b) ⊢
      BIBase.sep (owns (PROP := PROP) γ a) (owns (PROP := PROP) γ b)
  valid_elim : ∀ (γ : GhostName) (a : A),
    owns (PROP := PROP) γ a ⊢ valid (PROP := PROP) a
  update : ∀ {a b : A}, CMRA.FramePreservingUpdate a b →
    ∀ (γ : GhostName) (E : Mask), owns (PROP := PROP) γ a ⊢
      FancyUpdate.apply E E (owns (PROP := PROP) γ b)
class AllocationLaws [OFE A] [CMRA A] : Prop where
  alloc : ∀ (a : A), CMRA.valid a →
    BIBase.emp ⊢ BI.biExist (fun γ : GhostName =>
      FancyUpdate.apply Mask.full Mask.full (owns (PROP := PROP) γ a))

end GhostOwn
end LeanIrisX
