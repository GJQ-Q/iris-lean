import LeanIrisX.Logic.ExtensibleResource
import LeanIrisX.Logic.Ownership
import LeanIrisX.Logic.GhostState

/-! Concrete ownership API for the solved, extensible recursive proposition model. -/

namespace LeanIrisX
namespace UnitGhostIris

def ownResource (a : IRes) : IProp := UPred.own a
def ownGuarded (X : IPre) : IProp := ownResource (guardedSlot X)
def ownNamedUnit (γ : GhostName) : IProp := ownResource (pluginSlot γ)
def validResource (a : IRes) : IProp := UPred.pure (CMRA.valid a)
def bupd (P : IProp) : IProp := UPred.basicUpdate P

theorem ownResource_op (a b : IRes) :
    ownResource (CMRA.op a b) ⊢ᵤ UPred.sep (ownResource a) (ownResource b) :=
  UPred.own_op_sep a b

theorem sep_ownResource (a b : IRes) :
    UPred.sep (ownResource a) (ownResource b) ⊢ᵤ
      ownResource (CMRA.op a b) :=
  UPred.sep_own_op a b

theorem ownResource_update {a b : IRes} (h : a ~~> b) :
    ownResource a ⊢ᵤ bupd (ownResource b) :=
  UPred.own_update h

theorem ownResource_update_refl (a : IRes) :
    ownResource a ⊢ᵤ bupd (ownResource a) :=
  ownResource_update (CMRA.update_refl a)

theorem slots_compose (X : IPre) (γ : GhostName) :
    UPred.sep (ownGuarded X) (ownNamedUnit γ) ⊢ᵤ
      ownResource (CMRA.op (guardedSlot X) (pluginSlot γ)) :=
  sep_ownResource _ _

theorem guarded_slots_conflict (X Y : IPre) :
    ¬ CMRA.valid (CMRA.op (guardedSlot X) (guardedSlot Y)) := by
  intro h
  exact GuardedExcl.own_conflict (Later.next X) (Later.next Y) h.1

instance instGhostOwnUnit : GhostOwn IProp Unit where
  own γ _ := ownNamedUnit γ
  validProp _ := UPred.pure True

theorem namedUnit_op (γ : GhostName) (a b : Unit) :
    GhostOwn.owns (PROP := IProp) γ (CMRA.op a b) ⊢
      UPred.sep (GhostOwn.owns (PROP := IProp) γ a)
        (GhostOwn.owns (PROP := IProp) γ b) := by
  change ownNamedUnit γ ⊢ᵤ UPred.sep (ownNamedUnit γ) (ownNamedUnit γ)
  have hop : CMRA.op (pluginSlot γ) (pluginSlot γ) = pluginSlot γ := by
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k = γ <;> simp [pluginSlot, GhostMap.singleton, hk]
  have h := ownResource_op (pluginSlot γ) (pluginSlot γ)
  rw [hop] at h
  exact h

theorem namedUnit_valid (γ : GhostName) (a : Unit) :
    GhostOwn.owns (PROP := IProp) γ a ⊢
      GhostOwn.valid (PROP := IProp) a := by
  intro n x hx hown
  trivial

end UnitGhostIris
end LeanIrisX
