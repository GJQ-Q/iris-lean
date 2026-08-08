import LeanIrisX.Logic.RecursiveLogic

namespace LeanIrisX.Tests.RecursiveLogic

open LeanIrisX LeanIrisX.UnitGhostIris

#synth BIBase UnitGhostIris.IProp
#synth BI.Laws UnitGhostIris.IProp
#synth GhostOwn UnitGhostIris.IProp Unit

theorem client_can_combine_core_and_plugin (X : IPre) (γ : GhostName) :
    UPred.sep (ownGuarded X) (ownNamedUnit γ) ⊢ᵤ
      ownResource (CMRA.op (guardedSlot X) (pluginSlot γ)) :=
  slots_compose X γ

theorem client_can_apply_resource_update (a : IRes) :
    ownResource a ⊢ᵤ bupd (ownResource a) :=
  ownResource_update_refl a

theorem duplicate_guarded_ownership_is_invalid (X Y : IPre) :
    ¬ CMRA.valid (CMRA.op (guardedSlot X) (guardedSlot Y)) :=
  guarded_slots_conflict X Y

theorem typed_named_ownership_splits (γ : GhostName) :
    GhostOwn.owns (PROP := UnitGhostIris.IProp) γ (() ⋅ ()) ⊢
      UPred.sep (GhostOwn.owns (PROP := UnitGhostIris.IProp) γ ())
        (GhostOwn.owns (PROP := UnitGhostIris.IProp) γ ()) :=
  namedUnit_op γ () ()

end LeanIrisX.Tests.RecursiveLogic
