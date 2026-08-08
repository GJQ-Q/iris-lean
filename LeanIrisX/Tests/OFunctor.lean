import LeanIrisX.Core.OFunctor

namespace LeanIrisX.Tests.OFunctor

open LeanIrisX

theorem identity_map_is_identity (x : Nat) :
    OFunctor.mapHom OFunctor.Id (OFEMor.id : Nat -n> Nat)
      (OFEMor.id : Nat -n> Nat) x = x := rfl

theorem later_map_identity (x : Later Nat) :
    OFunctor.mapHom OFunctor.LaterF (OFEMor.id : Nat -n> Nat)
      (OFEMor.id : Nat -n> Nat) x = x := by cases x; rfl

theorem constant_ignores_both_maps (x : Bool) :
    OFunctor.mapHom (OFunctor.Const Bool)
      (OFEMor.const 0 : Unit -n> Nat)
      (OFEMor.const () : Nat -n> Unit) x = x := rfl

end LeanIrisX.Tests.OFunctor
