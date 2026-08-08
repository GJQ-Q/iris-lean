import LeanIrisX.Logic.GuardedResourceFunctor

namespace LeanIrisX.Tests.GuardedResourceFunctor

open LeanIrisX

#synth OFunctor GuardedResourceF
#synth OFunctorContractive GuardedResourceF
#synth UCMRAFunctor GuardedResourceF
#synth OFunctor GuardedPropF
#synth OFunctorContractive GuardedPropF
#synth OFE RecursiveIProp.IPre
#synth COFE RecursiveIProp.IPre
#synth OFE RecursiveIProp.IRes
#synth CMRA RecursiveIProp.IRes
#synth UCMRA RecursiveIProp.IRes

theorem recursive_resource_payload_is_delayed (X Y : RecursiveIProp.IPre) :
    GuardedExcl.own (Later.next X) ≡{0}≡
      (GuardedExcl.own (Later.next Y) : RecursiveIProp.IRes) := by
  change Later.next X ≡{0}≡ Later.next Y
  exact Later.dist_zero _ _

theorem guarded_payload_visible_at_one :
    ¬ (GuardedExcl.own (Later.next 0) ≡{1}≡
      (GuardedExcl.own (Later.next 1) : GuardedExcl Nat)) := by
  intro h
  change Later.next 0 ≡{1}≡ Later.next 1 at h
  have h01 : (0 : Nat) ≡{0}≡ 1 := Later.dist_succ_iff.mp h
  exact Nat.zero_ne_one (OFE.Discrete.eq_of_dist h01)

theorem recursive_fold_unfold (P : RecursiveIProp.IProp) :
    RecursiveIProp.fold (RecursiveIProp.unfold P) = P :=
  RecursiveIProp.fold_unfold P

theorem recursive_unfold_fold (X : RecursiveIProp.IPre) :
    RecursiveIProp.unfold (RecursiveIProp.fold X) = X :=
  RecursiveIProp.unfold_fold X

end LeanIrisX.Tests.GuardedResourceFunctor
