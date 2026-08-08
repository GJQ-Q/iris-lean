import LeanIrisX.Logic.FreshAllocation

namespace LeanIrisX.Tests.FreshAllocator
open LeanIrisX LeanIrisX.UPred

def afterThree : FreshNameState := ⟨3⟩

theorem next_name_is_three : FreshNameState.fresh afterThree = 3 := rfl

theorem three_was_not_allocated :
    ¬ FreshNameState.Allocated afterThree 3 := by
  simp [FreshNameState.Allocated, afterThree]

theorem three_is_allocated_after :
    FreshNameState.Allocated (FreshNameState.advance afterThree) 3 := by
  simp [FreshNameState.Allocated, FreshNameState.advance, afterThree]

theorem allocation_preserves_old_name :
    FreshNameState.Allocated afterThree 1 →
      FreshNameState.Allocated (FreshNameState.advance afterThree) 1 :=
  FreshNameState.previously_allocated_remains

theorem logical_fresh_allocation :
    allocatorAuthority afterThree ⊢ᵤ
      basicUpdate (sep
        (allocatorAuthority (FreshNameState.advance afterThree))
        (allocatedToken 3)) :=
  allocateFresh afterThree

end LeanIrisX.Tests.FreshAllocator
