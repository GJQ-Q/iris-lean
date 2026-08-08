import LeanIrisX.Logic.WorldSatisfaction

namespace LeanIrisX.Tests.WorldSatisfaction

open LeanIrisX

def invName : Namespace := [7, 1]
def names : Mask := Mask.singleton invName
def closed : Mask := Mask.singleton invName
def opened : Mask := Mask.empty

theorem one_closed_partition :
    WorldSatisfaction.Partition names closed opened := by
  constructor
  · intro N
    simp [names, closed, opened, Mask.singleton, Mask.empty]
  · intro N hc ho
    exact ho

theorem one_closed_state_is_exclusive :
    (closed invName ∧ ¬ opened invName) ∨
      (opened invName ∧ ¬ closed invName) := by
  apply WorldSatisfaction.registered_is_exactly_one_state one_closed_partition
  simp [names, invName, Mask.singleton]

theorem one_closed_tokens_are_valid :
    CMRA.valid (CMRA.op (MaskToken.ofMask closed) (MaskToken.ofMask opened)) :=
  WorldSatisfaction.closed_opened_tokens_valid one_closed_partition

theorem same_name_cannot_be_closed_and_opened
    (h : WorldSatisfaction.Partition names closed opened) :
    ¬ (closed invName ∧ opened invName) := by
  intro both
  exact h.2 invName both.1 both.2

end LeanIrisX.Tests.WorldSatisfaction
