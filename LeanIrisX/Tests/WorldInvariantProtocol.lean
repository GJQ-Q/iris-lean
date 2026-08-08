import LeanIrisX.Logic.WorldInvariantProtocol

namespace LeanIrisX.Tests.WorldInvariantProtocol

open LeanIrisX
open LeanIrisX.WorldInvariantProtocol

def N : Namespace := [7]
def E : Mask := Mask.singleton N

theorem leaf : LeafAt E N := by
  intro K hPrefix hK
  exact hK

theorem opening_removes_the_namespace :
    Mask.erase E N = Mask.without E N :=
  erase_eq_without leaf

theorem restoration_requires_protocol :
    ¬ CertifiedFancyUpdate.Admissible (Mask.without E N) E := by
  intro h
  exact Mask.without_excludes_prefix E (Namespace.prefix_refl N)
    (h N rfl)

theorem certified_shrink_is_available :
    CertifiedFancyUpdate.Admissible E (Mask.without E N) :=
  Mask.without_subset E N

end LeanIrisX.Tests.WorldInvariantProtocol
