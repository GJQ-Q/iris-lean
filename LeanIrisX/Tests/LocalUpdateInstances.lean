import LeanIrisX.Algebra.LocalUpdateInstances

namespace LeanIrisX.Tests.LocalUpdateInstances

open LeanIrisX

theorem product_unit_local_update :
    CMRA.LocalUpdate
      ((((), ()), ((), ())) : (Unit × Unit) × (Unit × Unit))
      ((((), ()), ((), ())) : (Unit × Unit) × (Unit × Unit)) := by
  apply CMRA.localUpdate_prod_mk
  · exact CMRA.localUpdate_unit _ _
  · exact CMRA.localUpdate_unit _ _

theorem allocate_option_unit :
    CMRA.LocalUpdate
      ((none, none) : Option Unit × Option Unit)
      ((some (), some ()) : Option Unit × Option Unit) := by
  exact CMRA.localUpdate_alloc_option () none UCMRA.unit_valid

end LeanIrisX.Tests.LocalUpdateInstances
