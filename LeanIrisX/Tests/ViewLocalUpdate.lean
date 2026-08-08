import LeanIrisX.Algebra.ViewLocalUpdate

namespace LeanIrisX.Tests.ViewLocalUpdate

open LeanIrisX

theorem auth_unit_local_update :
    CMRA.LocalUpdate
      (CMRA.op (Auth.authoritative ()) (Auth.fragment ()),
       CMRA.op (Auth.authoritative ()) (Auth.fragment ()))
      (CMRA.op (Auth.authoritative ()) (Auth.fragment ()),
       CMRA.op (Auth.authoritative ()) (Auth.fragment ())) := by
  apply Auth.localUpdate (CMRA.localUpdate_unit ((), ()) ((), ()))
  intro n h
  exact h

end LeanIrisX.Tests.ViewLocalUpdate
