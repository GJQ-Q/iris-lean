import LeanIrisX.Algebra.FreshName
import LeanIrisX.Logic.Ownership

namespace LeanIrisX.UPred

open LeanIrisX

def allocatorAuthority (s : FreshNameState) : UPred FreshNameGhost.Resource :=
  own (FreshNameGhost.authority s)

def allocatedToken (γ : GhostName) : UPred FreshNameGhost.Resource :=
  own (FreshNameGhost.token γ)

/-- Logical allocation: owning the authoritative high-water mark can be
updated to the advanced authority together with a token for the genuinely
fresh name. -/
theorem allocateFresh (s : FreshNameState) :
    allocatorAuthority s ⊢ᵤ
      basicUpdate (sep
        (allocatorAuthority (FreshNameState.advance s))
        (allocatedToken (FreshNameState.fresh s))) := by
  apply entails_trans (own_update (FreshNameGhost.allocate_update s))
  apply basicUpdate_mono
  exact own_op_sep _ _

end LeanIrisX.UPred
