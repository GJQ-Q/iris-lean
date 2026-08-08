import LeanIrisX.Algebra.MonoNat
import LeanIrisX.Logic.Modalities
import LeanIrisX.Logic.Ownership

namespace LeanIrisX.Examples.MonoNatGhost

open LeanIrisX LeanIrisX.UPred

theorem observed_fragment_is_bounded {n : Nat}
    (h : CMRA.validN n
      (CMRA.op (MonoNatGhost.authoritative 10) (MonoNatGhost.fragment 7))) :
    7 ≤ 10 :=
  MonoNatGhost.fragment_le_authority h

theorem counter_can_grow :
    CMRA.FramePreservingUpdate
      (MonoNatGhost.authoritative 3) (MonoNatGhost.authoritative 8) :=
  MonoNatGhost.authoritative_grow (by decide)

theorem ownership_counter_can_grow :
    UPred.own (MonoNatGhost.authoritative 3) ⊢ᵤ
      UPred.basicUpdate (UPred.own (MonoNatGhost.authoritative 8)) :=
  UPred.own_update counter_can_grow

theorem ownership_can_allocate_fragment :
    UPred.own (MonoNatGhost.authoritative 8) ⊢ᵤ
      UPred.basicUpdate
        (UPred.own (CMRA.op (MonoNatGhost.authoritative 8)
          (MonoNatGhost.fragment 5))) :=
  UPred.own_update (MonoNatGhost.allocate_fragment (by decide))

theorem ownership_can_grow_and_allocate :
    UPred.own (MonoNatGhost.authoritative 3) ⊢ᵤ
      UPred.basicUpdate
        (UPred.own (CMRA.op (MonoNatGhost.authoritative 8)
          (MonoNatGhost.fragment 8))) :=
  UPred.own_update (MonoNatGhost.grow_and_allocate (by decide))

theorem ownership_can_grow_and_split_fragment :
    UPred.own (MonoNatGhost.authoritative 3) ⊢ᵤ
      UPred.basicUpdate
        (UPred.sep
          (UPred.own (MonoNatGhost.authoritative 8))
          (UPred.own (MonoNatGhost.fragment 8))) := by
  apply UPred.entails_trans ownership_can_grow_and_allocate
  apply UPred.basicUpdate_mono
  exact UPred.own_op_sep _ _

end LeanIrisX.Examples.MonoNatGhost
