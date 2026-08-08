import LeanIrisX.Tests.SemanticCore
import LeanIrisX.Tests.LogicCore
import LeanIrisX.Tests.ResourceInterface
import LeanIrisX.Tests.GlobalResource
import LeanIrisX.Tests.FreshAllocator
import LeanIrisX.Tests.NonDiscrete
import LeanIrisX.Tests.AgreementRaw
import LeanIrisX.Tests.Agreement
import LeanIrisX.Tests.ViewRel
import LeanIrisX.Tests.DFracOption
import LeanIrisX.Tests.View
import LeanIrisX.Tests.ViewUpdate
import LeanIrisX.Tests.Auth
import LeanIrisX.Tests.UpdateP
import LeanIrisX.Tests.LocalUpdate
import LeanIrisX.Tests.ViewLocalUpdate
import LeanIrisX.Tests.LocalUpdateInstances
import LeanIrisX.Examples.MonoNatGhost

open LeanIrisX LeanIrisX.UPred

#check IProp
#check IProp.imp
#check IProp.all
#check IProp.exist
#check Persistent
#check Affine
#check Absorbing
#check Timeless
#check LeanIrisX.Tests.LogicCore.intuitionistic_modus_ponens
#check LeanIrisX.Tests.LogicCore.quantified_choice
#print axioms LeanIrisX.Tests.LogicCore.intuitionistic_modus_ponens
#print axioms LeanIrisX.Tests.LogicCore.quantified_choice
#check Namespace
#check Mask
#check FancyUpdate
#check GhostName
#check GhostOwn
#check Invariant
#check Invariant.closeToken
#check LeanIrisX.Tests.ResourceInterface.removed_namespace_is_unavailable
#check LeanIrisX.Tests.ResourceInterface.fancy_update_can_be_framed
#check LeanIrisX.Tests.ResourceInterface.invariant_open_rule_available
#print axioms LeanIrisX.Tests.ResourceInterface.removed_namespace_is_unavailable
#check TotalCore
#check GhostMap
#synth OFE (GhostMap Unit)
#synth CMRA (GhostMap Unit)
#synth UCMRA (GhostMap Unit)
#check UPredGhost.namedOwn
#check UPredGhost.validProp
#check LeanIrisX.Tests.GlobalResource.named_unit_composes
#check LeanIrisX.Tests.GlobalResource.named_unit_is_step_valid
#print axioms LeanIrisX.Tests.GlobalResource.named_unit_composes
#print axioms LeanIrisX.Tests.GlobalResource.named_unit_is_step_valid
#check FreshNameState
#check FreshNameState.Allocated
#check FreshNameState.fresh_not_allocated
#check FreshNameGhost.Resource
#check FreshNameGhost.allocate_update
#check FreshNameGhost.token_proves_allocated
#check UPred.allocateFresh
#check LeanIrisX.Tests.FreshAllocator.logical_fresh_allocation
#print axioms FreshNameGhost.allocate_update
#print axioms FreshNameGhost.token_proves_allocated
#print axioms LeanIrisX.Tests.FreshAllocator.logical_fresh_allocation

#check MonoNat
#check MonoNatGhost.Ghost
#check MonoNatGhost.authoritative
#check MonoNatGhost.fragment
#check MonoNatGhost.fragment_le_authority
#check MonoNatGhost.authoritative_grow
#check MonoNatGhost.allocate_fragment
#check MonoNatGhost.grow_and_allocate
#check LeanIrisX.Examples.MonoNatGhost.ownership_counter_can_grow
#check LeanIrisX.Examples.MonoNatGhost.ownership_can_allocate_fragment
#check LeanIrisX.Examples.MonoNatGhost.ownership_can_grow_and_allocate
#check UPred.own_op_sep
#check UPred.sep_own_op
#check LeanIrisX.Examples.MonoNatGhost.ownership_can_grow_and_split_fragment
#print axioms MonoNat.instCMRA
#print axioms MonoNatGhost.authoritative_grow
#print axioms LeanIrisX.Examples.MonoNatGhost.ownership_counter_can_grow
#print axioms MonoNatGhost.allocate_fragment
#print axioms MonoNatGhost.grow_and_allocate
#print axioms LeanIrisX.Examples.MonoNatGhost.ownership_can_allocate_fragment
#print axioms LeanIrisX.Examples.MonoNatGhost.ownership_can_grow_and_allocate
#print axioms UPred.own_op_sep
#print axioms UPred.sep_own_op
#print axioms LeanIrisX.Examples.MonoNatGhost.ownership_can_grow_and_split_fragment

#check CMRA.FramePreservingUpdateP
#check CMRA.opFrame
#check CMRA.update_preserves_validN
#check CMRA.updateP_preserves_validN
#check CMRA.update_of_total
#check CMRA.updateP_of_total
#check CMRA.LocalUpdate
#check CMRA.localUpdate_refl
#check CMRA.localUpdate_trans
#check CMRA.localUpdate_iff_total
#check View.localUpdate
#check Auth.localUpdate
#check CMRA.localUpdate_prod
#check CMRA.localUpdate_option
#check CMRA.localUpdate_alloc_option
#print axioms CMRA.localUpdate_prod
#print axioms CMRA.localUpdate_option
#print axioms CMRA.localUpdate_alloc_option
#print axioms LeanIrisX.Tests.LocalUpdateInstances.product_unit_local_update
#print axioms LeanIrisX.Tests.LocalUpdateInstances.allocate_option_unit
#print axioms View.localUpdate
#print axioms Auth.localUpdate
#print axioms LeanIrisX.Tests.ViewLocalUpdate.auth_unit_local_update
#print axioms LeanIrisX.Tests.LocalUpdate.unit_local_update
#print axioms LeanIrisX.Tests.LocalUpdate.local_update_composes
#print axioms LeanIrisX.Tests.LocalUpdate.unital_characterization_available
#check CMRA.update_to_updateP
#check CMRA.updateP_trans
#check View.full_auth_frag_updateP
#check Auth.authoritative_fragment_updateP

#check ValidAt
#check UPred
#check UPred.own
#check UPred.sep
#check UPred.later
#check UPred.wand
#check UPred.emp
#check UPred.basicUpdate
#check UPred.plainly
#check UPred.persistently
#check UPred.own_update
#check BIBase
#check BI.Laws
#synth BIBase (UPred Unit)
#synth BI.Laws (UPred Unit)
#synth OFE (Later Bool)
#synth COFE (Later Bool)
#check Later.next_contractive
#check Agreement.Raw
#check Agreement.Raw.Dist
#check Agreement.Raw.ValidN
#check Agreement
#check Agreement.toAgreement
#synth CMRA (Agreement (Later Bool))
#check ViewRel
#check IsViewRel
#check AuthViewRel
#synth IsViewRel (AuthViewRel (A := Unit))
#check PosRat
#check DFrac
#check DFrac.half
#synth CMRA DFrac
#synth OFE (Option Unit)
#synth CMRA (Option Unit)
#synth UCMRA (Option Unit)
#check View
#check View.Auth
#check View.Frag
#check View.ValidN
#check View.op
#check View.auth_frag_validN_iff
#check View.full_auth_frag_update
#check View.full_auth_update
#check View.full_auth_alloc
#check View.full_auth_dealloc
#check Auth
#check Auth.authoritative
#check Auth.authoritativeDFrac
#check Auth.fragment
#check Auth.authoritative_fragment_validN
#check Auth.fragment_includedN
#check Auth.fragment_validN
#check Auth.authoritative_update
#check Auth.alloc_fragment
#check Auth.dealloc_fragment
#synth CMRA (Auth Unit)
#synth UCMRA (Auth Unit)
#synth CMRA (View (AuthViewRel (A := Unit)))
#synth UCMRA (View (AuthViewRel (A := Unit)))
#check UPred.includedN_trans
#synth OFE (UPred Unit)
#synth COFE (UPred Unit)

#print axioms UPred.includedN_trans
#print axioms UPred.sep_comm
#print axioms UPred.sep_assoc
#print axioms UPred.sep_emp_right
#print axioms UPred.wand_elim
#print axioms UPred.basicUpdate_intro
#print axioms UPred.basicUpdate_mono
#print axioms UPred.basicUpdate_idem
#print axioms UPred.own_update
#print axioms UPred.plainly_elim
#print axioms UPred.persistently_elim
#print axioms UPred.persistently_dup
#print axioms UPred.basicUpdate_frame
#print axioms UPred.later_contractive
#print axioms UPred.persistently_nonExpansive
#print axioms LeanIrisX.Tests.SemanticCore.GenericBI.sep_swap
#print axioms LeanIrisX.Tests.NonDiscrete.hidden_at_zero
#print axioms LeanIrisX.Tests.NonDiscrete.visible_at_one
#print axioms Later.next_contractive
#print axioms LeanIrisX.Tests.AgreementRaw.combined_valid_zero
#print axioms LeanIrisX.Tests.AgreementRaw.combined_invalid_one
#print axioms Agreement.op_comm
#print axioms Agreement.op_assoc
#print axioms Agreement.instCMRA
#print axioms LeanIrisX.Tests.Agreement.combined_valid_zero
#print axioms LeanIrisX.Tests.Agreement.combined_invalid_one
#print axioms ViewRel.iff_of_dist
#print axioms AuthViewRel.instIsViewRel
#print axioms AuthViewRel.fragment_valid
#print axioms DFrac.instCMRA
#print axioms OptionCMRA.instCMRA
#print axioms LeanIrisX.Tests.DFracOption.two_halves_make_full
#print axioms LeanIrisX.Tests.DFracOption.full_and_half_conflict
#print axioms LeanIrisX.Tests.DFracOption.discarding_owned_fraction_records_both
#print axioms LeanIrisX.Tests.DFracOption.option_some_composes
#print axioms View.instOFE
#print axioms View.auth_one_frag_validN_iff
#print axioms View.instCMRA
#print axioms View.instUCMRA
#print axioms LeanIrisX.Tests.View.authority_fragment_validN
#print axioms LeanIrisX.Tests.View.authority_fragment_cmra_validN
#print axioms LeanIrisX.Tests.View.view_unit_valid
#print axioms View.full_auth_frag_update
#print axioms LeanIrisX.Tests.ViewUpdate.authority_update_refl
#print axioms LeanIrisX.Tests.ViewUpdate.allocate_unit_fragment
#print axioms LeanIrisX.Tests.ViewUpdate.deallocate_unit_fragment
#print axioms Auth.authoritative_fragment_validN
#print axioms Auth.authoritative_fragment_update
#print axioms LeanIrisX.Tests.Auth.authoritative_fragment_valid
#print axioms LeanIrisX.Tests.Auth.fragment_is_included
#print axioms LeanIrisX.Tests.Auth.authoritative_update_refl
#print axioms View.full_auth_frag_updateP
#print axioms Auth.authoritative_fragment_updateP
#print axioms LeanIrisX.Tests.UpdateP.auth_unit_predicate_update
#print axioms LeanIrisX.Tests.UpdateP.deterministic_embeds_into_predicate_update
#print axioms UPred.later_intro

#check ResourceMap
#check InvariantEntry
#check InvariantRegistry
#check WorldSnapshot
#check WorldSatisfaction.WSatAt
#check LeanIrisX.Tests.InvariantEntry.registry_cell_forces_body_agreement
#check LeanIrisX.Tests.WorldSatisfaction.one_closed_tokens_are_valid
#check LeanIrisX.Tests.WorldSatisfaction.same_name_cannot_be_closed_and_opened

#print axioms InvariantRegistry.validN_same_name_agree
#print axioms WorldSatisfaction.closed_opened_tokens_valid
#print axioms WorldSatisfaction.registered_is_exactly_one_state
#print axioms LeanIrisX.Tests.WorldSatisfaction.same_name_cannot_be_closed_and_opened

#check WorldTransition.openName
#check WorldTransition.closeName
#check WorldTransition.wsat_open
#check WorldTransition.wsat_close
#check LeanIrisX.Tests.WorldTransition.opening_preserves_wsat
#check LeanIrisX.Tests.WorldTransition.closing_preserves_wsat
#check LeanIrisX.Tests.WorldTransition.opened_name_cannot_remain_closed

#print axioms WorldTransition.wsat_open
#print axioms WorldTransition.wsat_close
#print axioms LeanIrisX.Tests.WorldTransition.opened_name_cannot_remain_closed

#check OFunctorPre
#check OFunctor
#check OFunctorContractive
#check OFunctor.Const
#check OFunctor.Id
#check OFunctor.LaterF
#check LeanIrisX.Tests.OFunctor.identity_map_is_identity
#check LeanIrisX.Tests.OFunctor.later_map_identity

#print axioms LeanIrisX.Tests.OFunctor.identity_map_is_identity
#print axioms LeanIrisX.Tests.OFunctor.later_map_identity

#check COFETower.PackedCOFE
#check COFETower.stagePack
#check COFETower.Stage
#check COFETower.up
#check COFETower.down
#check COFETower.down_up
#check LeanIrisX.Tests.COFETower.every_stage_retracts
#check COFETower.up_down
#check COFETower.Tower
#check COFETower.towerChain
#check COFETower.Tower.proj
#synth OFE (COFETower.Tower LeanIrisX.Tests.COFETower.F LeanIrisX.Tests.COFETower.seed)
#synth COFE (COFETower.Tower LeanIrisX.Tests.COFETower.F LeanIrisX.Tests.COFETower.seed)
#check LeanIrisX.Tests.COFETower.tower_limit_observed_at

#print axioms COFETower.down_up
#print axioms LeanIrisX.Tests.COFETower.every_stage_retracts
#print axioms COFETower.up_down
#print axioms LeanIrisX.Tests.COFETower.tower_limit_observed_at
#check COFETower.upN
#check COFETower.downN
#check COFETower.Tower.embed
#check COFETower.Tower.embed_up
#check COFETower.Tower.embed_self
#check COFETower.towerFold
#check COFETower.towerUnfold
#check COFETower.towerIso
#check COFETower.Fix
#check COFETower.Fix.fold
#check COFETower.Fix.unfold
#check COFETower.Fix.fold_unfold
#check COFETower.Fix.unfold_fold
#check LeanIrisX.Tests.COFETower.fold_after_unfold_is_identity
#check LeanIrisX.Tests.COFETower.unfold_after_fold_is_identity

#print axioms COFETower.Tower.embed_up
#print axioms COFETower.Tower.embed_self
#print axioms COFETower.towerFold_unfold
#print axioms COFETower.towerUnfold_fold
#print axioms COFETower.Fix.fold_unfold
#print axioms COFETower.Fix.unfold_fold
#print axioms LeanIrisX.Tests.COFETower.fold_after_unfold_is_identity
#print axioms LeanIrisX.Tests.COFETower.unfold_after_fold_is_identity
#check CMRAHom
#check CMRAHom.includedN_map
#check UCMRAFunctor
#check UCMRAFunctor.mapCMRA
#check UPred.holds_ne
#check UPred.map
#check UPredOF
#synth UCMRAFunctor LeanIrisX.Tests.UPredFunctor.ResourceF
#synth OFunctor LeanIrisX.Tests.UPredFunctor.PropF
#synth OFunctorContractive LeanIrisX.Tests.UPredFunctor.PropF
#check LeanIrisX.Tests.UPredFunctor.RecursivePropDomain
#check LeanIrisX.Tests.UPredFunctor.recursive_fold_unfold
#check LeanIrisX.Tests.UPredFunctor.recursive_unfold_fold

#print axioms CMRAHom.includedN_map
#print axioms UPred.holds_ne
#print axioms UPred.map_comp
#print axioms LeanIrisX.Tests.UPredFunctor.recursive_fold_unfold
#print axioms LeanIrisX.Tests.UPredFunctor.recursive_unfold_fold

#check GuardedExcl
#check GuardedExcl.Dist
#check GuardedResourceF
#synth OFunctor GuardedResourceF
#synth OFunctorContractive GuardedResourceF
#synth UCMRAFunctor GuardedResourceF
#check RecursiveIProp.IPre
#check RecursiveIProp.IRes
#check RecursiveIProp.IProp
#check RecursiveIProp.fold
#check RecursiveIProp.unfold
#check RecursiveIProp.fold_unfold
#check RecursiveIProp.unfold_fold
#check LeanIrisX.Tests.GuardedResourceFunctor.recursive_resource_payload_is_delayed
#check LeanIrisX.Tests.GuardedResourceFunctor.guarded_payload_visible_at_one

#print axioms RecursiveIProp.fold_unfold
#print axioms RecursiveIProp.unfold_fold
#print axioms LeanIrisX.Tests.GuardedResourceFunctor.recursive_resource_payload_is_delayed
#print axioms LeanIrisX.Tests.GuardedResourceFunctor.guarded_payload_visible_at_one

#check ProductOF
#check IrisResourceF
#check ExtensibleIris.IPre
#check ExtensibleIris.IRes
#check ExtensibleIris.IProp
#check UnitGhostPlugin
#check UnitGhostIris.guardedSlot
#check UnitGhostIris.pluginSlot
#check UnitGhostIris.fold_unfold
#check UnitGhostIris.unfold_fold
#check LeanIrisX.Tests.ExtensibleResource.core_and_plugin_compose

#print axioms UnitGhostIris.fold_unfold
#print axioms UnitGhostIris.unfold_fold
#print axioms LeanIrisX.Tests.ExtensibleResource.core_and_plugin_compose

#check UnitGhostIris.ownResource
#check UnitGhostIris.ownGuarded
#check UnitGhostIris.ownNamedUnit
#check UnitGhostIris.bupd
#check UnitGhostIris.ownResource_update
#check UnitGhostIris.slots_compose
#check UnitGhostIris.guarded_slots_conflict
#synth GhostOwn UnitGhostIris.IProp Unit
#check LeanIrisX.Tests.RecursiveLogic.client_can_combine_core_and_plugin
#check LeanIrisX.Tests.RecursiveLogic.client_can_apply_resource_update
#check LeanIrisX.Tests.RecursiveLogic.duplicate_guarded_ownership_is_invalid

#print axioms UnitGhostIris.ownResource_update
#print axioms UnitGhostIris.slots_compose
#print axioms UnitGhostIris.guarded_slots_conflict

#check InvariantRegistryF
#synth OFunctor InvariantRegistryF
#synth OFunctorContractive InvariantRegistryF
#synth UCMRAFunctor InvariantRegistryF
#check WorldPlugin
#check WorldIris.IPre
#check WorldIris.IRes
#check WorldIris.IProp
#check WorldIris.invariantSlot
#check WorldIris.WSatAt
#check WorldIris.openName
#check WorldIris.closeName
#check WorldIris.distinct_invariants_compatible
#check WorldIris.same_invariant_conflicts
#check LeanIrisX.Tests.RecursiveWorld.two_names_can_coexist
#check LeanIrisX.Tests.RecursiveWorld.one_name_cannot_have_two_bodies

#print axioms WorldIris.fold_unfold
#print axioms WorldIris.distinct_invariants_compatible
#print axioms WorldIris.same_invariant_conflicts

#check CertifiedFancyUpdate.Admissible
#check CertifiedFancyUpdate.fupd
#synth FancyUpdate (UPred Unit)
#synth FancyUpdate.Laws (UPred Unit)
#check LeanIrisX.Tests.CertifiedFancyUpdate.shrinking_update_is_available
#check LeanIrisX.Tests.CertifiedFancyUpdate.unsupported_enlargement_is_impossible
#check LeanIrisX.Tests.CertifiedFancyUpdate.certified_updates_compose
#check LeanIrisX.Tests.CertifiedFancyUpdate.certified_update_frames

#print axioms CertifiedFancyUpdate.trans
#print axioms CertifiedFancyUpdate.frame
#print axioms LeanIrisX.Tests.CertifiedFancyUpdate.unsupported_enlargement_is_impossible

#check WorldInvariantProtocol.OpenCertificate
#check WorldInvariantProtocol.OpenCertificate.RestorationPermit
#check WorldInvariantProtocol.OpenCertificate.opened_wsat
#check WorldInvariantProtocol.OpenCertificate.close_wsat
#check WorldInvariantProtocol.OpenCertificate.close_restores_world
#check WorldInvariantProtocol.OpenCertificate.restoration_not_plain
#check LeanIrisX.Tests.WorldInvariantProtocol.opening_removes_the_namespace
#check LeanIrisX.Tests.WorldInvariantProtocol.restoration_requires_protocol

#print axioms WorldInvariantProtocol.OpenCertificate.opened_wsat
#print axioms WorldInvariantProtocol.OpenCertificate.close_restores_world
#print axioms WorldInvariantProtocol.OpenCertificate.restoration_not_plain

#check InvariantId
#check InvariantKey
#check InvariantIdentity.Catalog
#check InvariantIdentity.authoritative
#check InvariantIdentity.handle
#check InvariantIdentity.handle_op_idem
#check InvariantIdentity.same_namespace_distinct_ids_valid
#check InvariantIdentity.same_id_forces_body_agreement
#check LeanIrisX.Tests.InvariantIdentity.two_invariants_can_share_namespace
#check LeanIrisX.Tests.InvariantIdentity.public_handle_is_duplicable

#print axioms InvariantIdentity.handle_op_idem
#print axioms InvariantIdentity.same_namespace_distinct_ids_valid
#print axioms InvariantIdentity.same_id_forces_body_agreement

#check NamedInvariantRegistryF
#synth OFunctor NamedInvariantRegistryF
#synth OFunctorContractive NamedInvariantRegistryF
#synth UCMRAFunctor NamedInvariantRegistryF
#check WorldPluginV2
#check WorldIrisV2.IPre
#check WorldIrisV2.IRes
#check WorldIrisV2.IProp
#check WorldIrisV2.fold_unfold
#check WorldIrisV2.handle_slot_idem
#check LeanIrisX.Tests.RecursiveWorldV2.two_invariants_share_namespace
#check LeanIrisX.Tests.RecursiveWorldV2.reused_identity_conflicts
#check LeanIrisX.Tests.RecursiveWorldV2.public_handle_duplicates

#print axioms WorldIrisV2.fold_unfold
#print axioms WorldIrisV2.same_namespace_distinct_ids_compatible
#print axioms WorldIrisV2.same_id_conflicts
#print axioms WorldIrisV2.handle_slot_idem

#check PersistentToken
#check FinalWorldPlugin
#check FinalWorld.IPre
#check FinalWorld.IRes
#check FinalWorld.IProp
#check FinalWorld.AuthenticatedAt
#check FinalWorld.registry_handle_valid
#check FinalWorld.handle_idem
#check FinalWorld.handle_nontrivial
#check FinalWorld.close_conflict
#check FinalWorld.package_authenticated
#check FinalWorldInvariantProtocol.allocate
#check FinalWorldInvariantProtocol.OpenCertificate.opened_wsat
#check FinalWorldInvariantProtocol.OpenCertificate.close_restores_world
#check FinalWorldInvariantProtocol.OpenCertificate.close_permission_linear
#check LeanIrisX.Tests.WorldResourceFinal.authenticated_package
#check LeanIrisX.Tests.WorldResourceFinal.close_permission_cannot_be_copied

#print axioms FinalWorld.fold_unfold
#print axioms FinalWorld.registry_handle_valid
#print axioms FinalWorld.handle_idem
#print axioms FinalWorld.handle_nontrivial
#print axioms FinalWorld.close_conflict
#print axioms FinalWorld.package_authenticated
