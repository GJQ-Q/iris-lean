import LeanIrisX.Logic.WorldResourceFinal
import LeanIrisX.Logic.WorldInvariantProtocol

/-! A certified open/close protocol for the integrated recursive world. -/

namespace LeanIrisX
namespace FinalWorldInvariantProtocol

set_option genSizeOf false in
structure World where
  resource : FinalWorld.IRes
  closed : Mask
  opened : Mask

def WSatAt (n : Nat) (w : World) : Prop :=
  CMRA.validN n w.resource ∧ Mask.Disjoint w.closed w.opened

def openName (w : World) (N : Namespace) : World :=
  { w with closed := Mask.erase w.closed N
           opened := Mask.insert w.opened N }

def closeName (w : World) (N : Namespace) : World :=
  { w with closed := Mask.insert w.closed N
           opened := Mask.erase w.opened N }

structure AllocationCertificate (n : Nat) (N : Namespace)
    (γ : GhostName) (P : FinalWorld.IPre) : Prop where
  valid : CMRA.validN n
    (CMRA.op (FinalWorld.registrySlot N γ P) (FinalWorld.handleSlot γ))
  authenticated : FinalWorld.AuthenticatedAt n
    (CMRA.op (FinalWorld.registrySlot N γ P) (FinalWorld.handleSlot γ)) N γ P

theorem allocate (n : Nat) (N : Namespace) (γ : GhostName)
    (P : FinalWorld.IPre) : AllocationCertificate n N γ P := by
  constructor
  · exact CMRA.validN_of_valid (FinalWorld.registry_handle_valid N γ P) n
  · exact FinalWorld.package_authenticated n N γ P

structure OpenCertificate (n : Nat) (w : World) (E : Mask)
    (N : Namespace) (γ : GhostName) (P : FinalWorld.IPre) : Prop where
  wsat : WSatAt n w
  mask_eq : E = w.closed
  enabled : E N
  leaf : WorldInvariantProtocol.LeafAt E N
  authenticated : FinalWorld.AuthenticatedAt n w.resource N γ P

namespace OpenCertificate

variable {n : Nat} {w : World} {E : Mask} {N : Namespace}
  {γ : GhostName} {P : FinalWorld.IPre}

theorem closed (c : OpenCertificate n w E N γ P) : w.closed N :=
  c.mask_eq ▸ c.enabled

theorem not_opened (c : OpenCertificate n w E N γ P) : ¬ w.opened N :=
  fun ho => c.wsat.2 N c.closed ho

theorem opened_wsat (c : OpenCertificate n w E N γ P) :
    WSatAt n (openName w N) := by
  refine ⟨c.wsat.1, ?_⟩
  intro K hclosed hopened
  rcases hopened with hopened | hKN
  · exact c.wsat.2 K hclosed.1 hopened
  · exact hclosed.2 hKN

theorem opened_mask (c : OpenCertificate n w E N γ P) :
    (openName w N).closed = Mask.without E N := by
  change Mask.erase w.closed N = Mask.without E N
  rw [← c.mask_eq, WorldInvariantProtocol.erase_eq_without c.leaf]

theorem authentication_preserved (c : OpenCertificate n w E N γ P) :
    FinalWorld.AuthenticatedAt n (openName w N).resource N γ P :=
  c.authenticated

structure RestorationPermit
    (c : OpenCertificate n w E N γ P) : Prop where
  opened_wsat : WSatAt n (openName w N)
  opened_name : (openName w N).opened N
  original_not_opened : ¬ w.opened N
  close_permission_valid : CMRA.valid (FinalWorld.closeSlot γ)

theorem restorationPermit (c : OpenCertificate n w E N γ P) :
    RestorationPermit c := by
  refine ⟨c.opened_wsat, Mask.insert_self _ _, c.not_opened, ?_⟩
  have h := FinalWorld.handle_and_close_compatible γ
  apply CMRA.valid_iff_validN.mpr
  intro k
  have hk := CMRA.validN_of_valid h k
  rw [CMRA.op_comm] at hk
  exact CMRA.validN_op_left hk

theorem close_wsat (c : OpenCertificate n w E N γ P)
    (permit : RestorationPermit c) :
    WSatAt n (closeName (openName w N) N) := by
  refine ⟨permit.opened_wsat.1, ?_⟩
  intro K hclosed hopened
  rcases hclosed with hclosed | hKN
  · exact permit.opened_wsat.2 K hclosed hopened.1
  · exact hopened.2 hKN

theorem close_restores_world (c : OpenCertificate n w E N γ P)
    (_permit : RestorationPermit c) :
    closeName (openName w N) N = w := by
  have hClosed : Mask.insert (Mask.erase w.closed N) N = w.closed :=
    Mask.insert_erase_cancel c.closed
  have hOpened : Mask.erase (Mask.insert w.opened N) N = w.opened := by
    rw [Mask.erase_insert_cancel,
      WorldInvariantProtocol.erase_absent c.not_opened]
  cases w
  simp only [openName, closeName] at hClosed hOpened ⊢
  simp only [hClosed, hOpened]

theorem close_restores_mask (c : OpenCertificate n w E N γ P)
    (permit : RestorationPermit c) :
    (closeName (openName w N) N).closed = E := by
  rw [c.close_restores_world permit, ← c.mask_eq]

theorem close_permission_linear (c : OpenCertificate n w E N γ P) :
    ¬ CMRA.valid
      (CMRA.op (FinalWorld.closeSlot γ) (FinalWorld.closeSlot γ)) :=
  FinalWorld.close_conflict γ

theorem restoration_not_plain (c : OpenCertificate n w E N γ P) :
    ¬ CertifiedFancyUpdate.Admissible (Mask.without E N) E := by
  intro h
  exact Mask.without_excludes_prefix E (Namespace.prefix_refl N)
    (h N c.enabled)

end OpenCertificate
end FinalWorldInvariantProtocol
end LeanIrisX
