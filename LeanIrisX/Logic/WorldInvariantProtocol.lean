import LeanIrisX.Logic.RecursiveWorld
import LeanIrisX.Logic.WorldTransition
import LeanIrisX.Logic.CertifiedFancyUpdate

/-!
# World/invariant transition protocol

This module connects four pieces that were previously separate: world
satisfaction, opening and closing a registered name, mask removal, and the
certificate needed to restore that mask.  The certificate is deliberately an
explicit protocol object; ordinary `CertifiedFancyUpdate.Admissible` cannot
justify restoration, because restoration is a genuine mask enlargement.
-/

namespace LeanIrisX
namespace WorldInvariantProtocol

/-- `N` is a leaf of `E`: no proper descendant of `N` is enabled.  This is the
condition under which exact-name world removal agrees with hierarchical Iris
mask removal. -/
def LeafAt (E : Mask) (N : Namespace) : Prop :=
  ∀ K, Namespace.Prefix N K → E K → K = N

theorem erase_eq_without {E : Mask} {N : Namespace} (hLeaf : LeafAt E N) :
    Mask.erase E N = Mask.without E N := by
  funext K
  apply propext
  constructor
  · intro h
    exact ⟨h.1, fun hPrefix => h.2 (hLeaf K hPrefix h.1)⟩
  · intro h
    exact ⟨h.1, fun hKN => h.2 (hKN ▸ Namespace.prefix_refl N)⟩

theorem erase_absent {E : Mask} {N : Namespace} (hN : ¬ E N) :
    Mask.erase E N = E := by
  funext K
  apply propext
  constructor
  · exact fun h => h.1
  · intro hK
    exact ⟨hK, fun hKN => hN (hKN ▸ hK)⟩

/-- Evidence required to open an invariant name in a satisfied recursive
world.  `mask_eq` connects the logical mask to the world's closed-name set. -/
structure OpenCertificate (n : Nat) (w : WorldIris.World)
    (E : Mask) (N : Namespace) : Prop where
  wsat : WorldIris.WSatAt n w
  mask_eq : E = w.closed
  enabled : E N
  leaf : LeafAt E N

namespace OpenCertificate

variable {n : Nat} {w : WorldIris.World} {E : Mask} {N : Namespace}

theorem closed (c : OpenCertificate n w E N) : w.closed N :=
  c.mask_eq ▸ c.enabled

theorem not_opened (c : OpenCertificate n w E N) : ¬ w.opened N :=
  fun ho => c.wsat.2.2 N c.closed ho

theorem opened_wsat (c : OpenCertificate n w E N) :
    WorldIris.WSatAt n (WorldIris.openName w N) := by
  exact ⟨c.wsat.1, WorldTransition.partition_open c.wsat.2 c.closed⟩

theorem opened_mask (c : OpenCertificate n w E N) :
    (WorldIris.openName w N).closed = Mask.without E N := by
  change Mask.erase w.closed N = Mask.without E N
  rw [← c.mask_eq, erase_eq_without c.leaf]

theorem shrink_is_admissible (_c : OpenCertificate n w E N) :
    CertifiedFancyUpdate.Admissible E (Mask.without E N) :=
  Mask.without_subset E N

/-- The restoration permit produced by opening.  It remembers the original
world and mask, so closing can be checked rather than postulated. -/
structure RestorationPermit (n : Nat) (w : WorldIris.World)
    (E : Mask) (N : Namespace) : Prop where
  source : OpenCertificate n w E N
  opened_wsat : WorldIris.WSatAt n (WorldIris.openName w N)
  opened_name : (WorldIris.openName w N).opened N
  original_not_opened : ¬ w.opened N

theorem restorationPermit (c : OpenCertificate n w E N) :
    RestorationPermit n w E N :=
  ⟨c, c.opened_wsat, Mask.insert_self _ _, c.not_opened⟩

theorem close_wsat (permit : RestorationPermit n w E N) :
    WorldIris.WSatAt n (WorldIris.closeName (WorldIris.openName w N) N) := by
  exact ⟨permit.opened_wsat.1,
    WorldTransition.partition_close permit.opened_wsat.2 permit.opened_name⟩

theorem close_restores_world (c : OpenCertificate n w E N)
    (_permit : RestorationPermit n w E N) :
    WorldIris.closeName (WorldIris.openName w N) N = w := by
  have hClosed : Mask.insert (Mask.erase w.closed N) N = w.closed :=
    Mask.insert_erase_cancel c.closed
  have hOpened : Mask.erase (Mask.insert w.opened N) N = w.opened := by
    rw [Mask.erase_insert_cancel, erase_absent c.not_opened]
  cases w
  simp only [WorldIris.openName, WorldIris.closeName] at hClosed hOpened ⊢
  simp only [hClosed, hOpened]

theorem close_restores_mask (c : OpenCertificate n w E N)
    (permit : RestorationPermit n w E N) :
    (WorldIris.closeName (WorldIris.openName w N) N).closed = E := by
  rw [c.close_restores_world permit, c.mask_eq]

/-- Restoration is intentionally not a plain shrinking transition when `N`
is enabled.  The permit above is therefore semantically necessary. -/
theorem restoration_not_plain (c : OpenCertificate n w E N) :
    ¬ CertifiedFancyUpdate.Admissible (Mask.without E N) E := by
  intro h
  exact Mask.without_excludes_prefix E (Namespace.prefix_refl N)
    (h N c.enabled)

end OpenCertificate
end WorldInvariantProtocol
end LeanIrisX
