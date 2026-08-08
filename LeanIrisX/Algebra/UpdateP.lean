import LeanIrisX.Algebra.ViewUpdate

/-! Predicate-valued frame-preserving camera updates. -/

namespace LeanIrisX.CMRA

variable {M : Type u} [OFE M] [CMRA M]

/-- A frame-preserving update whose result may be chosen from `P`. -/
def FramePreservingUpdateP (x : M) (P : M → Prop) : Prop :=
  ∀ n frame, CMRA.validN n (opFrame x frame) →
    ∃ y, P y ∧ CMRA.validN n (opFrame y frame)

theorem updateP_refl (x : M) : FramePreservingUpdateP x (fun y => y = x) := by
  intro n frame h
  exact ⟨x, rfl, h⟩

theorem update_to_updateP {x y : M} (h : x ~~> y) :
    FramePreservingUpdateP x (fun z => z = y) := by
  intro n frame hv
  exact ⟨y, rfl, h n frame hv⟩

theorem updateP_mono {x : M} {P Q : M → Prop}
    (h : FramePreservingUpdateP x P) (hpq : ∀ y, P y → Q y) :
    FramePreservingUpdateP x Q := by
  intro n frame hv
  obtain ⟨y, hy, hvy⟩ := h n frame hv
  exact ⟨y, hpq y hy, hvy⟩

theorem updateP_preserves_validN {x : M} {P : M → Prop}
    (h : FramePreservingUpdateP x P) {n : Nat} (hv : CMRA.validN n x) :
    ∃ y, P y ∧ CMRA.validN n y := by
  exact h n none hv

theorem updateP_trans {x : M} {P Q : M → Prop}
    (h : FramePreservingUpdateP x P)
    (hnext : ∀ y, P y → FramePreservingUpdateP y Q) :
    FramePreservingUpdateP x Q := by
  intro n frame hv
  obtain ⟨y, hy, hvy⟩ := h n frame hv
  exact hnext y hy n frame hvy

/-- For a unital camera it suffices to check ordinary frames. -/
theorem updateP_of_total [UCMRA M] {x : M} {P : M → Prop}
    (h : ∀ n frame, CMRA.validN n (CMRA.op x frame) →
      ∃ y, P y ∧ CMRA.validN n (CMRA.op y frame)) :
    FramePreservingUpdateP x P := by
  intro n frame hv
  cases frame with
  | none =>
      change CMRA.validN n x at hv
      have hv' : CMRA.validN n (CMRA.op x UCMRA.unit) := by
        rw [UCMRA.unit_right]
        exact hv
      obtain ⟨y, hy, hvy⟩ := h n UCMRA.unit hv'
      exact ⟨y, hy, CMRA.validN_op_left hvy⟩
  | some frame => exact h n frame hv

end LeanIrisX.CMRA

namespace LeanIrisX.View

variable {A : Type u} {B : Type v}
variable [OFE A] [OFE B] [CMRA B] [UCMRA B]
variable {R : ViewRel A B} [IsViewRel R]

/-- Predicate-valued update for a full authority and fragment pair. -/
theorem full_auth_frag_updateP {a : A} {b : B} (P : A → B → Prop)
    (hup : ∀ n frame, R n a (CMRA.op b frame) →
      ∃ a' b', P a' b' ∧ R n a' (CMRA.op b' frame)) :
    CMRA.FramePreservingUpdateP
      (op (FullAuth (R := R) a) (Frag (R := R) b))
      (fun target => ∃ a' b', P a' b' ∧
        target = op (FullAuth (R := R) a') (Frag (R := R) b')) := by
  apply CMRA.updateP_of_total
  intro n frame hvalid
  cases frame with
  | mk fa ff =>
    cases fa with
    | none =>
      change ValidN n
        (op (op (FullAuth (R := R) a) (Frag (R := R) b))
          (Frag (R := R) ff)) at hvalid
      rw [← op_assoc] at hvalid
      have hs : R n a (CMRA.op b ff) := by
        exact (auth_one_frag_validN_iff n a (CMRA.op b ff)).mp hvalid
      obtain ⟨a', b', hp, hs'⟩ := hup n ff hs
      refine ⟨op (FullAuth (R := R) a') (Frag (R := R) b'), ?_, ?_⟩
      · exact ⟨a', b', hp, rfl⟩
      · change ValidN n
          (op (op (FullAuth (R := R) a') (Frag (R := R) b'))
            (Frag (R := R) ff))
        rw [← op_assoc]
        exact (auth_one_frag_validN_iff n a' (CMRA.op b' ff)).mpr hs'
    | some fa =>
      rcases fa with ⟨dq, ag⟩
      have hdq : CMRA.validN n (CMRA.op (DFrac.own DFrac.one) dq) := hvalid.1
      exact False.elim (DFrac.full_op_invalidN n dq hdq)

end LeanIrisX.View
