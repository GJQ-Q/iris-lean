import LeanIrisX.Algebra.UpdateP

/-! Local updates, aligned with the official Iris definition. -/

namespace LeanIrisX.CMRA

variable {M : Type u} [OFE M] [CMRA M]

/--
`LocalUpdate (x₁,x₂) (y₁,y₂)` preserves both validity of the first component
and its step-indexed decomposition through the second component and any
optional frame.
-/
def LocalUpdate (x y : M × M) : Prop :=
  ∀ n frame, CMRA.validN n x.1 →
    OFE.dist n x.1 (opFrame x.2 frame) →
    CMRA.validN n y.1 ∧ OFE.dist n y.1 (opFrame y.2 frame)

infixr:40 " ~l~> " => LocalUpdate

theorem localUpdate_refl (x : M × M) : x ~l~> x := by
  intro n frame hv heq
  exact ⟨hv, heq⟩

theorem localUpdate_trans {x y z : M × M}
    (hxy : x ~l~> y) (hyz : y ~l~> z) : x ~l~> z := by
  intro n frame hv heq
  obtain ⟨hvy, hey⟩ := hxy n frame hv heq
  exact hyz n frame hvy hey

theorem localUpdate_congr {x x' y y' : M × M}
    (hx : x = x') (hy : y = y') (h : x ~l~> y) : x' ~l~> y' := by
  subst x'
  subst y'
  exact h

/-- Official unital characterization: an ordinary frame suffices in a UCMRA. -/
theorem localUpdate_iff_total [UCMRA M] {x y : M × M} :
    x ~l~> y ↔
      ∀ n frame, CMRA.validN n x.1 →
        OFE.dist n x.1 (CMRA.op x.2 frame) →
        CMRA.validN n y.1 ∧ OFE.dist n y.1 (CMRA.op y.2 frame) := by
  constructor
  · intro h n frame hv heq
    exact h n (some frame) hv heq
  · intro h n frame hv heq
    cases frame with
    | none =>
        have hx : OFE.dist n x.1 (CMRA.op x.2 UCMRA.unit) :=
          OFE.trans heq (OFE.of_eq (UCMRA.unit_right x.2).symm)
        obtain ⟨hvy, hy⟩ := h n UCMRA.unit hv hx
        exact ⟨hvy, OFE.trans hy (OFE.of_eq (UCMRA.unit_right y.2))⟩
    | some frame => exact h n frame hv heq

theorem localUpdate_unit (x y : Unit × Unit) : x ~l~> y := by
  intro n frame hv heq
  exact ⟨trivial, OFE.refl n ()⟩

end LeanIrisX.CMRA
