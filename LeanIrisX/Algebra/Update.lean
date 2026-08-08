import LeanIrisX.Algebra.Core
import LeanIrisX.Algebra.Exclusive

namespace LeanIrisX.CMRA

variable {M : Type u} [OFE M] [CMRA M]

/-- Compose a camera element with an optional frame. `none` means no frame. -/
def opFrame (x : M) : Option M → M
  | none => x
  | some frame => CMRA.op x frame

/-- Deterministic frame-preserving camera update. -/
def FramePreservingUpdate (x y : M) : Prop :=
  ∀ n frame, CMRA.validN n (opFrame x frame) →
    CMRA.validN n (opFrame y frame)

infix:40 " ~~> " => FramePreservingUpdate

theorem update_refl (x : M) : x ~~> x := by
  intro n frame h; exact h

theorem update_trans {x y z : M} (hxy : x ~~> y) (hyz : y ~~> z) :
    x ~~> z := by
  intro n frame h
  exact hyz n frame (hxy n frame h)

theorem update_congr {x x' y y' : M} (hx : x = x') (hy : y = y')
    (h : x ~~> y) : x' ~~> y' := by
  subst x'
  subst y'
  exact h

theorem update_preserves_validN {x y : M} (h : x ~~> y) {n : Nat}
    (hv : CMRA.validN n x) : CMRA.validN n y := by
  exact h n none hv

/-- For a unital camera it suffices to check ordinary frames. -/
theorem update_of_total [UCMRA M] {x y : M}
    (h : ∀ n frame, CMRA.validN n (CMRA.op x frame) →
      CMRA.validN n (CMRA.op y frame)) : x ~~> y := by
  intro n frame hv
  cases frame with
  | none =>
      change CMRA.validN n x at hv
      have hv' : CMRA.validN n (CMRA.op x UCMRA.unit) := by
        rw [UCMRA.unit_right]
        exact hv
      exact CMRA.validN_op_left (h n UCMRA.unit hv')
  | some frame => exact h n frame hv

end LeanIrisX.CMRA

namespace LeanIrisX.Excl

theorem update_own (a b : α) :
    CMRA.FramePreservingUpdate (own a : Excl α) (own b) := by
  intro n frame h
  cases frame with
  | none => trivial
  | some frame =>
      cases frame with
      | unit => trivial
      | own c => exact False.elim h
      | invalid => exact False.elim h

end LeanIrisX.Excl
