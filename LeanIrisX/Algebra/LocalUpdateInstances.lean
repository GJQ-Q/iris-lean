import LeanIrisX.Algebra.LocalUpdate
import LeanIrisX.Algebra.Product
import LeanIrisX.Algebra.Option

/-! Reusable local-update lifting rules for product and option cameras. -/

namespace LeanIrisX.CMRA

variable {A : Type u} {B : Type v}
variable [OFE A] [CMRA A] [OFE B] [CMRA B]

theorem localUpdate_prod {x y x' y' : A × B}
    (hl : LocalUpdate (x.1, y.1) (x'.1, y'.1))
    (hr : LocalUpdate (x.2, y.2) (x'.2, y'.2)) :
    LocalUpdate (x, y) (x', y') := by
  intro n frame hv heq
  cases frame with
  | none =>
      obtain ⟨hvl, hel⟩ := hl n none hv.1 heq.1
      obtain ⟨hvr, her⟩ := hr n none hv.2 heq.2
      exact ⟨⟨hvl, hvr⟩, ⟨hel, her⟩⟩
  | some frame =>
      obtain ⟨hvl, hel⟩ := hl n (some frame.1) hv.1 heq.1
      obtain ⟨hvr, her⟩ := hr n (some frame.2) hv.2 heq.2
      exact ⟨⟨hvl, hvr⟩, ⟨hel, her⟩⟩

theorem localUpdate_prod_mk
    {x1 y1 x1' y1' : A} {x2 y2 x2' y2' : B}
    (hl : LocalUpdate (x1, y1) (x1', y1'))
    (hr : LocalUpdate (x2, y2) (x2', y2')) :
    LocalUpdate ((x1, x2), (y1, y2)) ((x1', x2'), (y1', y2')) :=
  localUpdate_prod hl hr

variable {M : Type u} [OFE M] [CMRA M]

theorem localUpdate_option {x y x' y' : M}
    (h : LocalUpdate (x, y) (x', y')) :
    LocalUpdate (some x, some y) (some x', some y') := by
  intro n frame hv heq
  cases frame with
  | none => exact h n none hv heq
  | some frame =>
      cases frame with
      | none => exact h n none hv heq
      | some z => exact h n (some z) hv heq

/-- Allocate a valid element into an absent Option resource. -/
theorem localUpdate_alloc_option (x : M) (y : Option M)
    (hx : CMRA.valid x) :
    LocalUpdate (none, y) (some x, some x) := by
  intro n frame hv heq
  cases frame with
  | none => exact ⟨CMRA.validN_of_valid hx n, OFE.refl n (some x)⟩
  | some frame =>
      cases frame with
      | none => exact ⟨CMRA.validN_of_valid hx n, OFE.refl n (some x)⟩
      | some z =>
          cases y <;> exact False.elim heq

end LeanIrisX.CMRA
