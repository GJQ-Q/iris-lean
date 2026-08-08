import LeanIrisX.Algebra.View
import LeanIrisX.Algebra.Update

/-! Frame-preserving updates for full authoritative Views. -/

namespace LeanIrisX.View

variable {A : Type u} {B : Type v}
variable [OFE A] [OFE B] [CMRA B] [UCMRA B]
variable {R : ViewRel A B} [IsViewRel R]

abbrev FullAuth (a : A) : View R := Auth (DFrac.own DFrac.one) a

omit [IsViewRel R] in
private theorem auth_frag_frag (a : A) (b frame : B) :
    op (op (FullAuth (R := R) a) (Frag (R := R) b)) (Frag (R := R) frame) =
      op (FullAuth (R := R) a) (Frag (R := R) (CMRA.op b frame)) := by
  rw [← op_assoc]
  rfl

omit [IsViewRel R] in
private theorem auth_frag_unit (a : A) :
    op (FullAuth (R := R) a) (Frag (R := R) UCMRA.unit) =
      FullAuth (R := R) a := by
  rw [op_comm]
  exact unit_left _

theorem full_auth_frag_update {a a' : A} {b b' : B}
    (hup : ∀ n frame,
      R n a (CMRA.op b frame) → R n a' (CMRA.op b' frame)) :
    CMRA.FramePreservingUpdate
      (op (FullAuth (R := R) a) (Frag (R := R) b))
      (op (FullAuth (R := R) a') (Frag (R := R) b')) := by
  apply CMRA.update_of_total
  intro n frame hvalid
  cases frame with
  | mk fa ff =>
    cases fa with
    | none =>
      change ValidN n
        (op (op (FullAuth (R := R) a) (Frag (R := R) b))
          (Frag (R := R) ff)) at hvalid
      rw [auth_frag_frag] at hvalid
      have hs : R n a (CMRA.op b ff) := by
        apply (auth_one_frag_validN_iff n a (CMRA.op b ff)).mp
        exact hvalid
      have hvTarget :
          ValidN n (op (FullAuth (R := R) a')
            (Frag (R := R) (CMRA.op b' ff))) :=
        (auth_one_frag_validN_iff n a' (CMRA.op b' ff)).mpr (hup n ff hs)
      change ValidN n
        (op (op (FullAuth (R := R) a') (Frag (R := R) b'))
          (Frag (R := R) ff))
      rw [auth_frag_frag]
      exact hvTarget
    | some fa =>
      rcases fa with ⟨dq, ag⟩
      have hdq : CMRA.validN n (CMRA.op (DFrac.own DFrac.one) dq) := hvalid.1
      exact False.elim (DFrac.full_op_invalidN n dq hdq)

theorem full_auth_update {a a' : A}
    (hup : ∀ n frame, R n a frame → R n a' frame) :
    CMRA.FramePreservingUpdate (FullAuth (R := R) a) (FullAuth (R := R) a') := by
  apply CMRA.update_congr (auth_frag_unit (R := R) a)
    (auth_frag_unit (R := R) a')
  exact full_auth_frag_update (R := R) (a := a) (a' := a')
      (b := UCMRA.unit) (b' := UCMRA.unit) (fun n frame h => by
        have hs : R n a frame := by simpa [UCMRA.unit_left] using h
        simpa [UCMRA.unit_left] using hup n frame hs)

theorem full_auth_alloc {a a' : A} {b : B}
    (hup : ∀ n frame, R n a frame → R n a' (CMRA.op b frame)) :
    CMRA.FramePreservingUpdate
      (FullAuth (R := R) a)
      (op (FullAuth (R := R) a') (Frag (R := R) b)) := by
  apply CMRA.update_congr (auth_frag_unit (R := R) a) rfl
  exact full_auth_frag_update (R := R) (a := a) (a' := a')
      (b := UCMRA.unit) (b' := b) (fun n frame h =>
        hup n frame (by simpa [UCMRA.unit_left] using h))

theorem full_auth_dealloc {a a' : A} {b : B}
    (hup : ∀ n frame, R n a (CMRA.op b frame) → R n a' frame) :
    CMRA.FramePreservingUpdate
      (op (FullAuth (R := R) a) (Frag (R := R) b))
      (FullAuth (R := R) a') := by
  apply CMRA.update_congr rfl (auth_frag_unit (R := R) a')
  exact full_auth_frag_update (R := R) (a := a) (a' := a')
      (b := b) (b' := UCMRA.unit) (fun n frame h => by
        simpa [UCMRA.unit_left] using hup n frame h)

end LeanIrisX.View
