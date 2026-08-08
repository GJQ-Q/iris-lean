import LeanIrisX.Algebra.CMRA

namespace LeanIrisX

/-- Cameras whose partial core is defined for every element. -/
class TotalCore (A : Type u) [OFE A] [CMRA A] where
  core : A → A
  core_spec : ∀ a, CMRA.pcore a = some (core a)

namespace TotalCore

variable {A : Type u} [OFE A] [CMRA A] [TotalCore A]

theorem nonExpansive : NonExpansive (TotalCore.core : A → A) := by
  intro n x y hxy
  obtain ⟨cy, hcy, hdist⟩ :=
    CMRA.pcore_ne hxy (TotalCore.core_spec x)
  rw [TotalCore.core_spec y] at hcy
  cases hcy
  exact hdist

theorem op_left (a : A) : CMRA.op (TotalCore.core a) a = a :=
  CMRA.pcore_op_left (TotalCore.core_spec a)

theorem idem (a : A) : TotalCore.core (TotalCore.core a) = TotalCore.core a := by
  have h := CMRA.pcore_idem (TotalCore.core_spec a)
  rw [TotalCore.core_spec] at h
  exact Option.some.inj h

end TotalCore

instance : TotalCore Unit where
  core _ := ()
  core_spec _ := rfl

end LeanIrisX
