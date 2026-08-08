import LeanIrisX.Algebra.CMRA

/-! Derived total-core operations for unital cameras. -/

namespace LeanIrisX.CMRA

variable {M : Type u} [OFE M] [CMRA M] [UCMRA M]

theorem pcore_total (x : M) : ∃ cx, CMRA.pcore x = some cx := by
  obtain ⟨cy, hcy⟩ := CMRA.pcore_op_mono (x := (UCMRA.unit : M))
    (cx := UCMRA.unit) UCMRA.pcore_unit x
  refine ⟨CMRA.op UCMRA.unit cy, ?_⟩
  simpa [UCMRA.unit_left] using hcy

/-- The total core induced by the unit of a UCMRA. -/
def core (x : M) : M := (CMRA.pcore x).getD x

theorem pcore_core (x : M) : CMRA.pcore x = some (core x) := by
  unfold core
  obtain ⟨cx, hcx⟩ := pcore_total x
  simp [hcx]

theorem core_ne {n : Nat} {x y : M} (hxy : x ≡{n}≡ y) :
    core x ≡{n}≡ core y := by
  obtain ⟨cy, hcy, hd⟩ := CMRA.pcore_ne hxy (pcore_core x)
  have : cy = core y := Option.some.inj (hcy.symm.trans (pcore_core y))
  subst cy
  exact hd

theorem core_op (x : M) : CMRA.op (core x) x = x :=
  CMRA.pcore_op_left (pcore_core x)

theorem core_validN {n : Nat} {x : M} (hx : CMRA.validN n x) :
    CMRA.validN n (core x) := by
  apply CMRA.validN_op_left (x := core x) (y := x)
  simpa [core_op] using hx

theorem core_idem (x : M) : core (core x) = core x := by
  have h₁ := CMRA.pcore_idem (pcore_core x)
  exact Option.some.inj ((pcore_core (core x)).symm.trans h₁)

theorem core_includedN_core {n : Nat} {x y : M}
    (hxy : CMRA.IncludedN n x y) :
    CMRA.IncludedN n (core x) (core y) := by
  obtain ⟨z, hy⟩ := hxy
  obtain ⟨cz, hcz⟩ := CMRA.pcore_op_mono (pcore_core x) z
  obtain ⟨cy, hcy, hdist⟩ := CMRA.pcore_ne (OFE.symm hy) hcz
  have hcyEq : cy = core y := by
    exact Option.some.inj (hcy.symm.trans (pcore_core y))
  subst cy
  exact ⟨cz, OFE.symm hdist⟩

end LeanIrisX.CMRA
