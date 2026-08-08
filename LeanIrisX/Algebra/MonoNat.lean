import LeanIrisX.Algebra.Auth

/-! A practical monotone-natural ghost resource based on the max camera. -/

namespace LeanIrisX

structure MonoNat where
  val : Nat
deriving DecidableEq, Repr

namespace MonoNat

def ofNat (n : Nat) : MonoNat := ⟨n⟩
def op (x y : MonoNat) : MonoNat := ⟨Nat.max x.val y.val⟩

instance : OFE MonoNat := OFE.ofDiscrete MonoNat
instance : OFE.Discrete MonoNat := ⟨fun h => h⟩

instance instCMRA : CMRA MonoNat where
  pcore x := some x
  op := op
  validN _ _ := True
  valid _ := True
  op_ne x := by
    intro n y1 y2 h
    subst y2
    exact OFE.refl n _
  pcore_ne := by
    intro n x y cx hxy hcore
    cases hcore
    exact ⟨y, rfl, hxy⟩
  pcore_none_ne := by intro n x y hxy h; contradiction
  validN_ne := by intro n x y hxy hv; trivial
  valid_iff_validN := by
    intro x
    constructor
    · intro h n; trivial
    · intro h; trivial
  validN_succ := by intro n x h; trivial
  validN_op_left := by intro n x y h; trivial
  assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    simp [op, Nat.max_assoc]
  comm := by
    rintro ⟨x⟩ ⟨y⟩
    simp [op, Nat.max_comm]
  pcore_op_left := by
    intro x cx h
    cases h
    cases x
    simp [op]
  pcore_idem := by intro x cx h; cases h; rfl
  pcore_op_mono := by
    intro x cx h y
    cases h
    exact ⟨y, rfl⟩
  extend := by
    intro n x y1 y2 hv hdist
    exact {
      left := y1
      right := y2
      decompose := hdist
      left_dist := OFE.refl n y1
      right_dist := OFE.refl n y2
    }

instance instUCMRA : UCMRA MonoNat where
  unit := ofNat 0
  unit_valid := trivial
  unit_left := by
    rintro ⟨x⟩
    change op (ofNat 0) ⟨x⟩ = ⟨x⟩
    simp [ofNat, op]
  pcore_unit := rfl

private theorem cmraOp_eq (x y : MonoNat) : CMRA.op x y = op x y := rfl

theorem includedN_iff_le {n : Nat} {x y : MonoNat} :
    CMRA.IncludedN n x y ↔ x.val ≤ y.val := by
  constructor
  · rintro ⟨z, h⟩
    have heq : y = CMRA.op x z := OFE.Discrete.eq_of_dist h
    rw [cmraOp_eq] at heq
    have hmax : y.val = Nat.max x.val z.val := congrArg MonoNat.val heq
    rw [hmax]
    exact Nat.le_max_left _ _
  · intro hxy
    refine ⟨y, ?_⟩
    apply OFE.of_eq
    rw [cmraOp_eq]
    cases x with
    | mk xv =>
      cases y with
      | mk yv => simp [op, Nat.max_eq_right hxy]

theorem included_iff_le {x y : MonoNat} :
    CMRA.Included x y ↔ x.val ≤ y.val := by
  constructor
  · rintro ⟨z, h⟩
    rw [h, cmraOp_eq]
    exact Nat.le_max_left _ _
  · intro hxy
    refine ⟨y, ?_⟩
    rw [cmraOp_eq]
    cases x with
    | mk xv =>
      cases y with
      | mk yv => simp [op, Nat.max_eq_right hxy]

end MonoNat

namespace MonoNatGhost

abbrev Ghost := Auth MonoNat

def authoritative (n : Nat) : Ghost := Auth.authoritative (MonoNat.ofNat n)
def fragment (n : Nat) : Ghost := Auth.fragment (MonoNat.ofNat n)

theorem fragment_le_authority {n k m : Nat}
    (h : CMRA.validN n (CMRA.op (authoritative k) (fragment m))) : m ≤ k := by
  exact MonoNat.includedN_iff_le.mp (Auth.fragment_includedN h)

theorem authoritative_grow {k m : Nat} (hkm : k ≤ m) :
    CMRA.FramePreservingUpdate (authoritative k) (authoritative m) := by
  apply Auth.authoritative_update
  intro n frame hrel
  constructor
  · trivial
  · apply MonoNat.includedN_iff_le.mpr
    exact Nat.le_trans (MonoNat.includedN_iff_le.mp hrel.2) hkm

/-- Allocate a lower-bound fragment from an existing authority. -/
theorem allocate_fragment {k m : Nat} (hmk : m ≤ k) :
    CMRA.FramePreservingUpdate
      (authoritative k)
      (CMRA.op (authoritative k) (fragment m)) := by
  apply Auth.alloc_fragment
  intro n frame hrel
  constructor
  · trivial
  · apply MonoNat.includedN_iff_le.mpr
    exact Nat.max_le.mpr ⟨hmk, MonoNat.includedN_iff_le.mp hrel.2⟩

/-- Grow the authority and simultaneously issue a fragment for the new value. -/
theorem grow_and_allocate {k m : Nat} (hkm : k ≤ m) :
    CMRA.FramePreservingUpdate
      (authoritative k)
      (CMRA.op (authoritative m) (fragment m)) := by
  apply Auth.alloc_fragment
  intro n frame hrel
  constructor
  · trivial
  · apply MonoNat.includedN_iff_le.mpr
    exact Nat.max_le.mpr ⟨Nat.le_refl m,
      Nat.le_trans (MonoNat.includedN_iff_le.mp hrel.2) hkm⟩

end MonoNatGhost

end LeanIrisX
