import LeanIrisX.Algebra.TotalCore
import LeanIrisX.Logic.Mask

/-!
An Iris-style disjoint-set resource for masks.

`MaskToken` records, for every namespace, how many owners claim it.  Composition
adds multiplicities and validity requires every multiplicity to be at most one.
Consequently two overlapping mask tokens compose to an invalid resource, while
disjoint masks can be split and recombined.  This is the resource algebra needed
for the enabled/disabled-name ownership used by `wsat`.
-/

namespace LeanIrisX

structure MaskToken where
  count : Namespace → Nat

namespace MaskToken

attribute [local instance] Classical.propDecidable

@[ext]
theorem ext {x y : MaskToken} (h : ∀ N, x.count N = y.count N) : x = y := by
  cases x
  cases y
  congr
  funext N
  exact h N

instance : OFE MaskToken := OFE.ofDiscrete MaskToken
instance : OFE.Discrete MaskToken where
  eq_of_dist h := h

def zero : MaskToken := ⟨fun _ => 0⟩
def op (x y : MaskToken) : MaskToken := ⟨fun N => x.count N + y.count N⟩
def Valid (x : MaskToken) : Prop := ∀ N, x.count N ≤ 1

noncomputable def ofMask (E : Mask) : MaskToken :=
  ⟨fun N => if E N then 1 else 0⟩

theorem op_assoc (x y z : MaskToken) : op x (op y z) = op (op x y) z := by
  ext N
  exact Nat.add_assoc _ _ _ |>.symm

theorem op_comm (x y : MaskToken) : op x y = op y x := by
  ext N
  exact Nat.add_comm _ _

instance instCMRA : CMRA MaskToken where
  pcore _ := some zero
  op := op
  validN _ x := Valid x
  valid := Valid
  op_ne _ := by
    intro n x y h
    subst y
    exact OFE.refl n _
  pcore_ne := by
    intro n x y cx hxy hx
    change some zero = some cx at hx
    injection hx with hx
    subst cx
    exact ⟨zero, rfl, OFE.refl n zero⟩
  pcore_none_ne := by
    intro n x y hxy h
    contradiction
  validN_ne := by
    intro n x y hxy hx
    subst y
    exact hx
  valid_iff_validN := by simp
  validN_succ := by simp
  validN_op_left := by
    intro n x y h N
    exact Nat.le_trans (Nat.le_add_right _ _) (h N)
  assoc := op_assoc
  comm := op_comm
  pcore_op_left := by
    intro x cx h
    change some zero = some cx at h
    injection h with h
    subst cx
    ext N
    exact Nat.zero_add _
  pcore_idem := by
    intro x cx h
    change some zero = some cx at h
    injection h with h
    subst cx
    rfl
  pcore_op_mono := by
    intro x cx hx y
    change some zero = some cx at hx
    injection hx with hx
    subst cx
    exact ⟨zero, rfl⟩
  extend := by
    intro n x y₁ y₂ hx hdist
    have heq : x = op y₁ y₂ := hdist
    exact {
      left := y₁
      right := y₂
      decompose := heq
      left_dist := OFE.refl n y₁
      right_dist := OFE.refl n y₂
    }

instance instUCMRA : UCMRA MaskToken where
  unit := zero
  unit_valid := by intro N; exact Nat.zero_le 1
  unit_left := by
    intro x
    ext N
    exact Nat.zero_add _
  pcore_unit := rfl

instance instTotalCore : TotalCore MaskToken where
  core _ := zero
  core_spec _ := rfl

theorem ofMask_count (E : Mask) (N : Namespace) :
    (ofMask E).count N = if E N then 1 else 0 := rfl

theorem ofMask_valid (E : Mask) : CMRA.valid (ofMask E) := by
  intro N
  simp only [ofMask]
  split <;> omega

theorem ofMask_empty : ofMask Mask.empty = zero := by
  ext N
  simp [ofMask, Mask.empty, zero]

theorem ofMask_op_valid_iff_disjoint (E F : Mask) :
    CMRA.valid (CMRA.op (ofMask E) (ofMask F)) ↔ Mask.Disjoint E F := by
  constructor
  · intro h N hE hF
    have := h N
    simp [CMRA.op, op, ofMask, hE, hF] at this
  · intro h N
    by_cases hE : E N
    · have hF : ¬ F N := by
        intro hFN
        exact h N hE hFN
      simp [CMRA.op, op, ofMask, hE, hF]
    · by_cases hF : F N <;>
        simp [CMRA.op, op, ofMask, hE, hF]

theorem ofMask_union (E F : Mask) (h : Mask.Disjoint E F) :
    ofMask (Mask.union E F) = CMRA.op (ofMask E) (ofMask F) := by
  ext N
  by_cases hE : E N
  · have hF : ¬ F N := by
      intro hFN
      exact h N hE hFN
    simp [ofMask, Mask.union, CMRA.op, op, hE, hF]
  · by_cases hF : F N <;>
      simp [ofMask, Mask.union, CMRA.op, op, hE, hF]

theorem singleton_conflict (N : Namespace) :
    ¬ CMRA.valid (CMRA.op (ofMask (Mask.singleton N))
      (ofMask (Mask.singleton N))) := by
  intro h
  have := h N
  simp [CMRA.op, op, ofMask, Mask.singleton] at this

end MaskToken
end LeanIrisX
