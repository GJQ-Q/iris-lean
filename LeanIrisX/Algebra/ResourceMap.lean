import LeanIrisX.Algebra.TotalCore

/-! Pointwise cameras indexed by an arbitrary key type. -/

namespace LeanIrisX

abbrev ResourceMap (K : Type v) (A : Type u) := K → A

namespace ResourceMap

variable {K : Type v} {A : Type u}
variable [OFE A] [CMRA A] [UCMRA A] [TotalCore A]

instance : CMRA (ResourceMap K A) where
  pcore x := some (fun k => TotalCore.core (x k))
  op x y k := CMRA.op (x k) (y k)
  validN n x := ∀ k, CMRA.validN n (x k)
  valid x := ∀ k, CMRA.valid (x k)
  op_ne x := by intro n y₁ y₂ h k; exact CMRA.op_ne_right (x k) n (h k)
  pcore_ne := by
    intro n x y cx hxy hcx
    change some (fun k => TotalCore.core (x k)) = some cx at hcx
    have hcx' := Option.some.inj hcx
    subst cx
    exact ⟨fun k => TotalCore.core (y k), rfl,
      fun k => TotalCore.nonExpansive n (hxy k)⟩
  pcore_none_ne := by intro n x y h hnone; contradiction
  validN_ne := by intro n x y hxy hx k; exact CMRA.validN_ne (hxy k) (hx k)
  valid_iff_validN := by
    intro x
    change (∀ k, CMRA.valid (x k)) ↔ ∀ n k, CMRA.validN n (x k)
    constructor
    · intro h n k; exact CMRA.validN_of_valid (h k) n
    · intro h k; exact CMRA.valid_iff_validN.mpr (fun n => h n k)
  validN_succ := by intro n x h k; exact CMRA.validN_succ (h k)
  validN_op_left := by intro n x y h k; exact CMRA.validN_op_left (h k)
  assoc := by intro x y z; funext k; exact CMRA.op_assoc _ _ _
  comm := by intro x y; funext k; exact CMRA.op_comm _ _
  pcore_op_left := by
    intro x cx h; cases h; funext k; exact TotalCore.op_left (x k)
  pcore_idem := by
    intro x cx h; cases h; congr 1; funext k; exact TotalCore.idem (x k)
  pcore_op_mono := by
    intro x cx h y; cases h
    classical
    let witness (k : K) :=
      Classical.choose (CMRA.pcore_op_mono (TotalCore.core_spec (x k)) (y k))
    have hs (k : K) : CMRA.pcore (CMRA.op (x k) (y k)) =
        some (CMRA.op (TotalCore.core (x k)) (witness k)) :=
      Classical.choose_spec (CMRA.pcore_op_mono (TotalCore.core_spec (x k)) (y k))
    refine ⟨witness, ?_⟩
    congr 2
    funext k
    have hc := TotalCore.core_spec (CMRA.op (x k) (y k))
    rw [hs k] at hc
    exact (Option.some.inj hc).symm
  extend := by
    intro n x y₁ y₂ hx hdist
    classical
    let e (k : K) := CMRA.extend (hx k) (hdist k)
    refine {
      left := fun k => (e k).left
      right := fun k => (e k).right
      decompose := ?_
      left_dist := fun k => (e k).left_dist
      right_dist := fun k => (e k).right_dist
    }
    funext k
    exact (e k).decompose

instance : UCMRA (ResourceMap K A) where
  unit _ := UCMRA.unit
  unit_valid _ := UCMRA.unit_valid
  unit_left x := by funext k; exact UCMRA.unit_left (x k)
  pcore_unit := by
    change some (fun _ : K => TotalCore.core (UCMRA.unit : A)) =
      some (fun _ : K => (UCMRA.unit : A))
    congr 1
    funext k
    have h := TotalCore.core_spec (UCMRA.unit : A)
    rw [UCMRA.pcore_unit] at h
    exact (Option.some.inj h).symm

instance : TotalCore (ResourceMap K A) where
  core x k := TotalCore.core (x k)
  core_spec _ := rfl

def singleton [DecidableEq K] (k : K) (a : A) : ResourceMap K A :=
  fun j => if j = k then a else UCMRA.unit

omit [TotalCore A] in @[simp] theorem singleton_same [DecidableEq K] (k : K) (a : A) :
    singleton k a k = a := by simp [singleton]

omit [TotalCore A] in @[simp] theorem singleton_other [DecidableEq K] {k j : K} (h : j ≠ k) (a : A) :
    singleton k a j = UCMRA.unit := by simp [singleton, h]

theorem singleton_op [DecidableEq K] (k : K) (a b : A) :
    singleton k (CMRA.op a b) = CMRA.op (singleton k a) (singleton k b) := by
  funext j
  change (if j = k then CMRA.op a b else UCMRA.unit) =
    CMRA.op (if j = k then a else UCMRA.unit)
      (if j = k then b else UCMRA.unit)
  by_cases h : j = k
  · simp [h]
  · simp [h, UCMRA.unit_left]

end ResourceMap
end LeanIrisX
