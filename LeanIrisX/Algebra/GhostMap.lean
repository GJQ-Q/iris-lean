import LeanIrisX.Algebra.TotalCore
import LeanIrisX.Logic.GhostState

namespace LeanIrisX

/-- Homogeneous global ghost resources indexed by ghost names. -/
abbrev GhostMap (A : Type u) := GhostName → A

namespace GhostMap

variable {A : Type u} [OFE A] [CMRA A] [UCMRA A] [TotalCore A]

def singleton (γ : GhostName) (a : A) : GhostMap A :=
  fun δ => if δ = γ then a else UCMRA.unit

omit [TotalCore A] in @[simp] theorem singleton_same (γ : GhostName) (a : A) : singleton γ a γ = a := by
  simp [singleton]

omit [TotalCore A] in @[simp] theorem singleton_other {γ δ : GhostName} (h : δ ≠ γ) (a : A) :
    singleton γ a δ = UCMRA.unit := by simp [singleton, h]

instance : CMRA (GhostMap A) where
  pcore x := some (fun γ => TotalCore.core (x γ))
  op x y γ := CMRA.op (x γ) (y γ)
  validN n x := ∀ γ, CMRA.validN n (x γ)
  valid x := ∀ γ, CMRA.valid (x γ)
  op_ne x := by intro n y₁ y₂ h γ; exact CMRA.op_ne_right (x γ) n (h γ)
  pcore_ne := by
    intro n x y cx hxy hcx
    change some (fun γ => TotalCore.core (x γ)) = some cx at hcx
    have hcx' := Option.some.inj hcx
    subst cx
    exact ⟨fun γ => TotalCore.core (y γ), rfl,
      fun γ => TotalCore.nonExpansive n (hxy γ)⟩
  pcore_none_ne := by intro n x y h hnone; contradiction
  validN_ne := by
    intro n x y hxy hx γ
    exact CMRA.validN_ne (hxy γ) (hx γ)
  valid_iff_validN := by
    intro x
    change (∀ γ, CMRA.valid (x γ)) ↔ ∀ n γ, CMRA.validN n (x γ)
    constructor
    · intro h n γ; exact CMRA.validN_of_valid (h γ) n
    · intro h γ; exact CMRA.valid_iff_validN.mpr (fun n => h n γ)
  validN_succ := by intro n x h γ; exact CMRA.validN_succ (h γ)
  validN_op_left := by intro n x y h γ; exact CMRA.validN_op_left (h γ)
  assoc := by intro x y z; funext γ; exact CMRA.op_assoc _ _ _
  comm := by intro x y; funext γ; exact CMRA.op_comm _ _
  pcore_op_left := by
    intro x cx h; cases h; funext γ; exact TotalCore.op_left (x γ)
  pcore_idem := by
    intro x cx h; cases h
    congr 1; funext γ; exact TotalCore.idem (x γ)
  pcore_op_mono := by
    intro x cx h y; cases h
    classical
    let witness (γ : GhostName) :=
      Classical.choose (CMRA.pcore_op_mono (TotalCore.core_spec (x γ)) (y γ))
    have witness_spec (γ : GhostName) :
        CMRA.pcore (CMRA.op (x γ) (y γ)) =
          some (CMRA.op (TotalCore.core (x γ)) (witness γ)) :=
      Classical.choose_spec
        (CMRA.pcore_op_mono (TotalCore.core_spec (x γ)) (y γ))
    refine ⟨witness, ?_⟩
    congr 2
    funext γ
    have hc := TotalCore.core_spec (CMRA.op (x γ) (y γ))
    rw [witness_spec γ] at hc
    exact (Option.some.inj hc).symm
  extend := by
    intro n x y₁ y₂ hx hdist
    classical
    let extAt (γ : GhostName) : CMRAExtension CMRA.op n (x γ) (y₁ γ) (y₂ γ) :=
      CMRA.extend (hx γ) (hdist γ)
    refine {
      left := fun γ => (extAt γ).left
      right := fun γ => (extAt γ).right
      decompose := ?_
      left_dist := fun γ => (extAt γ).left_dist
      right_dist := fun γ => (extAt γ).right_dist
    }
    funext γ
    exact (extAt γ).decompose

instance : UCMRA (GhostMap A) where
  unit _ := UCMRA.unit
  unit_valid γ := UCMRA.unit_valid
  unit_left x := by funext γ; exact UCMRA.unit_left (x γ)
  pcore_unit := by
    change some (fun _ => TotalCore.core (UCMRA.unit : A)) =
      some (fun _ => (UCMRA.unit : A))
    congr 1
    funext γ
    have h := TotalCore.core_spec (UCMRA.unit : A)
    rw [UCMRA.pcore_unit] at h
    exact (Option.some.inj h).symm

theorem singleton_op (γ : GhostName) (a b : A) :
    singleton γ (CMRA.op a b) =
      CMRA.op (singleton γ a) (singleton γ b) := by
  funext δ
  change (if δ = γ then CMRA.op a b else UCMRA.unit) =
    CMRA.op (if δ = γ then a else UCMRA.unit)
      (if δ = γ then b else UCMRA.unit)
  by_cases h : δ = γ
  · simp [h]
  · simp [h, UCMRA.unit_left]

theorem singleton_validN_iff (n : Nat) (γ : GhostName) (a : A) :
    CMRA.validN n (singleton γ a) ↔ CMRA.validN n a := by
  change (∀ δ, CMRA.validN n (if δ = γ then a else UCMRA.unit)) ↔
    CMRA.validN n a
  constructor
  · intro h; simpa using h γ
  · intro ha δ
    by_cases h : δ = γ
    · subst δ; simpa using ha
    · simp [h]; exact CMRA.validN_of_valid UCMRA.unit_valid n

end GhostMap
end LeanIrisX
