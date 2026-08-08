import LeanIrisX.Algebra.CMRA

namespace LeanIrisX

namespace ProductCMRA

variable {α : Type u} {β : Type v}
variable [OFE α] [OFE β] [CMRA α] [CMRA β]

def pcore (x : α × β) : Option (α × β) :=
  match CMRA.pcore x.1, CMRA.pcore x.2 with
  | some cx, some cy => some (cx, cy)
  | _, _ => none

instance prodCMRA : CMRA (α × β) where
  pcore := pcore
  op x y := (CMRA.op x.1 y.1, CMRA.op x.2 y.2)
  validN n x := CMRA.validN n x.1 ∧ CMRA.validN n x.2
  valid x := CMRA.valid x.1 ∧ CMRA.valid x.2
  op_ne x := by
    intro n y₁ y₂ h
    exact ⟨CMRA.op_ne x.1 n h.1, CMRA.op_ne x.2 n h.2⟩
  pcore_ne := by
    intro n x y cx hxy hcore
    simp only [pcore] at hcore
    split at hcore <;> try contradiction
    next c₁ c₂ hx₁ hx₂ =>
      cases hcore
      obtain ⟨d₁, hy₁, hd₁⟩ := CMRA.pcore_ne hxy.1 hx₁
      obtain ⟨d₂, hy₂, hd₂⟩ := CMRA.pcore_ne hxy.2 hx₂
      exact ⟨(d₁, d₂), by simp [pcore, hy₁, hy₂], ⟨hd₁, hd₂⟩⟩
  pcore_none_ne := by
    intro n x y hxy hnone
    simp only [pcore] at hnone ⊢
    cases hx₁ : CMRA.pcore x.1 with
    | none =>
      have hy₁ : CMRA.pcore y.1 = none := CMRA.pcore_none_ne hxy.1 hx₁
      simp [hy₁]
    | some cx₁ =>
      cases hx₂ : CMRA.pcore x.2 with
      | none =>
        have hy₂ : CMRA.pcore y.2 = none := CMRA.pcore_none_ne hxy.2 hx₂
        simp [hy₂]
      | some cx₂ => simp [hx₁, hx₂] at hnone
  validN_ne := by
    intro n x y hxy hx
    exact ⟨CMRA.validN_ne hxy.1 hx.1, CMRA.validN_ne hxy.2 hx.2⟩
  valid_iff_validN := by
    intro x
    constructor
    · intro h n
      exact ⟨CMRA.valid_iff_validN.mp h.1 n, CMRA.valid_iff_validN.mp h.2 n⟩
    · intro h
      exact ⟨CMRA.valid_iff_validN.mpr (fun n => (h n).1),
        CMRA.valid_iff_validN.mpr (fun n => (h n).2)⟩
  validN_succ := by
    intro n x h
    exact ⟨CMRA.validN_succ h.1, CMRA.validN_succ h.2⟩
  validN_op_left := by
    intro n x y h
    exact ⟨CMRA.validN_op_left h.1, CMRA.validN_op_left h.2⟩
  assoc := by
    intro x y z
    apply Prod.ext
    · exact CMRA.assoc _ _ _
    · exact CMRA.assoc _ _ _
  comm := by
    intro x y
    apply Prod.ext
    · exact CMRA.comm _ _
    · exact CMRA.comm _ _
  pcore_op_left := by
    intro x cx h
    simp only [pcore] at h
    split at h <;> try contradiction
    next c₁ c₂ hx₁ hx₂ =>
      cases h
      apply Prod.ext
      · exact CMRA.pcore_op_left hx₁
      · exact CMRA.pcore_op_left hx₂
  pcore_idem := by
    intro x cx h
    simp only [pcore] at h
    split at h <;> try contradiction
    next c₁ c₂ hx₁ hx₂ =>
      cases h
      simp [pcore, CMRA.pcore_idem hx₁, CMRA.pcore_idem hx₂]
  pcore_op_mono := by
    intro x cx h y
    simp only [pcore] at h
    split at h <;> try contradiction
    next c₁ c₂ hx₁ hx₂ =>
      cases h
      obtain ⟨d₁, hd₁⟩ := CMRA.pcore_op_mono hx₁ y.1
      obtain ⟨d₂, hd₂⟩ := CMRA.pcore_op_mono hx₂ y.2
      exact ⟨(d₁, d₂), by simp [pcore, hd₁, hd₂]⟩
  extend := by
    intro n x y₁ y₂ hx hdist
    obtain e₁ := CMRA.extend hx.1 hdist.1
    obtain e₂ := CMRA.extend hx.2 hdist.2
    exact {
      left := (e₁.left, e₂.left)
      right := (e₁.right, e₂.right)
      decompose := by
        apply Prod.ext
        · exact e₁.decompose
        · exact e₂.decompose
      left_dist := ⟨e₁.left_dist, e₂.left_dist⟩
      right_dist := ⟨e₁.right_dist, e₂.right_dist⟩
    }

instance prodUCMRA [UCMRA α] [UCMRA β] : UCMRA (α × β) where
  unit := (UCMRA.unit, UCMRA.unit)
  unit_valid := ⟨UCMRA.unit_valid, UCMRA.unit_valid⟩
  unit_left := by
    intro x
    apply Prod.ext
    · exact UCMRA.unit_left x.1
    · exact UCMRA.unit_left x.2
  pcore_unit := by
    change ProductCMRA.pcore
      ((UCMRA.unit : α), (UCMRA.unit : β)) =
      some ((UCMRA.unit : α), (UCMRA.unit : β))
    simp only [ProductCMRA.pcore, UCMRA.pcore_unit]

end ProductCMRA
end LeanIrisX
