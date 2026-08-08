import LeanIrisX.Logic.BI

/-! Logical ownership laws connecting camera composition and separation. -/

namespace LeanIrisX.UPred

variable {M : Type u} [OFE M] [CMRA M] [UCMRA M]

/-- Ownership of a composition can be split into separating ownership. -/
theorem own_op_sep (a b : M) : own (CMRA.op a b) ⊢ᵤ sep (own a) (own b) := by
  intro n x hx hab
  obtain ⟨frame, hframe⟩ := hab
  have hsplit : OFE.dist n x (CMRA.op a (CMRA.op b frame)) :=
    OFE.trans hframe (OFE.of_eq (CMRA.op_assoc a b frame).symm)
  have hvSplit : CMRA.validN n (CMRA.op a (CMRA.op b frame)) :=
    CMRA.validN_ne hsplit hx
  have hva : CMRA.validN n a := CMRA.validN_op_left hvSplit
  have hvbf : CMRA.validN n (CMRA.op b frame) := by
    apply CMRA.validN_op_left (x := CMRA.op b frame) (y := a)
    simpa [CMRA.op_comm] using hvSplit
  refine ⟨a, CMRA.op b frame, hsplit, hva, hvbf, ?_, ?_⟩
  · exact includedN_refl n a
  · exact ⟨frame, OFE.refl n _⟩

/-- Separating ownership recombines into ownership of the camera operation. -/
theorem sep_own_op (a b : M) : sep (own a) (own b) ⊢ᵤ own (CMRA.op a b) := by
  intro n x hx hsep
  obtain ⟨ra, rb, hsplit, hva, hvb, ha, hb⟩ := hsep
  obtain ⟨fa, hra⟩ := ha
  obtain ⟨fb, hrb⟩ := hb
  refine ⟨CMRA.op fa fb, ?_⟩
  have hparts : OFE.dist n (CMRA.op ra rb)
      (CMRA.op (CMRA.op a fa) (CMRA.op b fb)) :=
    CMRA.op_ne₂ n hra hrb
  have hreorder :
      CMRA.op (CMRA.op a fa) (CMRA.op b fb) =
        CMRA.op (CMRA.op a b) (CMRA.op fa fb) := by
    calc
      CMRA.op (CMRA.op a fa) (CMRA.op b fb) =
          CMRA.op a (CMRA.op fa (CMRA.op b fb)) :=
        (CMRA.op_assoc a fa (CMRA.op b fb)).symm
      _ = CMRA.op a (CMRA.op (CMRA.op fa b) fb) := by
        rw [CMRA.op_assoc fa b fb]
      _ = CMRA.op a (CMRA.op (CMRA.op b fa) fb) := by
        rw [CMRA.op_comm fa b]
      _ = CMRA.op a (CMRA.op b (CMRA.op fa fb)) := by
        rw [← CMRA.op_assoc b fa fb]
      _ = CMRA.op (CMRA.op a b) (CMRA.op fa fb) :=
        CMRA.op_assoc a b (CMRA.op fa fb)
  exact OFE.trans hsplit (OFE.trans hparts (OFE.of_eq hreorder))

theorem own_op_iff_sep (a b : M) :
    own (CMRA.op a b) ⊢ᵤ sep (own a) (own b) ∧
      sep (own a) (own b) ⊢ᵤ own (CMRA.op a b) :=
  ⟨own_op_sep a b, sep_own_op a b⟩

end LeanIrisX.UPred
