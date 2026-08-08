import LeanIrisX.Logic.BI
import LeanIrisX.Algebra.Update

namespace LeanIrisX.UPred

variable {M : Type u} [OFE M] [CMRA M] [UCMRA M]

/-- Resource-independent modality: evaluate at the camera unit. -/
def plainly (P : UPred M) : UPred M where
  holds n _ := P.holdsAt n UCMRA.unit (CMRA.validN_of_valid UCMRA.unit_valid n)
  mono hp _ hle := P.mono hp (includedN_refl _ _) hle

/-- Persistent modality: evaluate at the duplicable core of the resource. -/
def persistently (P : UPred M) : UPred M where
  holds n x := P.holdsAt n (CMRA.core x.val) (CMRA.core_validN x.property)
  mono hp hinc hle :=
    P.mono hp (CMRA.core_includedN_core hinc) hle

theorem plainly_mono {P Q : UPred M} (h : P ⊢ᵤ Q) : plainly P ⊢ᵤ plainly Q := by
  intro n x hx hp
  exact h n UCMRA.unit (CMRA.validN_of_valid UCMRA.unit_valid n) hp

theorem plainly_idem (P : UPred M) :
    plainly (plainly P) ⊢ᵤ plainly P ∧ plainly P ⊢ᵤ plainly (plainly P) := by
  constructor <;> intro n x hx hp <;> exact hp

theorem plainly_elim (P : UPred M) : plainly P ⊢ᵤ P := by
  intro n x hx hp
  apply P.mono hp
  · exact ⟨x, OFE.of_eq (UCMRA.unit_left x).symm⟩
  · exact Nat.le_refl n

theorem persistently_mono {P Q : UPred M} (h : P ⊢ᵤ Q) :
    persistently P ⊢ᵤ persistently Q := by
  intro n x hx hp
  exact h n (CMRA.core x) (CMRA.core_validN hx) hp

theorem persistently_elim (P : UPred M) : persistently P ⊢ᵤ P := by
  intro n x hx hp
  apply P.mono hp
  · exact ⟨x, OFE.of_eq (CMRA.core_op x).symm⟩
  · exact Nat.le_refl n

theorem persistently_dup (P : UPred M) :
    persistently P ⊢ᵤ sep (persistently P) (persistently P) := by
  intro n x hx hp
  have hcorev : CMRA.validN n (CMRA.core x) := CMRA.core_validN hx
  refine ⟨CMRA.core x, x, OFE.of_eq (CMRA.core_op x).symm,
    hcorev, hx, ?_, hp⟩
  simpa [persistently, holdsAt, CMRA.core_idem] using hp

/-- A camera update yields the corresponding logical ownership update. -/
theorem own_update {a b : M} (hab : CMRA.FramePreservingUpdate a b) :
    own a ⊢ᵤ basicUpdate (own b) := by
  intro n x hx hax m hmn frame hxframe
  obtain ⟨f, hxf⟩ := includedN_mono hmn hax
  have hOldEq : CMRA.op x frame ≡{m}≡ CMRA.op a (CMRA.op f frame) :=
    OFE.trans (CMRA.op_ne_left frame m hxf)
      (OFE.of_eq (CMRA.op_assoc a f frame).symm)
  have hOld : CMRA.validN m (CMRA.op a (CMRA.op f frame)) :=
    CMRA.validN_ne hOldEq hxframe
  have hNew : CMRA.validN m (CMRA.op b (CMRA.op f frame)) :=
    hab m (some (CMRA.op f frame)) hOld
  refine ⟨CMRA.op b f, ?_, ?_⟩
  · simpa [CMRA.op_assoc] using hNew
  · have hNew' : CMRA.validN m (CMRA.op (CMRA.op b f) frame) := by
      rw [← CMRA.op_assoc]
      exact hNew
    have hbf : CMRA.validN m (CMRA.op b f) := CMRA.validN_op_left hNew'
    exact ⟨hbf, ⟨f, OFE.refl m (CMRA.op b f)⟩⟩

theorem basicUpdate_trans (P : UPred M) :
    basicUpdate (basicUpdate P) ⊢ᵤ basicUpdate P := by
  intro n x hx houter m hmn frame hxframe
  obtain ⟨y, hyframe, hy, hinner⟩ := houter m hmn frame hxframe
  exact hinner m (Nat.le_refl m) frame hyframe

theorem basicUpdate_idem (P : UPred M) :
    basicUpdate (basicUpdate P) ⊢ᵤ basicUpdate P ∧
    basicUpdate P ⊢ᵤ basicUpdate (basicUpdate P) :=
  ⟨basicUpdate_trans P, basicUpdate_intro (basicUpdate P)⟩

/-- The basic update frame rule. -/
theorem basicUpdate_frame (P R : UPred M) :
    sep (basicUpdate P) R ⊢ᵤ basicUpdate (sep P R) := by
  intro n x hx hsep m hmn frame hxframe
  obtain ⟨a, b, hab, ha, hb, hup, hr⟩ := hsep
  have habm : x ≡{m}≡ CMRA.op a b := OFE.mono hmn hab
  have hOldEq : CMRA.op x frame ≡{m}≡ CMRA.op a (CMRA.op b frame) :=
    OFE.trans (CMRA.op_ne_left frame m habm)
      (OFE.of_eq (CMRA.op_assoc a b frame).symm)
  have hOld : CMRA.validN m (CMRA.op a (CMRA.op b frame)) :=
    CMRA.validN_ne hOldEq hxframe
  have ham : CMRA.validN m a := CMRA.validN_mono hmn ha
  have hbm : CMRA.validN m b := CMRA.validN_mono hmn hb
  obtain ⟨y, hybf, hy, hp⟩ :=
    hup m hmn (CMRA.op b frame) hOld
  refine ⟨CMRA.op y b, ?_, ?_⟩
  · simpa [CMRA.op_assoc] using hybf
  · have hyb : CMRA.validN m (CMRA.op y b) := by
      have hybf' : CMRA.validN m (CMRA.op (CMRA.op y b) frame) := by
        rw [← CMRA.op_assoc]
        exact hybf
      exact CMRA.validN_op_left hybf'
    refine ⟨hyb, y, b, OFE.refl m _, hy, hbm, hp, ?_⟩
    exact R.mono hr (includedN_refl m b) hmn

theorem later_contractive : Contractive (later : UPred M → UPred M) := by
  intro n P Q hPQ m x hx hmn
  cases m with
  | zero => exact Iff.rfl
  | succ m =>
    have hlt : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hmn
    exact hPQ m hlt m x (CMRA.validN_succ hx) (Nat.le_refl m)

theorem plainly_nonExpansive : NonExpansive (plainly : UPred M → UPred M) := by
  intro n P Q hPQ m x hx hmn
  exact hPQ m UCMRA.unit (CMRA.validN_of_valid UCMRA.unit_valid m) hmn

theorem persistently_nonExpansive :
    NonExpansive (persistently : UPred M → UPred M) := by
  intro n P Q hPQ m x hx hmn
  exact hPQ m (CMRA.core x) (CMRA.core_validN hx) hmn

theorem basicUpdate_nonExpansive :
    NonExpansive (basicUpdate : UPred M → UPred M) := by
  intro n P Q hPQ m x hx hmn
  constructor
  · intro hup k hkm frame hvalid
    obtain ⟨y, hyframe, hy, hp⟩ := hup k hkm frame hvalid
    exact ⟨y, hyframe, hy, (hPQ k y hy (Nat.le_trans hkm hmn)).mp hp⟩
  · intro hup k hkm frame hvalid
    obtain ⟨y, hyframe, hy, hq⟩ := hup k hkm frame hvalid
    exact ⟨y, hyframe, hy, (hPQ k y hy (Nat.le_trans hkm hmn)).mpr hq⟩

end LeanIrisX.UPred
