import LeanIrisX.Algebra.GhostMap
import LeanIrisX.Logic.BIInstance
import LeanIrisX.Logic.Ownership

namespace LeanIrisX

namespace UPredGhost

variable {A : Type u} [OFE A] [CMRA A] [UCMRA A] [TotalCore A]

def namedOwn (γ : GhostName) (a : A) : UPred (GhostMap A) :=
  UPred.own (GhostMap.singleton γ a)

def validProp (a : A) : UPred (GhostMap A) where
  holds n _ := CMRA.validN n a
  mono h _ hle := CMRA.validN_mono hle h

instance : GhostOwn (UPred (GhostMap A)) A where
  own := namedOwn
  validProp := validProp

theorem namedOwn_op (γ : GhostName) (a b : A) :
    namedOwn γ (CMRA.op a b) ⊢ᵤ
      UPred.sep (namedOwn γ a) (namedOwn γ b) := by
  rw [namedOwn, GhostMap.singleton_op]
  exact UPred.own_op_sep _ _

theorem namedOwn_valid (γ : GhostName) (a : A) :
    namedOwn γ a ⊢ᵤ validProp a := by
  intro n x hx hinc
  obtain ⟨frame, hdist⟩ := hinc
  have hvCombined : CMRA.validN n
      (CMRA.op (GhostMap.singleton γ a) frame) :=
    CMRA.validN_ne hdist hx
  have hvSingleton : CMRA.validN n (GhostMap.singleton γ a) :=
    CMRA.validN_op_left hvCombined
  exact (GhostMap.singleton_validN_iff n γ a).mp hvSingleton

end UPredGhost
end LeanIrisX
