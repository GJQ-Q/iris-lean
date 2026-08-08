import LeanIrisX.Algebra.InvariantEntry
import LeanIrisX.Algebra.ResourceMap
import LeanIrisX.Logic.Mask

namespace LeanIrisX

abbrev InvariantRegistry (PROP : Type u) [OFE PROP] :=
  ResourceMap Namespace (InvariantEntry PROP)

namespace InvariantRegistry

variable {PROP : Type u} [OFE PROP]

def singleton (N : Namespace) (P : PROP) : InvariantRegistry PROP :=
  ResourceMap.singleton N (InvariantEntry.allocated P)

theorem singleton_same (N : Namespace) (P : PROP) :
    singleton N P N = InvariantEntry.allocated P := by
  simp [singleton]

theorem singleton_op (N : Namespace) (P Q : PROP) :
    ResourceMap.singleton N
      (CMRA.op (InvariantEntry.allocated P) (InvariantEntry.allocated Q)) =
    CMRA.op (singleton N P) (singleton N Q) :=
  ResourceMap.singleton_op N _ _

theorem validN_same_name_agree {n : Nat} {N : Namespace} {P Q : PROP}
    (h : CMRA.validN (n + 1) (CMRA.op (singleton N P) (singleton N Q))) :
    P ≡{n}≡ Q := by
  have h' : CMRA.validN (n + 1) (ResourceMap.singleton N
      (CMRA.op (InvariantEntry.allocated P) (InvariantEntry.allocated Q))) := by
    rw [singleton_op]
    exact h
  have hN := h' N
  have hN' : CMRA.validN (n + 1)
      (CMRA.op (InvariantEntry.allocated P) (InvariantEntry.allocated Q)) := by
    simpa using hN
  exact InvariantEntry.allocated_op_valid_succ_iff.mp hN'

end InvariantRegistry
end LeanIrisX
