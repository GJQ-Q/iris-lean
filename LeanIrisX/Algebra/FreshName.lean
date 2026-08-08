import LeanIrisX.Algebra.MonoNat
import LeanIrisX.Logic.GhostState

namespace LeanIrisX

/-- A high-water-mark allocator: precisely the names below `next` have already
been allocated. -/
structure FreshNameState where
  next : GhostName
deriving DecidableEq, Repr

namespace FreshNameState

def initial : FreshNameState := ⟨0⟩
def Allocated (s : FreshNameState) (γ : GhostName) : Prop := γ < s.next
def fresh (s : FreshNameState) : GhostName := s.next
def advance (s : FreshNameState) : FreshNameState := ⟨s.next + 1⟩

theorem fresh_not_allocated (s : FreshNameState) :
    ¬ Allocated s (fresh s) := by
  simp [Allocated, fresh]

theorem fresh_allocated_after (s : FreshNameState) :
    Allocated (advance s) (fresh s) := by
  simp [Allocated, advance, fresh]

theorem previously_allocated_remains {s : FreshNameState} {γ : GhostName}
    (h : Allocated s γ) : Allocated (advance s) γ := by
  exact Nat.lt_succ_of_lt h

theorem advance_strict (s : FreshNameState) : s.next < (advance s).next := by
  simp [advance]

end FreshNameState

/- Authoritative ghost representation of the high-water mark. -/
namespace FreshNameGhost

abbrev Resource := MonoNatGhost.Ghost

def authority (s : FreshNameState) : Resource :=
  MonoNatGhost.authoritative s.next

/-- A token for `γ` records the lower bound `γ + 1`, hence proves `γ` was
allocated once combined with the current authority. -/
def token (γ : GhostName) : Resource :=
  MonoNatGhost.fragment (γ + 1)

theorem allocate_update (s : FreshNameState) :
    CMRA.FramePreservingUpdate (authority s)
      (CMRA.op (authority (FreshNameState.advance s))
        (token (FreshNameState.fresh s))) := by
  exact MonoNatGhost.grow_and_allocate (Nat.le_succ s.next)

theorem token_proves_allocated {n : Nat} {s : FreshNameState}
    {γ : GhostName}
    (h : CMRA.validN n (CMRA.op (authority s) (token γ))) :
    FreshNameState.Allocated s γ := by
  have hbound : γ + 1 ≤ s.next := MonoNatGhost.fragment_le_authority h
  exact (Nat.add_one_le_iff).mp hbound

theorem fresh_token_after_update_is_valid_bound (s : FreshNameState) :
    FreshNameState.Allocated (FreshNameState.advance s)
      (FreshNameState.fresh s) :=
  FreshNameState.fresh_allocated_after s

end FreshNameGhost
end LeanIrisX
