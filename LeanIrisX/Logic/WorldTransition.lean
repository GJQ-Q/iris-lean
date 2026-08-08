import LeanIrisX.Logic.WorldSatisfaction

/-! Conservation laws for opening and closing invariant names in `wsat`. -/

namespace LeanIrisX
namespace WorldTransition

variable {PROP : Type u} [OFE PROP]

def openName (w : WorldSnapshot PROP) (N : Namespace) : WorldSnapshot PROP :=
  { w with closed := Mask.erase w.closed N, opened := Mask.insert w.opened N }

def closeName (w : WorldSnapshot PROP) (N : Namespace) : WorldSnapshot PROP :=
  { w with closed := Mask.insert w.closed N, opened := Mask.erase w.opened N }

theorem partition_open {all closed opened : Mask} {N : Namespace}
    (hp : WorldSatisfaction.Partition all closed opened) (hc : closed N) :
    WorldSatisfaction.Partition all (Mask.erase closed N) (Mask.insert opened N) := by
  constructor
  · intro K
    constructor
    · intro hK
      rcases (hp.1 K).mp hK with hclosed | hopened
      · by_cases hKN : K = N
        · exact Or.inr (Or.inr hKN)
        · exact Or.inl ⟨hclosed, hKN⟩
      · exact Or.inr (Or.inl hopened)
    · intro hK
      rcases hK with hclosed | hopened
      · exact (hp.1 K).mpr (Or.inl hclosed.1)
      · rcases hopened with hopened | rfl
        · exact (hp.1 K).mpr (Or.inr hopened)
        · exact (hp.1 K).mpr (Or.inl hc)
  · intro K hclosed hopened
    rcases hopened with hopened | hKN
    · exact hp.2 K hclosed.1 hopened
    · exact hclosed.2 hKN

theorem partition_close {all closed opened : Mask} {N : Namespace}
    (hp : WorldSatisfaction.Partition all closed opened) (ho : opened N) :
    WorldSatisfaction.Partition all (Mask.insert closed N) (Mask.erase opened N) := by
  constructor
  · intro K
    constructor
    · intro hK
      rcases (hp.1 K).mp hK with hclosed | hopened
      · exact Or.inl (Or.inl hclosed)
      · by_cases hKN : K = N
        · exact Or.inl (Or.inr hKN)
        · exact Or.inr ⟨hopened, hKN⟩
    · intro hK
      rcases hK with hclosed | hopened
      · rcases hclosed with hclosed | rfl
        · exact (hp.1 K).mpr (Or.inl hclosed)
        · exact (hp.1 K).mpr (Or.inr ho)
      · exact (hp.1 K).mpr (Or.inr hopened.1)
  · intro K hclosed hopened
    rcases hclosed with hclosed | hKN
    · exact hp.2 K hclosed hopened.1
    · exact hopened.2 hKN

theorem wsat_open {n : Nat} {w : WorldSnapshot PROP} {N : Namespace}
    (hw : WorldSatisfaction.WSatAt n w) (hc : w.closed N) :
    WorldSatisfaction.WSatAt n (openName w N) := by
  exact ⟨hw.1, partition_open hw.2.1 hc, hw.2.2⟩

theorem wsat_close {n : Nat} {w : WorldSnapshot PROP} {N : Namespace}
    (hw : WorldSatisfaction.WSatAt n w) (ho : w.opened N) :
    WorldSatisfaction.WSatAt n (closeName w N) := by
  exact ⟨hw.1, partition_close hw.2.1 ho, hw.2.2⟩

theorem open_removes_closed (w : WorldSnapshot PROP) (N : Namespace) :
    ¬ (openName w N).closed N := Mask.erase_self _ _

theorem open_adds_opened (w : WorldSnapshot PROP) (N : Namespace) :
    (openName w N).opened N := Mask.insert_self _ _

theorem close_adds_closed (w : WorldSnapshot PROP) (N : Namespace) :
    (closeName w N).closed N := Mask.insert_self _ _

theorem close_removes_opened (w : WorldSnapshot PROP) (N : Namespace) :
    ¬ (closeName w N).opened N := Mask.erase_self _ _

end WorldTransition
end LeanIrisX
