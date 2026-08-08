import LeanIrisX.Logic.WorldTransition

namespace LeanIrisX.Tests.WorldTransition

open LeanIrisX

theorem opening_preserves_wsat {PROP : Type u} [OFE PROP]
    {n : Nat} {w : WorldSnapshot PROP} {N : Namespace}
    (hw : WorldSatisfaction.WSatAt n w) (hc : w.closed N) :
    WorldSatisfaction.WSatAt n (WorldTransition.openName w N) :=
  WorldTransition.wsat_open hw hc

theorem closing_preserves_wsat {PROP : Type u} [OFE PROP]
    {n : Nat} {w : WorldSnapshot PROP} {N : Namespace}
    (hw : WorldSatisfaction.WSatAt n w) (ho : w.opened N) :
    WorldSatisfaction.WSatAt n (WorldTransition.closeName w N) :=
  WorldTransition.wsat_close hw ho

theorem opened_name_cannot_remain_closed {PROP : Type u} [OFE PROP]
    (w : WorldSnapshot PROP) (N : Namespace) :
    ¬ (WorldTransition.openName w N).closed N :=
  WorldTransition.open_removes_closed w N

theorem closed_name_cannot_remain_opened {PROP : Type u} [OFE PROP]
    (w : WorldSnapshot PROP) (N : Namespace) :
    ¬ (WorldTransition.closeName w N).opened N :=
  WorldTransition.close_removes_opened w N

end LeanIrisX.Tests.WorldTransition
