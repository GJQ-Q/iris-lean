import LeanIrisX.Logic.FinalWorldInvariantProtocol

namespace LeanIrisX.Tests.FinalWorldInvariantProtocol

open LeanIrisX.FinalWorldInvariantProtocol

def N : Namespace := [7, 1]

example (n : Nat) (P : FinalWorld.IPre) :
    AllocationCertificate n N 40 P :=
  allocate n N 40 P

example {n : Nat} {w : World} {E : Mask} {P : FinalWorld.IPre}
    (c : OpenCertificate n w E N 40 P) :
    WSatAt n (openName w N) :=
  c.opened_wsat

example {n : Nat} {w : World} {E : Mask} {P : FinalWorld.IPre}
    (c : OpenCertificate n w E N 40 P) :
    ¬ CMRA.valid
      (CMRA.op (FinalWorld.closeSlot 40) (FinalWorld.closeSlot 40)) :=
  c.close_permission_linear

end LeanIrisX.Tests.FinalWorldInvariantProtocol
