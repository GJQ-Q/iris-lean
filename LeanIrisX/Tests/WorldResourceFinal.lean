import LeanIrisX.Logic.WorldResourceFinal

namespace LeanIrisX.Tests.WorldResourceFinal

open LeanIrisX

def N : Namespace := [12]

#synth OFunctor FinalWorldPlugin
#synth OFunctorContractive FinalWorldPlugin
#synth UCMRAFunctor FinalWorldPlugin

theorem authenticated_package (P : FinalWorld.IPre) :
    FinalWorld.AuthenticatedAt 5
      (CMRA.op (FinalWorld.registrySlot N 30 P)
        (FinalWorld.handleSlot 30)) N 30 P :=
  FinalWorld.package_authenticated 5 N 30 P

theorem handle_can_be_copied :
    CMRA.op (FinalWorld.handleSlot 30) (FinalWorld.handleSlot 30) =
      FinalWorld.handleSlot 30 :=
  FinalWorld.handle_idem 30

theorem close_permission_cannot_be_copied :
    ¬ CMRA.valid (CMRA.op
      (FinalWorld.closeSlot 30) (FinalWorld.closeSlot 30)) :=
  FinalWorld.close_conflict 30

theorem handle_is_not_emp :
    FinalWorld.handleSlot 30 ≠ (UCMRA.unit : FinalWorld.IRes) :=
  FinalWorld.handle_nontrivial 30

end LeanIrisX.Tests.WorldResourceFinal
