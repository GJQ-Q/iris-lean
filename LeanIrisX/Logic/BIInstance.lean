import LeanIrisX.Logic.BIBase
import LeanIrisX.Logic.Modalities

namespace LeanIrisX

instance {M : Type u} [OFE M] [CMRA M] [UCMRA M] : BIBase (UPred M) where
  Entails := UPred.Entails
  emp := UPred.emp
  pure := UPred.pure
  and := UPred.and
  or := UPred.or
  imp := UPred.imp
  sep := UPred.sep
  wand := UPred.wand
  later := UPred.later
  persistently := UPred.persistently
  plainly := UPred.plainly
  basicUpdate := UPred.basicUpdate

instance {M : Type u} [OFE M] [CMRA M] [UCMRA M] : BIQuantifiers (UPred M) where
  all := UPred.all
  exist := UPred.exist

instance {M : Type u} [OFE M] [CMRA M] [UCMRA M] : BI.Laws (UPred M) where
  entails_refl := UPred.entails_refl
  entails_trans := UPred.entails_trans
  sep_comm := UPred.sep_comm
  sep_assoc := UPred.sep_assoc_forward
  sep_emp_left P := UPred.entails_trans (UPred.sep_comm _ _)
    (UPred.sep_emp_right_forward P)
  sep_emp_right := UPred.sep_emp_right_forward
  wand_intro := UPred.wand_intro
  wand_elim := UPred.wand_elim
  later_intro := UPred.later_intro
  persistently_elim := UPred.persistently_elim
  persistently_dup := UPred.persistently_dup
  bupd_intro := UPred.basicUpdate_intro
  bupd_trans := UPred.basicUpdate_trans

end LeanIrisX
