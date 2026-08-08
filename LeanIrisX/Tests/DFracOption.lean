import LeanIrisX.Algebra.DFrac
import LeanIrisX.Algebra.Option

namespace LeanIrisX.Tests.DFracOption

open LeanIrisX DFrac OptionCMRA

theorem two_halves_make_full :
    CMRA.op (DFrac.own DFrac.half) (DFrac.own DFrac.half) = DFrac.own DFrac.one := by
  apply congrArg DFrac.own
  apply PosRat.ext
  exact DFrac.half_add_half

theorem two_halves_are_valid :
    CMRA.valid (CMRA.op (DFrac.own DFrac.half) (DFrac.own DFrac.half)) :=
  DFrac.halves_valid

theorem full_and_half_conflict :
    ¬ CMRA.valid (CMRA.op (DFrac.own DFrac.one) (DFrac.own DFrac.half)) :=
  DFrac.full_plus_half_invalid

theorem discarded_is_persistent :
    CMRA.op DFrac.discard DFrac.discard = DFrac.discard := rfl

theorem discarding_owned_fraction_records_both :
    CMRA.op (DFrac.own DFrac.half) DFrac.discard =
      DFrac.ownDiscard DFrac.half := rfl

theorem option_none_is_unit (x : Option Unit) : CMRA.op none x = x := rfl

theorem option_some_composes :
    CMRA.op (some ()) (some ()) = (some () : Option Unit) := rfl

theorem option_some_valid : CMRA.valid (some () : Option Unit) := trivial

end LeanIrisX.Tests.DFracOption
