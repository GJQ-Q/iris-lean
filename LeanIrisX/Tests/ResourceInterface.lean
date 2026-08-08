import LeanIrisX.Logic.Invariant

namespace LeanIrisX.Tests.ResourceInterface
open LeanIrisX LeanIrisX.BI

theorem child_is_under_parent (N : Namespace) (i : Nat) :
    Namespace.Prefix N (Namespace.child N i) :=
  Namespace.prefix_child N i

theorem removed_namespace_is_unavailable (E : Mask) (N : Namespace) :
    ¬ Mask.without E N N :=
  Mask.without_excludes_prefix E (Namespace.prefix_refl N)

theorem fancy_update_can_be_framed {PROP : Type u} [BIBase PROP]
    [FancyUpdate PROP] [FancyUpdate.Laws PROP]
    (E₁ E₂ : Mask) (P R : PROP) :
    BIBase.sep (FancyUpdate.apply E₁ E₂ P) R ⊢
      FancyUpdate.apply E₁ E₂ (BIBase.sep P R) :=
  FancyUpdate.Laws.frame E₁ E₂ P R

theorem invariant_open_rule_available {PROP : Type u} [BIBase PROP]
    [FancyUpdate PROP] [Invariant PROP] [Invariant.Laws (PROP := PROP)]
    (E : Mask) (N : Namespace) (P : PROP) :
    Invariant.invProp N P ⊢ FancyUpdate.apply E (Mask.without E N)
      (BIBase.sep (BIBase.later P) (Invariant.closeToken E N P)) :=
  Invariant.Laws.openInvariant E N P

end LeanIrisX.Tests.ResourceInterface
