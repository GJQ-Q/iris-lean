# M17 certified fancy-update audit

## Scope

M17 turns the previously abstract `FancyUpdate` API into a concrete,
mask-sensitive instance for `UPred M`.

The implementation is:

* `Admissible E₁ E₂ := E₂ ⊆ₘ E₁`;
* `fupd E₁ E₂ P := Admissible E₁ E₂ ∧ basicUpdate P` at every world;
* all five laws required by `FancyUpdate.Laws` are proved: introduction,
  monotonicity, transitivity, framing, and mask framing.

Mask arguments are not decorative.  The negative regression test proves that
an update from the empty mask to the full mask is uninhabited.

## Semantic boundary

This milestone is the conservative mask-transition kernel.  It does **not**
claim that arbitrary mask enlargement is legal and does **not** claim the full
Iris invariant opening rule.  Restoring a temporarily removed namespace must
be justified by the invariant/world-satisfaction protocol in the next
milestone.

## Verification

* `lake build`: successful, 94 jobs.
* `lake env lean .\Demo.lean`: successful.
* Source scan over `LeanIrisX` and `Demo.lean`: no `sorry`, `admit`, user
  `axiom`, or `unsafe` declaration.
* `#print axioms` reports no axioms for `CertifiedFancyUpdate.trans`,
  `CertifiedFancyUpdate.frame`, and the negative mask test.

Lean's normal logical principles used by older quotient-based modules remain
reported separately and are not introduced by M17.

## Completion estimate

The first three roadmap layers are approximately **98%** complete.  Remaining
work is the semantic bridge connecting invariant opening/closing and
world-satisfaction transitions to this certified update kernel, followed by a
final API and regression audit.
