# M18 world/invariant protocol audit

## Result

M18 connects recursive-world satisfaction, namespace opening/closing,
hierarchical mask removal, and restoration authorization.

Implemented and proved:

* `LeafAt`, making explicit when exact world-name removal agrees with Iris
  subtree mask removal;
* `OpenCertificate`, which requires a satisfied world, mask/world alignment,
  an enabled and closed namespace, and the leaf condition;
* preservation of `WorldIris.WSatAt` when opening;
* agreement between the opened world's closed mask and `E.without N`;
* production of an explicit `RestorationPermit` by a successful opening;
* preservation of world satisfaction when closing;
* exact open/close round-trip restoration of both world and mask;
* a negative theorem proving restoration is not an ordinary M17 shrinking
  update when the namespace was enabled.

## Important semantic boundary

`RestorationPermit` is currently a checked transition certificate in Lean's
`Prop`. It establishes the world-transition semantics, but it is not yet a
linear `IProp` resource. M19 must internalize this certificate into ownership
before the public `Invariant.Laws.openInvariant` instance can honestly be
provided. M18 therefore does not install a fake invariant instance.

## Verification

* `lake build`: successful, 96 jobs.
* `lake env lean .\Demo.lean`: successful.
* The only build warnings are the two pre-existing universe co-occurrence
  lints in functor modules.
* No `sorry`, `admit`, user `axiom`, or `unsafe` declaration is introduced.
* Reported `propext`, `Classical.choice`, and `Quot.sound` are Lean principles
  inherited from the quotient-based recursive world representation.

## Completion estimate

The first three roadmap layers are approximately **99%** complete. The final
remaining task is to internalize the restoration permit as a consumable
logical resource, expose the concrete invariant instance, and run the final
API/negative-regression audit.
