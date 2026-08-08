# Resource Interface M2 audit

## Status

M2 is a verified interface milestone between the BI/UPred logic core and a
future concrete invariant model. It builds successfully (56 jobs), its demo
checks successfully, and its Lean sources contain no `sorry`, `admit`, declared
`axiom`, or `unsafe` declaration.

## Concrete semantics completed

- Hierarchical namespaces represented by component lists.
- Namespace prefix relation with reflexivity, transitivity, and child proofs.
- Extensional masks with empty/full/singleton, union, intersection, difference,
  subset, disjointness, and namespace-subtree removal.
- Proof that removing a namespace excludes it and all of its descendants.
- Ghost names as a stable public name type.

## Law-constrained interfaces completed

- Fancy updates indexed by source and destination masks.
- Fancy-update introduction, monotonicity, transitivity, frame, and mask-frame
  laws.
- Typed named ghost ownership, including composition, validity, update, and
  allocation law interfaces.
- Invariant propositions, persistence/allocation interfaces, and an open rule
  that returns both the later body and a mandatory close token.
- Generic client theorems demonstrating that these laws are usable without
  depending on a specific proposition model.

These are type classes with proof fields, not global axioms. No instance for
`UPred` is fabricated. Code cannot use the laws unless it supplies an instance
and proofs of every field.

## Verification

```powershell
lake build
lake env lean .\Demo.lean
rg -n '\b(sorry|admit|axiom|unsafe)\b' . -g '*.lean' -g '!/.lake/**'
```

Expected results: 56 successful build jobs, successful Demo exit, and an empty
placeholder scan.

## Remaining semantic work

The next milestone must construct a concrete global resource/invariant model
and instantiate `FancyUpdate`, `GhostOwn`, and `Invariant` for its `IProp`.
Until those instances exist, M2 should be reported as a complete and usable
resource-layer **interface**, not as a complete invariant model.
