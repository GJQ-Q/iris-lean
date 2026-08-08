# First Three Layers Integration Candidate — Audit Report

## Result

This candidate compiles as one Lean package (`104` build jobs) and its public
demo type-checks.  A source scan finds no `sorry`, `admit`, user-declared
`axiom`, or `unsafe` declaration in Lean source files.

The new integrated construction is not a mock record.  `FinalWorld.IRes` is a
solved recursive resource domain built through the existing contractive
OFunctor/COFE tower and combines:

1. a guarded named-invariant registry;
2. a persistent-handle ghost map using a nontrivial idempotent CMRA element;
3. an exclusive close-token ghost map;
4. an independent extension slot for client ghost resources.

## Newly machine-checked guarantees

- `FinalWorld.fold_unfold` and `unfold_fold`: the recursive proposition/resource
  equation is an isomorphism.
- `FinalWorld.registry_handle_valid`: a registered guarded body and its public
  handle form a valid resource package.
- `FinalWorld.handle_idem`: duplicating a public handle changes no resource.
- `FinalWorld.handle_nontrivial`: the handle is not merely the CMRA unit.
- `FinalWorld.close_conflict`: two copies of a close permission are invalid.
- `FinalWorld.handle_and_close_compatible`: a public handle and one close
  permission can coexist.
- `FinalWorld.package_authenticated`: the registry entry and handle are tied to
  the same internal ghost identity.

All these statements are kernel-checked.  Their reported dependencies are the
standard Lean quotient/extensionality principles (`propext`,
`Classical.choice`, `Quot.sound`) inherited from the recursive quotient model;
they are not project-specific assumptions.

## Reproduction

Run from the project root:

```powershell
lake build
lake env lean .\Demo.lean
rg -n --glob '*.lean' "\bsorry\b|\badmit\b|^\s*axiom\b|^\s*unsafe\b" .
```

Expected results: the first two commands exit with code zero; the final scan
prints no matches.

## Honest semantic boundary

This candidate substantially completes the algebraic, logical-model, and
resource-model infrastructure, but it is not yet a complete port of Iris's
invariant subsystem.  The remaining critical task is to connect this concrete
recursive world to a world-satisfaction-indexed fancy update and then derive
the public allocation/open/close invariant rules.  Existing abstract
`Invariant`/`FancyUpdate` interfaces must not be mistaken for that derivation.

Consequently, the candidate is suitable for review, reuse of the first-three-
layer primitives, and continued implementation.  It should be presented as a
semantic-core integration candidate, not yet as a full production Iris port.
