# Invariant Core M6 audit

## Scope completed

- A disjoint mask-token CMRA based on namespace ownership multiplicities.
- Concrete `ownE` and `ownD` predicates with sound split/combine rules.
- Optional agreement cells containing `Later PROP` for invariant bodies.
- Namespace-indexed pointwise resource maps and invariant registries.
- Same-name registry validity implies step-indexed agreement of bodies.
- Structural world snapshots and `WSatAt` coherence conditions.
- Closed and opened names form a disjoint partition, so an invariant cannot be
  simultaneously closed and opened.

## Semantic boundary

`WSatAt` is the structural world-satisfaction layer.  It is not yet the final
recursive `IProp` fixed point and this milestone does not claim a concrete
`FancyUpdate (IProp M)` or final invariant allocation/opening rules.  Those must
be constructed on top of this audited resource model.

## Verification

- `lake build`: passed, 72 jobs.
- `lake env lean Demo.lean`: passed.
- Source scan: no `sorry`, `admit`, or declared `axiom`.
- `#print axioms` reports only Lean quotient/extensionality/classical principles
  where used; no project-specific axioms are introduced.

## Reproduction

```powershell
lake build
lake env lean .\Demo.lean
```
