# M16 Recursive World Resource Audit

## Result

M16 places a namespace-indexed invariant registry inside the solved recursive
resource equation. Invariant bodies occur under `Later`, and each namespace is
exclusive, so the construction is locally contractive and prevents two bodies
from occupying the same invariant name.

## Added components

- `InvariantRegistryF = Namespace → GuardedExcl B`;
- complete OFunctor, contractive functor and UCMRAFunctor proofs;
- singleton invariant slots containing delayed recursive propositions;
- `WorldPlugin = InvariantRegistryF × UnitGhostPlugin`;
- solved recursive `WorldIris.IPre`, `IRes`, and `IProp`;
- core, invariant and named-ghost resource injections;
- recursive fold/unfold inverse laws;
- concrete world records with registered/closed/opened masks;
- world validity and structural open/close transitions;
- validity preservation of structural transitions;
- proofs that distinct invariant names coexist;
- proof that one invariant name cannot contain two bodies.

## Verification

```powershell
lake build
lake env lean .\Demo.lean
```

The source is scanned for `sorry`, `admit`, and user `axiom` tokens.

## Remaining boundary

The recursive world resource is now concrete. A full Iris fancy update still
requires quantifying over frame-preserving world transitions and proving the
abstract `FancyUpdate.Laws` and `Invariant.Laws` instances. M16 does not replace
that construction with a mask-insensitive basic update.
