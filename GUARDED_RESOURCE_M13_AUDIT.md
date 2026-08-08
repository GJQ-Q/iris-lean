# M13 Guarded Recursive Resource Audit

## Result

M13 replaces the constant-resource smoke test of M12 with a genuinely
parameter-dependent resource functor.  Its recursive parameter occurs beneath
`Later`, so contractiveness follows from step-indexed guardedness rather than
from ignoring the parameter.

## New semantic components

- `GuardedExcl α`: a non-discrete exclusive CMRA carrying `Later α`;
- proved OFE and COFE instances, including a constructor-shape-preserving limit;
- proved CMRA, UCMRA and total-core instances;
- functorial payload mapping preserving validity and composition;
- `GuardedResourceF`, with proved `OFunctor`, `OFunctorContractive`, and
  `UCMRAFunctor` instances;
- `GuardedPropF := UPredOF GuardedResourceF`;
- a solved recursive equation with
  `IPre ≃ UPred (GuardedExcl IPre)`;
- both fold/unfold inverse laws.

## Regression evidence

The tests prove both sides of guarded observation: depth zero hides arbitrary
payload differences, while depth one distinguishes the concrete payloads
`0` and `1`.  This prevents accidentally replacing the construction with a
constant or fully discrete simulation.

Verification commands:

```powershell
lake build
lake env lean .\Demo.lean
```

The release was also scanned for the tokens `sorry`, `admit`, and user-declared
`axiom`; none occur in Lean sources.

## Exact boundary

This is a real guarded recursive resource model and validates the complete
domain-equation pipeline.  It is not yet the full extensible Iris resource
signature (`iResF`) with a family of user-selected ghost functors and invariant
namespaces.  That extensible signature is the next milestone.
