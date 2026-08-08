# M14 Extensible Resource Signature Audit

## Result

M14 generalizes the single guarded resource from M13 into a reusable resource
signature parameterized by a client-provided functor `G`:

```text
IrisResourceF G = GuardedResourceF × G
IrisPropF G     = UPredOF (IrisResourceF G)
IPre G          ≃ UPred (IrisResourceF G (IPre G) (IPre G))
```

The plugin must provide `OFunctor`, `OFunctorContractive`, and
`UCMRAFunctor`. These requirements make the recursive equation well-founded
and ensure all resource operations preserve step-indexed validity.

## New proved infrastructure

- binary product composition for arbitrary OFunctors;
- preservation of local contractiveness by product;
- preservation of CMRA/UCMRA structure and validity by product;
- generic `ExtensibleIris` recursive solution parameterized by a plugin;
- public generic `IPre`, `IRes`, `IProp`, `fold`, and `unfold` interfaces;
- both inverse laws for every lawful plugin;
- concrete `UnitGhostPlugin` based on `GhostMap Unit`;
- simultaneous composition of a guarded recursive slot and a named plugin slot.

## Verification

```powershell
lake build
lake env lean .\Demo.lean
```

The release is also scanned for `sorry`, `admit`, and user-declared `axiom`.

## Boundary

M14 supplies type-safe compile-time extensibility through functor composition.
It is not a runtime heterogeneous registry. This matches the normal theorem-
prover design: the chosen ghost signature is fixed when an Iris instance is
constructed, while clients can build larger signatures by repeated products.
M15 will connect ownership, updates, masks and invariants directly to this
final recursive `IProp`.
