# M20 recursive world V2 audit

## Delivered

M20 integrates the corrected invariant identity design into a newly solved
recursive world domain.

* `NamedInvariantRegistryF` is a contractive `OFunctor` and `UCMRAFunctor`.
* Registry keys are `(Namespace, GhostName)`, not namespaces alone.
* `WorldPluginV2` combines the named registry, a separate duplicable handle
  resource, and the ordinary ghost plugin.
* `WorldIrisV2.IPre`, `IRes`, and `IProp` solve the new recursive domain.
* Fold/unfold laws are exposed.
* Two identities in one namespace compose validly.
* Reusing one identity conflicts.
* Public handle slots are idempotent/duplicable.

## Design decision discovered during integration

The M19 agreement catalog cannot itself be placed directly in the recursive
functor yet because the current `Agreement` implementation has OFE and CMRA
instances but no COFE instance. M20 therefore uses the already complete
guarded-exclusive registry for body storage and a separate duplicable handle
slot. No cast or fake COFE instance was introduced.

## Remaining semantic bridge

The handle identity must still be authenticated against its registry body in
world satisfaction. The final logic release must then prove fresh allocation,
exclusive open/close ownership, world-aware fancy update, and the concrete
invariant laws.

## Verification

* `lake build`: successful, 101 jobs.
* `lake env lean .\Demo.lean`: successful.
* No `sorry`, `admit`, user `axiom`, or `unsafe` declaration.
* Existing universe co-occurrence lints are non-failing warnings.

## Completion estimate

Strict first-three-layer completion: approximately **93%**. This estimate is
lower than the earlier projected 94–96% because the missing Agreement COFE and
the remaining body/handle authentication bridge are now explicit audit items.
