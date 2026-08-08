# LeanIrisX M12: resource morphisms and UPred functor audit

## Result

M12 adds the semantic bridge between resource algebras and the M11 recursive
COFE solver. It implements the same architectural boundary used by Iris:

```text
non-expansive map
      + validity preservation
      + operation preservation
                ↓
             CMRAHom
                ↓
          UCMRAFunctor F
                ↓
             UPredOF F
```

`UPredOF F` reverses the resource functor's variance as required by predicate
reindexing. Its `OFunctor` and `OFunctorContractive` instances are proved from
the corresponding laws of `F`.

## Kernel-checked claims

- CMRA morphisms preserve step-indexed inclusion.
- `UPred.map` preserves uniform-predicate monotonicity.
- predicate reindexing is non-expansive.
- `UPredOF` satisfies identity and composition laws.
- a contractive resource functor induces a contractive proposition functor.
- the induced proposition functor is accepted by the M11 COFE solver.
- both recursive fold/unfold laws are tested on a concrete unital resource
  functor.

## Scope boundary

The constant resource-functor test is an interface validation, not the final
Iris resource model. The next milestone must define the non-constant,
later-guarded `IResF`, prove its UCMRA-functor laws, and instantiate the final
recursive `IProp`. M12 makes that construction type-safe and semantically
meaningful; it does not claim that `IResF` already exists.

No `sorry`, `admit`, or user-declared `axiom` is permitted in the deliverable.
