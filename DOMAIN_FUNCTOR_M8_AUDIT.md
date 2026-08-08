# Domain Functor M8 audit

## Purpose

M8 begins the type-level domain-equation infrastructure required for a genuine
recursive Iris proposition model.  A value-level guarded fixed point cannot
solve this type equation.

## Implemented

- Mixed-variance `OFunctorPre` (contravariant first argument, covariant second).
- `OFunctor` with OFE/COFE objects, non-expansive mapping, identity law, and
  composition law.
- `OFunctorContractive`, expressing that mapping gains one observation step.
- Constant, identity, and later functors.
- Contractiveness instances for constant and later functors.
- Executable typechecking tests for functor maps.

## Boundary

The tower-based COFE solver, resource functors, `UPred` functor, and final
`fold`/`unfold` isomorphism are not part of M8.  No recursive `IProp` instance is
claimed yet.
