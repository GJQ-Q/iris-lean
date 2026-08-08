# LeanIrisX M11: contractive COFE solver audit

## Result

M11 completes the generic recursive-domain solver for a mixed-variance,
contractive OFE functor `F`. Given the stage-one seed, the implementation
constructs a complete OFE `Fix F seed` and a kernel-checked isomorphism

```text
F (Fix F seed) (Fix F seed)  ≃  Fix F seed.
```

This is an inverse-limit construction, not bounded unrolling and not a mock
datatype.

## Kernel-checked components

- finite stages and embedding/projection pairs;
- exact retraction `down_up`;
- approximate section `up_down`, using functor contractiveness;
- the infinite coherent `Tower`, with OFE and COFE instances;
- iterated maps `upN` and `downN`;
- non-expansive stage embeddings and projections;
- `Tower.embed_up` and observation-indexed `Tower.embed_self`;
- the Cauchy `unfoldChain`;
- non-expansive `towerFold` and `towerUnfold`;
- both inverse laws `towerFold_unfold` and `towerUnfold_fold`;
- public `Fix.fold`, `Fix.unfold`, `Fix.fold_unfold`, and `Fix.unfold_fold`.

## Trust boundary

The project contains no `sorry`, `admit`, or user-declared `axiom`. Expected
Lean foundations such as propositional extensionality and quotient soundness
can appear in `#print axioms`; these are standard Lean kernel/library
dependencies and are not replacement assumptions for the solver laws.

## Scope boundary

This milestone solves the generic COFE domain equation. It does not by itself
instantiate the final Iris resource functor or replace the current
parameterized `IProp M` by the recursively solved Iris proposition model. That
semantic integration is the next milestone.
