# LeanIrisX M10: inverse-limit COFE tower audit

M10 extends the finite tower kernel from M9 with the two ingredients needed
before the final recursive-domain isomorphism can be constructed.

## Added and kernel-checked

- `COFETower.up_down`: the embedding/projection composite agrees with the
  identity for the first `n` observations. This is where functor
  contractiveness is used.
- `COFETower.Tower`: the inverse-limit carrier, containing one point at each
  finite stage and an exact projection coherence equation.
- Pointwise `OFE (Tower F seed)`.
- Pointwise-limit `COFE (Tower F seed)`, including a proof that limits preserve
  the tower coherence equation.
- `Tower.proj`: reusable non-expansive finite-stage observations.

## Meaning

This is not a list or depth-bounded executable mock-up. `Tower` quantifies over
all natural-numbered stages, and its `COFE` instance constructs limits for
arbitrary OFE Cauchy chains. The finite stages remain computationally
generated, while the inverse limit is a genuine infinite mathematical object.

## Deliberate boundary

M10 does not yet claim the final solution of `X ≅ F X X`. The next milestone
must build the embeddings into the inverse limit and prove both fold/unfold
identities. Until those identities are checked, this module is accurately
described as the inverse-limit tower kernel, not the completed COFE solver.
