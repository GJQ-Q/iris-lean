# M19 invariant identity redesign audit

## What changed

M19 begins the corrected invariant resource architecture:

* `InvariantId` is an internal fresh ghost identity;
* `InvariantKey` separates that identity from the mask `Namespace`;
* invariant bodies are guarded by `Later` and stored in `Agreement` cells;
* `Catalog` is keyed by `(namespace, internal identity)`;
* `Ghost` is an authoritative camera over that catalog;
* public `handle` values are authoritative fragments and are duplicable.

## Proved properties

* `handle_op_idem`: a public handle can be duplicated without changing the
  resource;
* `same_namespace_distinct_ids_valid`: two invariants can share a namespace
  when their internal names differ;
* `same_id_forces_body_agreement`: reusing one internal identity forces the
  guarded bodies to agree at the appropriate step index;
* catalog entries are valid and use a total core.

These properties directly repair the two structural defects found after M18:
namespace-as-identity and exclusive public invariant assertions.

## Semantic boundary

M19 does not yet replace `WorldIris.WorldPlugin`. The corrected catalog must
next be turned into a recursive OFunctor and incorporated into the solved
world resource. Fresh allocation and an exclusive open/close token will then
be proved against its authoritative state.

## Verification

* `lake build`: successful, 98 jobs.
* `lake env lean .\Demo.lean`: successful.
* No `sorry`, `admit`, user `axiom`, or `unsafe` declaration.

## Revised completion

First-three-layer completion is approximately **88%** after this corrective
milestone. This percentage is intentionally conservative and refers to a
semantically correct Iris-compatible endpoint.
