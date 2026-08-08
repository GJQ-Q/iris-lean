# LeanIrisX — First Three Layers Integration Candidate

This directory is the consolidated successor of milestones M1–M20.  It adds a
single recursive world resource containing four deliberately separate
components:

- guarded invariant bodies indexed by `(Namespace, GhostName)`;
- non-unit, idempotent public invariant handles;
- exclusive close permissions;
- an extensible client ghost-state slot.

The main entry point is `LeanIrisX.Logic.WorldResourceFinal`.  Its checked
theorems establish validity of registry/handle packages, duplication and
non-triviality of handles, conflict of duplicated close permissions, and
identity-level authentication.  See `FIRST_THREE_LAYERS_CANDIDATE_AUDIT.md`
for exact guarantees and the remaining boundary.  This is an integration
candidate, not a claim that the complete Iris invariant rule has already been
derived.

中文材料见 [`项目说明.md`](项目说明.md) 和
[`中文审计报告.md`](中文审计报告.md)。

Build and verify with:

```powershell
lake build
lake env lean .\Demo.lean
```

## Historical milestones

# LeanIrisX Recursive World Resource M16

M16 integrates a guarded invariant registry into the final recursive resource
equation. See `WORLD_RESOURCE_M16_AUDIT.md` for its proof boundary.

The sections below retain the history of earlier audited milestones.

M15 exposes concrete ownership and basic-update operations over the solved,
extensible recursive `IProp`. See `RECURSIVE_LOGIC_M15_AUDIT.md`.

The sections below retain the history of earlier audited milestones.

M14 provides compositional resource functors and a generic recursive Iris
model parameterized by a user plugin. See `EXTENSIBLE_RESOURCE_M14_AUDIT.md`.

The sections below retain the history of earlier audited milestones.

M13 adds the first nonconstant guarded resource functor and solves the recursive
equation `IPre ≃ UPred (GuardedExcl IPre)`. See
`GUARDED_RESOURCE_M13_AUDIT.md` for proof evidence and the exact boundary.

The sections below retain the history of earlier audited milestones.

This milestone adds a proved authoritative high-water-mark allocator for fresh
ghost names and lifts allocation into UPred. See `FRESH_ALLOCATOR_AUDIT.md` for
the model, proof evidence, and remaining semantic boundary.

This milestone adds a concrete global GhostMap CMRA and step-indexed named
ownership for UPred. See `GLOBAL_RESOURCE_AUDIT.md` for proof evidence,
corrections to the M2 interface, and the remaining invariant-model boundary.

This milestone adds concrete namespaces/masks and law-constrained fancy-update,
ghost-ownership, and invariant interfaces. See `RESOURCE_INTERFACE_AUDIT.md`
for the exact semantic boundary and verification evidence.

This milestone adds an audited Iris-style logic interface and stable `IProp`
facade to the semantic foundation. See `LOGIC_CORE_AUDIT.md` for exact scope,
verification commands, and remaining work.

This is the first post-audit semantic-alignment release.

Included in the stable API:

- OFE and COFE;
- non-expansive and contractive maps;
- guarded fixed points;
- the core CMRA/UCMRA interface;
- discrete exclusive and product cameras;
- validity-indexed `UPred`;
- step-indexed inclusion for monotonicity and ownership;
- OFE and COFE instances for `UPred`;
- the later modality.
- BI conjunction, disjunction and quantifiers;
- separating implication (`wand`) and its introduction/elimination laws;
- `emp`, separating associativity and unit laws;
- a step-indexed, frame-quantified basic update modality.
- deterministic frame-preserving camera updates connected to logical ownership;
- basic-update composition/idempotence;
- `plainly`, interpreted at the UCMRA unit;
- `persistently`, interpreted at the camera core;
- persistent elimination and duplication laws.
- an abstract `BIBase` API and a separate `BI.Laws` law bundle;
- a certified UPred instance of the abstract BI interface;
- public BI notation independent of the UPred representation;
- the basic-update frame rule;
- contractiveness of later and non-expansiveness of key modalities.
- a genuine non-discrete `Later α` OFE;
- completeness of `Later α` whenever `α` is complete;
- a contractive `Later.next` map;
- regression tests showing that depth zero hides a difference which depth one observes.
- the nonempty-list raw carrier of generic Agreement;
- Hausdorff lifting of OFE distance to raw agreement values;
- pairwise step-indexed agreement validity;
- proofs for singleton validity, duplicated validity and conflict detection;
- a non-discrete `Later Bool` agreement test without `DecidableEq`.

`Agreement.Raw` remains the explicitly named pre-quotient representation.
v0.7 completes the public quotient construction:

- quotient by `Raw.SameElems`;
- representative-independent distance and validity;
- a non-discrete OFE instance;
- commutative, associative, idempotent composition;
- a full CMRA instance including the extension law;
- singleton injection through `toAgreement`;
- non-discrete CMRA regression tests over `Later Bool`.

Agreement is a CMRA, not a UCMRA: the official construction has no empty
nonempty agreement value.

v0.8 adds the audited relation layer required by View:

- generic step-indexed `ViewRel A B`;
- the `IsViewRel` monotonicity, validity and unit laws;
- congruence under OFE distance;
- the generic authoritative relation `AuthViewRel`;
- proof that `AuthViewRel` is a lawful view relation for every UCMRA;
- authority validity, fragment inclusion and fragment validity lemmas.

The full `View` carrier and CMRA are intentionally deferred until fractional
authority and the required option camera are available.

v0.10 corrects and strengthens those prerequisite cameras after direct
comparison with the official Iris-Lean source:

- exact rational discardable fractions (`DFrac`), with strictly positive
  owned shares represented by `PosRat`;
- exact addition of owned shares and validity bounded by one;
- the official three-way discardable fraction state: `own`, `discard`, and
  `ownDiscard`;
- `discard` is persistent but is not falsely treated as an ordinary unit;
- a step-indexed `Option` OFE and lawful option CMRA/UCMRA;
- conservative option cores (`none`) that are valid for arbitrary partial-core
  CMRAs;
- regression tests for two halves, over-allocation, option composition and
  option validity.

v0.10 also adds the official-shaped `View A B R` semantic layer:

- carrier `Option (DFrac × Agreement A) × B`;
- authoritative and fragment constructors;
- componentwise step-indexed OFE;
- componentwise operation and unit;
- indexed/global validity;
- the central theorem connecting authority-plus-fragment validity to `R`.

v0.11 completes the next audited step:

- CMRA partial-core existence is stable under OFE distance;
- every existing CMRA instance proves the strengthened law;
- Option now lifts the underlying partial core instead of discarding it;
- the total UCMRA core is proved non-expansive;
- `View R` has a full CMRA and UCMRA instance;
- the View proof includes indexed validity monotonicity, operation projection,
  partial-core laws and the CMRA extension law;
- client tests use `CMRA.validN` directly on authority/fragment compositions.

v0.12 adds frame-preserving View updates:

- simultaneous full-authority and fragment update;
- authority-only update;
- fragment allocation while changing authority;
- fragment deallocation while changing authority;
- explicit rejection of every frame containing a second full authority;
- end-to-end client tests for update, allocation and deallocation.

v0.13 adds the public authoritative camera API derived from `View`:

- `Auth A` is the specialization `View (AuthViewRel (A := A))`;
- `Auth.authoritative`, `Auth.authoritativeDFrac`, and `Auth.fragment` are
  stable client constructors;
- authority/fragment validity exposes both authority validity and indexed
  fragment inclusion;
- projection lemmas recover authority validity, fragment inclusion, and
  fragment validity from a valid combined resource;
- update, allocation, and deallocation rules delegate to the audited View
  frame-preserving update layer;
- client tests synthesize `CMRA (Auth Unit)` and `UCMRA (Auth Unit)` and use
  the public API without unfolding its representation.

v0.14 adds predicate-valued frame-preserving updates:

- `CMRA.FramePreservingUpdateP x P` permits the updated resource to be chosen
  from a predicate instead of fixing one result in advance;
- deterministic updates embed into predicate-valued updates;
- monotonicity and sequential composition (`updateP_trans`) are proved;
- `View.full_auth_frag_updateP` lifts a relation-preserving family of choices
  to a camera update;
- `Auth.authoritative_fragment_updateP` exposes the construction through the
  public authoritative API;
- client tests exercise both a native predicate update and deterministic
  embedding.

v0.15 corrects the update semantics after line-by-line comparison with the
official Iris-Lean `Algebra/Updates.lean`:

- both deterministic and predicate-valued updates quantify over `Option M`;
- `none` represents the absence of a frame and `some frame` a concrete frame;
- validity preservation for the no-frame case is exposed as a theorem;
- UCMRAs retain convenient ordinary-frame introduction rules;
- View, Auth, Exclusive, and UPred ownership updates were all re-proved against
  the corrected definition.

v0.16 implements the audited core of Iris local updates:

- `CMRA.LocalUpdate (x₁,x₂) (y₁,y₂)` uses optional frames, indexed validity,
  and indexed decomposition exactly in the shape of official Iris-Lean;
- reflexivity and transitivity are proved;
- equality-based congruence is provided for client rewriting;
- `localUpdate_iff_total` proves the ordinary-frame characterization for
  UCMRAs rather than assuming it;
- independent Unit tests check construction, composition, and the unital
  characterization without additional axioms.

v0.17 lifts local updates through the authoritative View construction:

- `View.localUpdate` follows the premise structure of official Iris-Lean
  `view_local_update`;
- a fragment pair local update and a relation-preservation premise produce a
  synchronized authority/fragment local update;
- frames containing only fragments are discharged using the underlying local
  update;
- frames containing a competing full authority are rejected through DFrac
  validity rather than silently ignored;
- `Auth.localUpdate` exposes the result through the stable public API.

v0.18 adds reusable local-update constructors:

- product local updates are built componentwise;
- an underlying local update lifts through `Option.some`;
- a globally valid resource can be allocated into an absent Option resource;
- tests compose two Unit local updates through Product and exercise real Option
  allocation.

v0.19 adds the first end-to-end reusable ghost state:

- `MonoNat` is a lawful discrete UCMRA with `max` composition and zero unit;
- indexed inclusion is proved equivalent to the ordinary natural-number order;
- `MonoNatGhost.Ghost` specializes the public `Auth` construction;
- validity of an authority/fragment pair proves that the observed fragment is
  bounded by the authority;
- an authority can grow from `k` to `m` when `k ≤ m`;
- the camera update is lifted through `UPred.own_update`, producing a genuine
  logical basic-update theorem for a monotone counter.

v0.20 completes the counter's basic client workflow:

- allocate any lower-bound fragment `m ≤ k` from authority `k`;
- grow an authority from `k` to `m` and issue a fragment for the new value in
  one frame-preserving update;
- lift both operations to UPred ownership basic updates;
- provide executable demonstrations for authority `8` issuing fragment `5`
  and authority `3` growing to `8` while issuing fragment `8`.

v0.21 exposes camera composition as logical separation:

- `UPred.own_op_sep` splits ownership of `a ⋅ b` into `own a ∗ own b`;
- `UPred.sep_own_op` recombines separated ownership;
- both generic laws are proved without additional axioms;
- the counter example now grows the authority and returns separately usable
  authoritative and fragment ownership under a basic update.

Intentionally excluded:

- the prototype `IProp`, `Invariant`, and `FancyUpdate` modules;
- a claim of complete Iris compatibility;
- WP and program logic.

Those features require recursive resource domains and world satisfaction and
will only enter the stable API after their semantics are implemented and audited.

Build on Windows:

```powershell
lake build
lake env lean .\Demo.lean
```
