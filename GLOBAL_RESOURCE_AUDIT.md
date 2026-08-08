# Global Resource M3 audit

## Result

M3 supplies a concrete homogeneous global ghost-resource model and its UPred
ownership interpretation. It builds successfully (60 jobs), the demo exits
successfully, and the project Lean sources contain no `sorry`, `admit`, declared
`axiom`, or `unsafe` declaration.

## Semantic correction to M2

M2 stated ghost validity as a pure, unindexed proposition. That is too strong
for a step-indexed CMRA. M3 replaces it with `GhostOwn.validProp`, an internal
logic proposition. The concrete UPred instance interprets it as `validN n a` at
the current observation depth. This matches step-indexed ownership semantics.

Allocation laws are separated from ordinary ownership laws. Fresh allocation
requires an allocator/authoritative construction; choosing a fixed natural
number would not be fresh and is therefore deliberately not implemented.

## Concrete constructions

- `TotalCore A`: evidence that a camera core is total.
- `GhostMap A = GhostName → A`.
- Pointwise OFE (from the existing function OFE).
- A proved pointwise CMRA instance, including validity, core laws, and CMRA
  extension.
- A proved pointwise UCMRA instance.
- Singleton resources at a ghost name, with composition and validity lemmas.
- `UPredGhost.namedOwn γ a`, represented by ownership of a singleton global
  resource.
- `UPredGhost.validProp a`, interpreted by current-step CMRA validity.
- Proof that named ownership composes.
- Proof that named ownership entails step-indexed validity.

## Kernel-visible dependencies

The global CMRA extension proof chooses the pointwise witnesses supplied by the
underlying CMRA extension law, so Lean reports `Classical.choice`. Function and
UPred extensionality may report `propext` and quotient soundness. These are
visible foundational dependencies, not unfinished proofs.

## Verification

```powershell
lake build
lake env lean .\Demo.lean
rg -n '\b(sorry|admit|axiom|unsafe)\b' . -g '*.lean' -g '!/.lake/**'
```

Expected: 60 successful build jobs, Demo exit 0, and a clean placeholder scan.

## Remaining work

M3 completes the concrete global resource and named-ownership component. It
does not yet instantiate fancy updates or invariants for UPred. The next model
milestone needs an authoritative fresh-name allocator and an invariant-state
camera/world-satisfaction construction before those instances can be proved.
