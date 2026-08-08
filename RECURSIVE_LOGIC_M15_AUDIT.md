# M15 Concrete Recursive Logic API Audit

## Result

M15 connects the solved extensible resource equation to a concrete proposition
and ownership API. Clients no longer manipulate the COFE solver directly.

## Added interface

- `ownResource`, `ownGuarded`, and `ownNamedUnit` over the final `IRes`;
- `validResource` and the concrete basic update `bupd`;
- resource ownership splitting and recombination;
- lifting frame-preserving CMRA updates to logical basic updates;
- simultaneous ownership of guarded core and plugin resources;
- a proved conflict for duplicated guarded exclusive ownership;
- a typed `GhostOwn IProp Unit` instance;
- proved named-unit splitting and validity interfaces;
- client-level regression tests using only the public recursive logic API.

## Verification

```powershell
lake build
lake env lean .\Demo.lean
```

All Lean sources are scanned for `sorry`, `admit`, and user `axiom` tokens.

## Remaining semantic boundary

This milestone deliberately does not manufacture a mask-insensitive
`FancyUpdate` instance. Such an instance would typecheck but would not model
Iris invariants correctly. The remaining third-layer work is to include the
invariant registry/world state in the recursive resource signature and derive
concrete fancy-update and invariant rules from world transitions.
