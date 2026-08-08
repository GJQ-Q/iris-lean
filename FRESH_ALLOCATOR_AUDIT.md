# Fresh Allocator M4 audit

## Result

M4 implements a proved fresh-name allocator backed by the existing
authoritative monotone-natural camera. The project builds successfully (63
jobs), the demo exits with code 0, and project Lean sources contain no `sorry`,
`admit`, declared `axiom`, `unsafe`, or `native_decide` declaration.

## Model

`FreshNameState.next = n` means exactly the ghost names below `n` are already
allocated. Allocation returns `n` and advances the state to `n + 1`.

- Before allocation: `¬ Allocated s (fresh s)`.
- After allocation: `Allocated (advance s) (fresh s)`.
- Previously allocated names remain allocated.
- The authoritative state is represented by `Auth MonoNat`.
- A token for name `γ` carries the lower bound `γ + 1`.

## Proved ghost update

`FreshNameGhost.allocate_update` proves the frame-preserving update

```text
authority s ~~> authority (advance s) ⋅ token (fresh s)
```

`token_proves_allocated` proves that validity of an authority/token pair
implies that the token's name is below the current high-water mark.

`UPred.allocateFresh` lifts the camera update into a logical basic update and
separates the advanced authority from the newly issued token.

No fixed ghost name is used and no freshness premise is assumed from the
caller.

## Verification

```powershell
lake build
lake env lean .\Demo.lean
rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b' . -g '*.lean' -g '!/.lake/**'
```

Expected: 63 successful build jobs, Demo exit 0, and a clean scan.

## Remaining work

The allocator now supplies the freshness mechanism needed by ghost allocation.
The next milestone must combine the allocator state with the global resource
camera and construct a concrete mask-changing UPred fancy-update model. An
invariant world-satisfaction model remains necessary before concrete invariant
instances can be claimed.
