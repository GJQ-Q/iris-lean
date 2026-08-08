# COFE Tower M9 audit

## Implemented

- Added functorial non-expansiveness in the morphism arguments (`map_ne`).
- Packaged OFE/COFE carrier types for dependent tower stages.
- Constructed finite approximants `Stage F n`.
- Constructed the embedding/projection pair `up` and `down` at every stage.
- Proved the exact section/retraction equation at every finite stage:
  `down F seed n (up F seed n x) = x`.

## Why this matters

The exact retraction law prevents information invented at higher stages from
changing a lower approximation. It is a central invariant of the standard
Iris COFE tower construction.

## Boundary

M9 contains the finite-stage tower kernel. The approximate opposite equation,
the coherent infinite tower type, its COFE limit, and the final `fold`/`unfold`
isomorphism remain to be implemented. M9 does not claim the domain equation is
already solved.
