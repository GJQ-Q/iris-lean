# World Transition M7 audit

## New verified semantics

- Exact-name mask insertion and erasure, distinct from namespace-subtree removal.
- `openName`: moves one name from the closed set to the opened set.
- `closeName`: moves one name from the opened set to the closed set.
- Opening preserves the registered-name partition and `WSatAt`.
- Closing preserves the registered-name partition and `WSatAt`.
- After opening, the name is opened and no longer closed.
- After closing, the name is closed and no longer opened.

These are conservation theorems quantified over arbitrary worlds and names;
they are not executions of one hard-coded example.

## Semantic boundary

This milestone verifies the state-transition kernel below logical fancy update.
It does not yet claim that `FancyUpdate` has been instantiated for recursive
`IProp`, nor that the final invariant opening theorem has been derived.

## Verification

- `lake build`: passed, 74 jobs.
- `lake env lean Demo.lean`: passed.
- No `sorry`, `admit`, or project-declared `axiom`.
- Only Lean's standard extensionality, quotient, and classical principles occur
  in `#print axioms` where the underlying constructions require them.
