# LeanIrisX Logic Core M1 — semantic audit

## Result

This milestone turns the previous semantic core into a reusable logical
interface. It builds with Lean 4.32.2 and contains no `sorry`, `admit`, declared
`axiom`, or `unsafe` declaration in project Lean sources.

## Implemented and checked

- `UPred` over valid step-indexed CMRA resources.
- BI entailment, pure propositions, conjunction, disjunction, separating
  conjunction, separating implication, later, persistent/plain modalities,
  and basic update.
- Ordinary intuitionistic implication with Kripke semantics over every smaller
  step and every resource extension. It is distinct from the magic wand.
- Universe-polymorphic universal and existential quantification.
- Introduction/elimination rules for conjunction, disjunction, implication,
  universal quantification, and existential quantification.
- Stable `IProp M` public facade and BI type-class implementations for `UPred`.
- Iris-aligned interfaces: `Persistent`, `Affine`, `Absorbing`, and `Timeless`.
- Concrete tests of modus ponens and existential introduction.

## Evidence

```powershell
lake build
lake env lean .\Demo.lean
rg -n '\b(sorry|admit|axiom|unsafe)\b' . -g '*.lean' -g '!/.lake/**'
```

The build completes 51 jobs. `Demo.lean` reports that the new implication and
quantifier demonstrations do not depend on any axioms. An empty `rg` result is
the expected placeholder-audit result.

## Honest scope boundary

M1 completes the intended public core of the UPred/BI logic layer used by this
project. It does **not** claim feature parity with the full Rocq Iris library.
It does not yet include invariants, fancy updates/masks, namespaces, weakest
preconditions, language semantics, HeapLang, or proof-mode automation.

Lean's standard `propext`, quotient soundness, and classical choice may appear
in older quotient-based algebraic constructions. They are kernel-visible
foundations, not unfinished proof placeholders.

## Next milestone

Proceed to the resource/modality layer: ghost names and a global resource
camera, fancy updates with masks, invariant allocation/open/close rules, and a
small client case study. Only after that should the project define a language,
weakest precondition, and adequacy.
