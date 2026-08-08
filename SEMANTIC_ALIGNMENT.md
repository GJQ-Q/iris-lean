# Semantic alignment record

Reference: official Iris-Lean `4a361b8da24ff73cc5fb8650eb8ed1d6b1c4573c`.

| Stable construction | Alignment decision |
|---|---|
| `OFE` | Indexed equivalence, equality at every index, downward closure. |
| `COFE` | Cauchy chain plus a limit agreeing at every observation depth. |
| `CMRA` | Partial core, operation, indexed validity, camera laws and extension. |
| `ValidAt M n` | A resource bundled with `validN n` evidence. |
| `UPred.mono` | Uses `IncludedN n`, not exact resource inclusion. |
| UPred distance | Agreement on every valid resource at all lower indices. |
| UPred COFE | Limit is the diagonal of the Cauchy chain. |
| `UPred.own` | Uses step-indexed inclusion. |
| `UPred.sep` | Uses step-indexed decomposition `x ≡{n}≡ a ⋅ b`. |
| `UPred.later` | True at zero; observes the predicate one step earlier. |

Additional v0.2/v0.3 alignment:

| Construction | Alignment decision |
|---|---|
| `wand` | Quantifies over lower indices and valid resource extensions. |
| `emp` | Ownership of the UCMRA unit. |
| `basicUpdate` | Quantifies over every lower index and compatible frame and may choose an updated resource per observation. |
| BI laws | Includes sep commutativity/associativity/unit and wand introduction/elimination. |
| `plainly` | Evaluates its body at the UCMRA unit. |
| `persistently` | Evaluates its body at the derived total camera core. |
| ownership update | A frame-preserving camera update entails the corresponding logical basic update. |
| update composition | Nested basic updates collapse to one basic update. |
| abstract BI API | Clients can quantify over `BIBase` and `BI.Laws` without inspecting UPred. |
| bupd frame | A framed resource is preserved across a basic update. |
| modality metric laws | Later is contractive; plainly, persistently and bupd are non-expansive. |
| non-discrete regression | `Later Bool` distinguishes step-indexed equality from Lean equality. |
| later type former | Standard one-step-later OFE/COFE with a contractive `next`. |
| Agreement raw carrier | Nonempty lists, matching the pre-quotient official construction. |
| Agreement raw distance | Hausdorff lifting of indexed OFE distance. |
| Agreement raw validity | Every pair of represented values agrees at the current index. |
| Agreement quotient | Quotient by same elements makes operation commutative as Lean equality. |
| Agreement OFE | Hausdorff distance lifted through the quotient. |
| Agreement CMRA | Total idempotent core, indexed validity and camera extension law. |
| ViewRel | Step-indexed relation with official monotonicity, validity and unit laws. |
| AuthViewRel | A valid authority whose fragment is included at the current index. |
| `PosRat` | Strictly positive exact Lean rational, preventing negative or zero owned fractions by construction. |
| `DFrac` | Official three constructors (`own`, `discard`, `ownDiscard`); owned shares add exactly, discard knowledge is persistent, and validity distinguishes owned-with-discarded. |
| Option OFE | Constructor-sensitive indexed distance, lifting the underlying OFE distance through `some`. |
| Option CMRA | `none` is the unit; `some` composition and validity lift the underlying camera. A conservative `none` core supports arbitrary partial-core cameras. |

| `View R` carrier | `Option (DFrac × Agreement A)` authority paired with a `B` fragment, matching official Iris-Lean. |
| View validity | Optional authority validity plus an Agreement witness related to the fragment by `R`; authority-free fragments require an `R` witness. |
| CMRA core stability | Presence or absence of a partial core is stable under indexed OFE distance. |
| Option core | Always has an outer core and preserves the underlying optional partial core. |
| View CMRA | Componentwise operation/core, relation-based validity, camera extension inherited through the product representation. |
| View update | Full-authority updates quantify over every step index and compatible fragment frame; framed competing authority is rejected by DFrac validity. |
| `Auth A` | Public specialization of `View` to `AuthViewRel`; no parallel or simplified authoritative semantics is introduced. |
| Auth validity | A valid full authority plus fragment yields authority validity and indexed fragment inclusion. |
| Auth updates | Public update/allocation/deallocation rules are wrappers around the audited frame-preserving View rules. |
| Predicate update | `FramePreservingUpdateP x P` preserves every compatible frame while allowing a target satisfying `P` to be selected per index and frame. |
| View/Auth predicate update | Relation-level existential choices are lifted to public predicate-valued camera updates. |
| Optional update frame | Updates quantify over `Option M`, matching Iris: `none` is no frame and `some m` is a concrete frame. |
| UCMRA update rule | Ordinary resource frames suffice because the unit represents the no-frame case. |
| Local update | A pair-to-pair rule preserving indexed validity and decomposition through every optional frame, matching official Iris-Lean `LocalUpdates.lean`. |
| UCMRA local update | The optional-frame definition is proved equivalent to quantifying over ordinary frames. |
| View local-update lifting | A fragment local update plus preservation of the View relation lifts to synchronized full-authority/fragment pairs. |
| Auth local-update lifting | The View theorem is re-exported through the public `Auth` specialization. |
| Product local update | Component local updates lift pointwise to the product camera. |
| Option local update | Updates lift through `some`; allocation from `none` requires global validity of the allocated resource. |
| `MonoNat` | Discrete max camera: composition records the greatest observation, unit is zero, and inclusion coincides with `≤`. |
| Monotone counter ghost | `Auth MonoNat` provides an authoritative counter and lower-bound fragments; authority growth lifts to a UPred basic update. |
| Counter fragment allocation | A fragment may be issued exactly when its lower bound does not exceed the authority; growth and issuance can be atomic. |
| Ownership composition | Camera composition corresponds in both directions to separating conjunction of ownership predicates. |

Not claimed in v0.21:

- cancelability/id-freeness based local updates and generic deletion rules;
- recursive IRes/IProp;
- invariant or fancy update;
- program logic or WP.

These claims are deliberately withheld instead of being filled by simplified
substitutes.
