# VFA, FDSA and PFDS integration

This integration receives the three textbook developments into the existing
`conaled` library and connects selected results through its shared contracts.
Library coherence takes priority; useful mathematics, including unfinished
proofs and counterexamples, keeps an explicit disposition. Receiving a source
branch or proving a shared client does not establish whole-book acceptance.

The integration checkpoint owns the current requirements, local issues and
acceptance evidence in `books/common/{REQUIREMENTS.md,ISSUES.json,STATUS.md}`.
Those paths are inside the checkpoint, not this repository. This note owns the
source and interface correspondence; it does not duplicate the changing
validation ledger or the books' source-coverage records.

## Source provenance and merge decisions

The integration starts from pinned master
`9175737c2b14ef738cfb6c2cdc68d885c0805ddd`. The three incoming candidates share
the older source base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

| Source | Received candidate | Integration merge |
| --- | --- | --- |
| FDSA | `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe` | `7d9cf6f091e11d24721184706e8c9f6d067bfa09` |
| PFDS | `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` | `3fe0ef512e6bae67eb4a99a414689ba0c20657fd` |
| VFA | `eae9e110adc7ba1cc28386448a6deef23e406c13` | `f5441b0e52cceea6efe825f823925319731f4c69` |

These merges preserve the incoming ancestry. Subsequent shared clients and
potential reconciliation extend this union. FDSA's mapped-potential work also
uses retained donor `12cb14fc98b8617b3b625620da8e60936daba340`, which was absent
from the FDSA candidate. The checkpoint's `source/refs.json` owns all original
reference identities; the three candidate heads are not its entire mathematical
inventory.

The FDSA merge combines both theorem families in
[Resources.Growth](../../Applications/Resources/Growth.lean): master's
asymptotic carrier/cast bridges and FDSA's binary ceiling-log bounds. All
nonblank, non-import lines from each parent remain in order. The three merges
also retain both parents' public imports in `SquareApplications.lean`.

Seven PFDS and nineteen VFA conflicting files receive the pinned-master
versions. Direct comparison with the common source base shows that those
incoming modifications change only imports and blank lines; comments,
declarations and proofs are unchanged. The resolved blobs equal the receiving
parent and pinned master exactly. The compact `merge-resolutions.json` receipt
records each path, source/receiving/resolved blob identity and comparison. This
import-only decision does not describe the substantive potential reconciliation
or the new integration proofs. Pinned-master architecture and workflow govern
the receiving library, with the user's checkpoint-local issue-tracking and
exact-pin native-toolchain exceptions.

## Shared owners and connected clients

### Sorting: full values, permutations and a common specification

[TextbookSorting](../../Examples/TextbookSorting.lean) connects VFA's
[FirstPair](../../Applications/Sorting/FirstPair.lean) permutation theorem to
the ordinary sorting uniqueness results used by FDSA. Its
`sort_after_compareSwap` applies to any correct sorter for an antisymmetric
relation on the actual values. The Boolean first-pair comparator is arbitrary:
the proof needs its permutation property, not a claim that one comparison sorts
the whole list.

`preprocessedQuickSquare` and `floorSquare` give two implementations the same
`sortOn id` specification through the existing exact representation. Their
`jointSquare` uses the existing `synchronize` construction and its
`synchronized` representation, rather than introducing a textbook-specific
implementation interface. `paired_outputs` obtains equality of the two
outputs from that construction's agreement theorem; `mixed_duplicates`
transfers an existing expected result through this public relationship.

The boundary is full-value antisymmetry. Sorting records by a noninjective key
does not make equal-key records interchangeable. `equal_key_order_matters`
exhibits the stable-sort distinction after reversing two Boolean records with
the same key. Output equality also makes no claim about equal comparison
counts, allocation, sharing or runtime. The more general VFA specification
draft remains separately owned below.

### Sequences: relational full-list behavior before summaries

[TextbookSequences](../../Examples/TextbookSequences.lean) reuses
[AbstractStack](../../Applications/Sequences/AbstractStack.lean)'s separate
`Ops` and relational `Laws`, the FDSA
[DifferenceListCosts](../../Examples/DifferenceListCosts.lean) materializer,
and [OrderedSummary](../../Applications/Sequences/OrderedSummary.lean).
`append_materialize_correct` relates an actual successful abstract-stack append
to the materializer's full output list. It preserves order and repeated
occurrences without imposing a total decoder on every stack representation.

The theorem retains two explicit observations: stack append makes
`4 * xs.length + 1` primitive calls, while materialization records
`4 * xs.length + 2` closure creation/application events. These are different
tariffs, not a runtime comparison. The successful stack result also requires
enough fuel for the left list.

For the concrete stack, `custom_summary_materialize` and
`custom_summary_append` transport the full-list result to an arbitrary monoid
summary. Multiplication retains sequence order; neither commutativity nor an
injective summary is assumed. `append_head_materialize` separately connects
the actual optional result's head observation. Equal summaries are never used
to infer equal lists.

The connected cases include repeated tagged values with an ordered free-monoid
summary, successful empty input over the uninhabited `Empty` payload, and
insufficient fuel. In the last case the stack computation returns `none`
although the total materializer still returns its list and observation. Thus
failure, successful empty output and ordinary successful output remain distinct.

### Potential accounting: one executor and a shared telescoping core

[Resources.Potential](../../Applications/Resources/Potential.lean) reconciles
PFDS's generic same-carrier and signed interfaces with the extra FDSA donor's
mapped, invariant-aware accounting. `Resources.run` remains the shared executor;
`budget` follows its actual successive states with a separately typed charge.
The same-carrier public laws specialize the mapped core through the identity
homomorphism, and existing natural-number clients remain specializations.

The ordered exact laws preserve both boundary potentials without assuming
commutativity. Inequality laws state their order and nonnegativity premises;
neither initial credit nor the observation map's meaning is implicit. The
retained signed-potential and transport clients join
[MappedPotentialAccounting](../../Examples/MappedPotentialAccounting.lean)'s
mapped, fractional, invalid-state and ordered-observation cases. The
[potential-accounting correspondence](fdsa-potential-accounting.md) owns the
precise source obligations, declarations, minimal assumptions and exclusions.

## Useful mathematics still owned outside this component

The preservation audit inspected branch tips and standalone mathematical
records, not only the three candidates. It identified 65 FDSA Lean paths absent
from its candidate, plus existing-path variants, and five VFA standalone
drafts. The potential donor above is one selected incorporation from that
larger set. Counts identify preservation scope, not required new public files.

| Preserved family | Checkpoint-local owner and disposition |
| --- | --- |
| FDSA tree folds, accumulators, traversal observations, rotations, ordered search, leftmost extraction, Braun shape and Chapter 4 branches | **INT-020**, integration owner: compare capabilities with current tree owners before receiving proofs. Preserve Chapter 4's original base `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`, 76 obligations and 11 exercises. A shared prerequisite does not close the chapter. |
| FDSA ADT refinement, priority observations, logarithm bounds, accumulated work and permutation expectation/joint-placement drafts | **INT-020**, integration owner: retain source/review evidence and give each capability an incorporation, supersession or preserved-pending disposition. Existing-path variants require capability comparison, not wholesale file replacement. |
| VFA sorting specifications, table observations, positive keys, unary comparison costs and queue-peek counterexample | **INT-021**, integration owner: preserve ordering/multiplicity hypotheses, presence versus default lookup, shifted key inverses, actual unary recursion tariff, and the reachable repeated-reversal counterexample. None is closed by the three shared clients alone. |

PFDS's wrapped historical output tree contains no additional absent Lean path
after normalizing the old `conaled/` directory prefix. It should not become a
second active library. Its coverage matrix, paper mathematics, source
obligations and forward cost contracts still constrain **INT-001**; importing
the candidate does not accept its unfinished textbook coverage.

Shared implementation work is tracked by **INT-010–013**. Final acceptance is
owned by **INT-090** and **INT-091**: the full applicable build, exhaustive
three-axiom audit and independent Standards/Spec reviews must describe the same
candidate and retain the original integration base through fixes. Historical
approvals and focused elaboration establish only their recorded scopes. The
checkpoint stores current outcomes, unresolved findings and durable recovery
instructions, so this correspondence need not become another status ledger.
