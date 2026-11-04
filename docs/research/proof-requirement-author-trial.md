# Discovering reusable proof requirements: author trial preparation

For [#293](https://github.com/VladimirMarko/conaled/issues/293), two small Lean
tasks now have concrete source proofs, target interpretations and private checked
reference solutions. Independent author observations are pending. Preparation
does not establish a benefit from dependency assistance.

The [prospective protocol](../../experiments/proof-requirement-authoring/protocol.md)
fixes the contracts, independent manual/assisted allocation, 20-minute caps,
allowed sources, assistance and stopping rules. The
[task statements](../../experiments/proof-requirement-authoring/tasks.md) specify
exact equality and selected subtype data. E reverses three blocks and is held out
from #286's published arguments. W adapts that report's selected right-unit
witness with a noninjective length observation and is calibration-derived.

## Source result and bounded implementation

Johnsen–Lüth's [*Theorem Reuse by Proof Term Transformation*](https://ebjohnsen.org/publication/04-tphols/04-tphols.pdf),
§§2.1–2.3, printed pp. 3–4, separates exposing assumptions, abstracting symbols
and abstracting types. Symbol abstraction requires higher-order variables;
type abstraction requires type variables and attention to type-specific rules.
The inspected paper presents an Isabelle implementation, not a Lean importer.
Its discussion of applicability conditions does not justify a globally weakest
requirement claim for this trial. The PDF was inspected during preparation on
2026-11-04. The local starting revision was
`2525b12052e4c85c57f9050dbf18f7a36ba2ef19`.

The [#286 comparison](proof-requirement-comparison.md) provides paper derivations
and the prior trials provide logging methodology. This trial supplies native
Lean source proofs and ordinary parameterized replay, not a new proof-term
extractor or a change of foundational logic. A manually prepared
[dependency ledger](../../experiments/proof-requirement-authoring/dependency-ledger.md)
is the entire assistance intervention. Its task designer chose opaque lemma
boundaries and validated them against printed terms and checked replays.

## Checked claims and statement review

[Public support](../../Examples/ProofRequirementSupport.lean) contains only the
completed concrete arguments and target operations.
[Coordinator references](../../Examples/ProofRequirementReference.lean) are
withheld from the isolated author handoffs until attempts close.

| Claim | Meaning and retained checks |
|---|---|
| Generic reversal | For arbitrary carrier, operation and reversing map, reversal of the operation twice yields the specified three-block equation. The anti-homomorphism law suffices; associativity is absent. List and Boolean models establish inhabited assumptions and derive concrete empty/nonempty cases. |
| Source replay and revision | The original body uses double reversal twice and no ambient append-empty evidence. The faithful generic replay retains involution; the revised proof omits that detour. A constant-empty reversing map satisfies the revised interface but fails involution at `[1]`. |
| Selected witness | For arbitrary observation result type, observed right-unit suffices to return the actual input in the required subtype. Full right-unit also replays the original proof. The list result equals the concrete source as subtype data; Boolean and empty/nonempty list cases use the generic construction. |
| Missing laws | Boolean left projection is associative but fails reversal and the requested equation. Nat addition with unit candidate 1 admits a witness at input 0 but cannot select 0. Neither rejection relies on an empty carrier. |
| Erasure | At list input `[1]`, `[1]` and `[2]` satisfy the same length predicate and have unequal first projections. Their `Nonempty` proofs are equal; no function from that erased proof can recover every original first projection. This does not deny choosing some inhabitant. |

Quantifier scopes, equation directions, operation order and subtype projections
were reviewed against the task's independent calculations. No interface field
assumes the three-block client theorem. Full right-unit is an acceptable
sufficient author interface for W; the reference's weaker observation law is
not an unannounced grading requirement. Proof equality uses Lean's ordinary
proof irrelevance, while data equality remains exact. The full integration audit
must include all successful author claims as well as these preparation modules.

## Preparation cost and current decision

The [preparation record](../../experiments/proof-requirement-authoring/preparation/record.md)
separates task design, private solutions, supplied assistance, compiler failures,
environment work and archived checks from author effort. First checks exposed
an implicit-argument mistake in a List lemma call; it was repaired before
freeze. No author saw that failed preparation artifact.

Current decision: investigate with the frozen author comparison. Retain, revise
or drop the assistance format only after recorded attempts are assessed against
the prospective rubric. Mathematical generality, interface/documentation cost,
Lean encoding and observed author work will be reported separately. This sample
cannot establish human usability, causal savings, tool productivity or a
universal weakest theory. #290/#235 own any later extractor or broader trial;
no #108 theorem selection or preparation is part of this work.
