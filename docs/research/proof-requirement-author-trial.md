# Discovering reusable proof requirements: manual and assisted author trial

For [#293](https://github.com/VladimirMarko/conaled/issues/293), both independent
authors published reusable requirements, justified the two target models and
preserved the selected witness under the frozen contracts. The manual author
also weakened the witness requirement to equality after observation; the
assisted author retained the sufficient carrier right-unit law. Both pass the
prospective rubric. Retain validated dependency ledgers as optional provenance
notes for this fragment; this comparison establishes no incremental success
benefit or causal productivity gain from supplying one.

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
| Generic reversal | For arbitrary carrier, operation and reversing map, two uses of the binary reversal law yield the specified three-block equation. The anti-homomorphism law suffices; associativity is absent. List and Boolean models establish inhabited assumptions and derive concrete empty/nonempty cases. |
| Source replay and revision | The original body uses double reversal twice and no ambient append-empty evidence. The faithful generic replay retains involution; the revised proof omits that detour. A constant-empty reversing map satisfies the revised interface but fails involution at `[1]`. |
| Selected witness | For arbitrary observation result type, observed right-unit suffices to return the actual input in the required subtype. Full right-unit also replays the original proof. The list result equals the concrete source as subtype data; Boolean and empty/nonempty list cases use the generic construction. |
| Missing laws | Boolean left projection is associative but fails reversal and the requested equation. Nat addition with unit candidate 1 admits a witness at input 0 but cannot select 0. Neither rejection relies on an empty carrier. |
| Erasure | At list input `[1]`, `[1]` and `[2]` satisfy the same length predicate and have unequal first projections. Their `Nonempty` proofs are equal; no function from that erased proof can recover every original first projection. This does not deny choosing some inhabitant. |

Quantifier scopes, equation directions, operation order and subtype projections
were reviewed against the task's independent calculations. No interface field
assumes the three-block client theorem. Full right-unit is an acceptable
sufficient author interface for W; the reference's weaker observation law is
not an unannounced grading requirement. Proof equality uses Lean's ordinary
proof irrelevance, while data equality remains exact. The integrated entrypoint
includes both successful author submissions and the coordinator comparisons,
so the exhaustive audit covers their generated proof helpers as well.

## Preparation cost and validation boundary

The [preparation record](../../experiments/proof-requirement-authoring/preparation/record.md)
separates task design, private solutions, supplied assistance, compiler failures,
environment work and archived checks from author effort. First checks exposed
an implicit-argument mistake in a List lemma call; it was repaired before
freeze. No author saw that failed preparation artifact.

The exact preparation candidate
`72607d73206b4be824c688aab738bb4f4493bb66` passed the README candidate check
(992 modules and exhaustive axiom audit) and candidate-record verification.
The [coordinator archive](../../experiments/proof-requirement-authoring/coordinator/README.md)
contains those raw logs, the prospective checkpoint and initial dispatch record,
with copy provenance. This gate covers preparation, not later author submissions.
The implementation branch subsequently incorporated accepted #292 work from
`f36b0a61db0e89b8eb6d08a996bbb3adbdec11b3`; frozen task/support hashes remained
unchanged. Author submissions were archived before evaluation or packaging;
their integrated source files are byte-identical copies, as recorded in the
[integration map](../../experiments/proof-requirement-authoring/authors/integration.json).
No post-attempt author repair was needed.

The integrated development check passed all 998 modules and the exhaustive
axiom audit; its [raw record](../../experiments/proof-requirement-authoring/evaluation/integrated-check.json)
identifies the checked source hashes and command, with the full log beside it.
The audit's transitive axiom union was `propext`, `Classical.choice` and
`Quot.sound`. Exact-candidate check and record verification are supplied to the
independent reviewers after committing these unchanged formal artifacts.

## Closed author observations

The coordinator dispatched `/root/author_293_manual` and
`/root/author_293_assisted` with no conversation fork or model/effort overrides.
The recorded dispatch interval is bounded by 2026-11-04T20:40:54Z and
2026-11-04T20:41:31.577643+00:00. These are launch bounds, not author-reported
start/finish times. The separately archived final dispatch record records
closure, reported times and no interventions. Both records contain the exact
messages and their hashes; each omitted only the frozen prompt file's final
newline. Both authors report no prior task-design, private-solution, #286-proof
or other-arm exposure. Allowed-source use is recorded in their self-reports;
the full reading history is not independently reconstructed without a session
export. Frozen public hashes and handoff Git HEADs remained unchanged.

| Arm/task | Closed artifact | Contract assessment |
|---|---|---|
| Manual E, held out | [Attempt03](../../experiments/proof-requirement-authoring/authors/manual/Attempt03.lean), integrated as [ProofRequirementManual](../../Examples/ProofRequirementManual.lean) | Pass: named binary law, original/revised replay, both interpretations, applications and missing-law rejection |
| Manual W, calibration-derived | Same source | Pass: observed right-unit interface, original stronger replay, exact selections/source recovery and both negative controls |
| Assisted E, held out | [Attempt02](../../experiments/proof-requirement-authoring/authors/assisted/Attempt02.lean), integrated as [ProofRequirementAssisted](../../Examples/ProofRequirementAssisted.lean) | Pass: named binary law, original/revised replay, both interpretations, applications and missing-law rejection |
| Assisted W, calibration-derived | Same source | Pass: full right-unit interface, faithful source replay, exact selections/source recovery and both negative controls |

The [coordinator assessment](../../experiments/proof-requirement-authoring/evaluation/assessment.md)
maps every rubric obligation to actual declarations and records statement review.
It independently checks definitions, quantifiers, derivations and concrete cases;
author assertions of success were not treated as sufficient evidence. Both exact
submissions passed coordinator Lean replay. The original failed manual source
was replayed separately and reproduced its recorded diagnostic.

| Arm | Reported UTC start and finish on 2026-11-04 | Checked development snapshots | Assistance |
|---|---|---|---|
| Manual | 20:41:09 to 20:44:57 | Three: E passed; E/W failed elaboration; repaired E/W passed | Frozen common material only |
| Assisted | 20:41:18 to 20:44:56.226719 | Two: E passed; E/W passed | Prepared dependency ledger read before authoring |

These successive snapshots are not independent samples. Both authors stopped
before the 20-minute cap. The
[raw archives](../../experiments/proof-requirement-authoring/authors/README.md)
retain all checked sources, hashes, commands, exact diagnostics, UTC bounds and
exit codes, plus authored transcripts and outcomes. No raw agent-session export
was available. The exposed identity was Codex based on GPT-6; effective model
identifier, reasoning setting, serving revision, token use and price remain
unavailable. There were no recorded interventions beyond the frozen assistance.
An integration-cache copy ran on the same host during both trials. Host activity
was neither controlled nor measured, so elapsed time cannot establish comparative
productivity.

## Mathematical generality and causes

Both authors distinguished the unused ambient right-unit argument from the two
actual uses of involution. Their original replays retain the latter and their
changed proofs remove the cancelling detour. Both publish the same sufficient
binary reversal law. The assisted author reports using the ledger to track those
leaves; the manual author found the same distinction from the source.

For W, manual's `ObservedRightUnit` requires
`observe (m x e) = observe x`, while assisted's `RightUnit` requires `m x e = x`.
The former is weaker for a fixed observation. The post-trial
[coordinator comparison](../../Examples/ProofRequirementComparison.lean) proves
that the carrier law supplies the observed law and that both constructions then
return equal subtype data. It also checks an actual separating model: Nat
addition, unit candidate 1 and constant observation into `Unit`. The observed
law holds and manual's construction selects 0; the carrier law would assert
`1=0` and fails. This comparison was written after both attempts closed and is
excluded from author effort. Assisted's sufficient interface remains a passing
answer; the evidence does not show that assistance caused its stronger choice.

The author-facing work remained explicit law naming, source-leaf interpretation,
Boolean case proofs, two target wrappers and subtype projection/equality proofs.
Manual used a Prop structure for E and named predicates for W; assisted used
named predicates for both. Neither author had to construct an AST, variable
indices or representation casts. The ledger did not perform those publication
and model-building decisions.

The only failed author check was manual's `Trans Eq Eq` synthesis error while
chaining subtype equalities. Replacing that proof with `Subtype.ext` and the
generic projection theorem preserved its statement. Initial manual warnings
concerned structure syntax and proposition declaration style. These are host
encoding and author repair observations, not failed mathematical requirements.
No documentation blocker or missing support was reported. Successful small
examples do not establish usability of the documentation for human authors or
larger arguments.

## Decision and remaining scope

**Retain** a supplied, validated ledger as an optional provenance aid for this
equational/subtype fragment. Its use here was compatible with correct replay,
dependency classification and witness preservation. Manual success on the same
contracts means this sample demonstrates no additional completion benefit.
The prepared ledger contains mathematical work from task design and reference
proofs; counting that work as extractor productivity or author savings would
misstate the experiment.

**Investigate** observation-sensitive law discovery under #290/#235 if a concrete
author need warrants another trial. A later ledger revision should distinguish
the original used leaf from candidate weaker sufficient requirements. Freeze
that revision, rerun affected tasks and add a fresh held-out task; preserve this
baseline. **Defer** a general Lean importer or extractor investment on this
evidence. No support prerequisite exceeded the bounded fixtures, so this trial
creates no prerequisite implementation task. #108 remains untouched.

The sample has one author per route, fixed E-then-W order and a calibration-derived
second task. It supports neither causal savings nor general model capability,
human usability or a globally weakest theory. Independent Standards/Spec review
and final exact-candidate acceptance are completion gates owned by the existing
implementation workflow; their records accompany the reviewed candidate.
