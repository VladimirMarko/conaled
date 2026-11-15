# Standards review, round 1 — provisional source analysis

Date: 2026-11-14. Reviewer: `/root/integration_review/standards`.

**Outcome: Blocked.** Required terminal validation of this exact candidate has
not yet been presented to this reviewer. Source analysis is complete for this
round and identifies **one unresolved low-severity documentation finding**,
INT-ST-001. No substantive mathematical or architectural defect was established.
This report is not approval and does not infer a pass from a running check.

## Immutable review scope

- Repository: `/workspace/scratch/e1eab3b6b18e/integration-20261113/master`.
- Original full-spec base and merge base:
  `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`.
- Candidate: `337c29ff2e2b969e701a9deb84840d6b148dd175`.
- Candidate tree: `70a8cab787ac1f5fb2b9bdda46ca4f4bb4e11f23`.
- Comparison: `git diff BASE...CANDIDATE`. BASE is an ancestor, so this is also
  the endpoint tree difference. The retained commit list has 310 entries.
- Complete scope: 356 changed paths, including 326 Lean files; 67,134 added
  lines and 66 deletions. The supplied integration manifest declares all changed
  paths, has 465 total paths, and contains no projections or exclusions.
- Receipts: `intake/integration-{baseline,candidate,scope}.json`. The original
  full-spec base remains fixed across future corrections.
- Full requirements: `checkpoint/conaled-textbooks/books/common/REQUIREMENTS.md`,
  version `2026-11-13-user-clarifications`, SHA-256
  `9358100642aa0a6eef7793459666d39f14ce6edd4437520aff656366df9b97df`.

The review used immutable `git show`/Git-object comparisons and the stable
candidate checkout. It made no source, index, branch, dependency, setup or
compiler changes. Root remains the sole full-check owner. This report and its
JSON companion are the only reviewer-created files.

## Governing standards and explicit user exceptions

The assessment applies the candidate's AGENTS and linked code-review skill,
review-loop procedure, example-driven-development/statement-review guidance,
README development and validation rules, architectural-quality and domain
guidance, GLOSSARY, and applicable ADRs 0001, 0002 and 0010. There is no root
CODING_STANDARDS.md or CONTRIBUTING.md. Review heuristics are prompts for
investigation, not automatic refactoring requirements.

The user prioritizes library coherence, then preservation of useful mathematics.
Checkpoint-local issue/spec tracking is authorized, and Nix is optional while
the exact pinned compiler/dependency inputs remain mandatory. Historical runtime
holds, chapter ordering and fresh-on-every-check rules do not override those
instructions or current README triggers. No GitHub write is authorized.

The complete three-head integration and preserved donor dispositions were in
scope; this was not a review limited to the three new clients. Historical book
acceptance is not current candidate acceptance. Useful unfinished families may
remain intact with explicit ownership and exact recovery pointers; that is
different from discarding their mathematics or claiming them accepted.

## Complete finding

### INT-ST-001 — duplicated source identifier in the merged provenance catalog

**Severity:** Low. **Status:** Open on candidate 337c29ff.

**Location:** `docs/SOURCES.md:90` and `docs/SOURCES.md:140`; related FDSA entry
at line 154 and `docs/research/pfds-union-coverage.md:5`.

Both Purely Functional Data Structures and Verified Functional Algorithms are
headed `S9`. FDSA is `S10`. The PFDS union coverage explicitly cites `[S9]`.
The merge therefore gives one source identifier two meanings in the central
provenance catalog. The full heading anchors remain distinct, but the short
source label is ambiguous for readers and subsequent source correspondence.

**Governing rule:** ADR 0001 requires references and pinned source revisions to
document provenance; the integration's documented source correspondence should
identify the received books unambiguously. This is a documentation correctness
finding, not a heuristic request for a new architecture.

**Remedy:** Give the merged entries distinct stable IDs and update affected
labels/anchors. Keeping PFDS as S9 and assigning VFA S10/FDSA S11 preserves the
existing explicit PFDS citation. Inspect the exact corrected candidate before
closing this ID. No mathematical statement needs to change.

The parent was notified promptly. No correction was made by this reviewer.

## Scope accounting and justified reuse of source analysis

An independent read-only blob comparison enumerated every Lean path in the
fixed-base diff and compared `git rev-parse CANDIDATE:path` with the same path
in each of the three incoming candidates and the selected additional FDSA
potential donor. **321 of 326 changed Lean paths are byte-identical to at least
one of those source snapshots.** The five exceptions are:

1. `Applications/Resources/Growth.lean`;
2. `Applications/Resources/Potential.lean`;
3. `Examples/TextbookSequences.lean`;
4. `Examples/TextbookSorting.lean`;
5. `SquareApplications.lean`.

Source candidates were VFA `eae9e110adc7ba1cc28386448a6deef23e406c13`, FDSA
`e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe`, PFDS
`3cf3de4fbc24c1a144353ae64b13b72f5ead54a5`, and extra FDSA donor
`12cb14fc98b8617b3b625620da8e60936daba340`.

The 326 Lean paths span Arithmetic (1), Probability (3), Resources (65), Search
(20), Selection (11), Sequences (8), Sorting (11), Suspensions (53), Trees (4),
Examples (149), and the public entrypoint (1). This identity accounting covers
the entire Lean diff; it is not a claim that every inherited proof line was
manually reread. Historical static assessments were used where source identity
and relevant surrounding definitions were checked. Their approval and compiler
outcomes were not transplanted to this candidate.

The shared context comparison against old common base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` found the inspected Relational,
SquareKit.Combinators and OrderedSummary owners unchanged. Progress.Evaluation
differs only by removal of an import; Resources.Workload adds a theorem without
changing its executor; Measured's change is the inspected universe
generalization of `erasureSquare`. This supports retained semantic analysis of
the incoming clients without treating a successful old build as current proof
validation.

The merge receipt's seven PFDS and nineteen VFA pinned-master resolutions are
import/blank-line changes relative to the common source base, with the resolved
blobs equal to pinned master. Growth retains both theorem families. Both parents'
public import sets remain. These are preservation facts, not sufficient approval
evidence by themselves.

## Independent source and statement assessment

### Shared potential accounting and receiving owners

The complete Potential owner, actual Workload executor, signed potential owner,
MappedPotentialAccounting, PotentialTransport and SignedPotential clients were
inspected. The implementation handoff's intended propositions and cases were
checked against actual definitions and theorem types.

`budget` follows the actual successive states with a separate charge carrier.
Mapped invariant-aware telescoping retains the initial invariant, successor
closure, local law, both boundary potentials and the actual observation map.
The source addition is not reassociated. Exact laws require associative target
addition but not commutativity, cancellation or order. Inequality laws state
both monotonicity assumptions. PFDS's same-carrier exact/inequality APIs are
specializations via the identity additive homomorphism; existing Nat APIs and
the weaker actual-final-state nonnegativity condition remain available.
Signed subtraction has the explicit additive commutative group assumptions it
needs. Similar induction shapes here establish materially different contracts
and do not constitute a duplication defect.

The clients retain arbitrary initial binary-counter states, mapped real
observations, negative state-dependent charges, fractional valid-state charges,
the invalid state-two counterexample, negative-final-potential counterexample,
and ordered free-monoid observations. The code does not infer operational
runtime or reusable persistent credit from these accounting equalities.

Other substantive modified receiving owners were inspected through their full
diffs and relevant surrounding definitions: Growth's ceiling-log bridge coexists
with current master's asymptotic carrier bridges; Measured.erasureSquare's
universe generalization retains ordinary old clients; Selection.ThreeWay now
uses the shared partition owner while preserving public semantics; Sorting.Merge
adds input-local sortedness/sublist facts without imposing unnecessary global
comparator laws. FIFOContracts' specialization remains a Nat observation.

### Sorting connection

The full TextbookSorting client, FirstPair owner and ComparisonPermutations
client were inspected alongside sorting uniqueness and the existing
synchronization construction. An arbitrary Boolean first-pair operation has a
permutation contract; it is not claimed to sort the entire list. The generic
complete-sorter equality adds antisymmetry on actual values, and the concrete
two implementations use the existing common `sortOn id` specification.
`jointSquare` uses the existing agreement representation and synchronization
theorem, with a real same-input agreement witness in `paired_outputs`.

The duplicate example consumes the universal public relationship. The
noninjective-key example correctly shows that first-pair preprocessing may
change stable ordering of distinct equal-key records. Value equality is not
advertised as equal cost or equal sharing. No parallel textbook interface or
replacement sorting kernel is introduced.

### Sequence connection

The complete TextbookSequences and AbstractStack interfaces and the relevant
DifferenceListCosts materialization definitions/proofs were inspected. The
generic result relates actual successful abstract-stack append to the full
materialized list before taking any summary. It retains explicit representation
laws and sufficient left-length fuel, arbitrary suffixes, order and repeated
occurrences. It does not force a total decoder on invalid representations.

The concrete summary theorem quantifies over an arbitrary monoid; the optional
head client reuses the existing relational composition. Distinct tariffs remain
explicit: `4*n+1` stack primitive calls and `4*n+2` closure events. Repeated
tagged elements, ordered words, the uninhabited Empty payload, empty success and
insufficient-fuel failure are meaningful connected cases. Lossy summary equality
is never used to infer sequence equality.

### Inherited containers, physical identity and persistent accounting

The PFDS abstract set, abstract stack, ordered-map interface/implementation and
ordered-tree interface were examined. Operations, laws, validity and observations
have separate roles. Presence uses Option, including the distinction between a
missing key and an existing `none` payload; no unnecessary order or equality on
payloads is imposed. Tree lookup and independent whole-tree observation meet
through the ordered invariant. Existing fold and relational constructions serve
ordinary clients.

SharedList observations and the persistent Realization/Observation owners retain
relations to actual heaps, partial failure, physical identity, arbitrary initial
seen support, and occurrence-sensitive unshared charges. Finite support, list
multiplicity and exact node enumeration remain separate. Abstract debit pricing
does not by itself claim the cost of arbitrary operational forcing. The inherited
source-boundary and forward-contract records remain open at their actual scope.

### Inherited suspension semantics and cache/body counts

The actual Observation executor, Pure.NoReentry, Pure.CacheCounts,
BodyAccounting, BodyRealization and connected body-count source cases were
inspected, with the historical nine-scope statement analysis retained as
supporting evidence for unchanged modules.

Observation runs the existing resource executor on actual transitions, retaining
ordered events and residual configurations. Its completion theorem matches the
existing evaluator's actual count; absorbing finished suffixes add no events.
Pure finite-execution correspondence derives freshness/nonreentry rather than
assuming the conclusion. Successful cache writes are distinct from body-entry
attempts. Body-at-most-once additionally requires the explicit no-memoize-unwind
condition; the finite pure external-handler counterexample has two attempts and
zero writes and disproves removing that premise. Distinct allocated addresses
are not equated by identical code or meanings. Replacing body occurrences by
support cardinality is justified only by the stated nonrepetition result.

The retained effectful cached-reference type/result counterexample is an explicit
source boundary. This integration makes no blanket type preservation,
blackholing or unconditional once-only evaluation claim.

### Inherited FDSA probability, selection, recurrences and costs

Historical FDSA Chapter 1/2/3 Standards evidence, coverage/statement records and
source correspondence were consulted with exact incoming identities. Current
context inspection included the occurrence-pivot RandomSelection step, its
actual finite run, expectation interfaces, refined-rank drift and tail theorem.
The step measures reached source operations, and the finite PMF follows the one
strict child actually selected. Support correctness covers duplicates and the
explicit invalid-rank extension. Abstract occurrence sampling is not presented
as a random-bit implementation.

Expectations are marginals of that same run. Scalar finiteness/integrability is
proved before real expectations are used, without a measurable/finite payload
assumption. Stable occurrence ranks preserve duplicate multiplicity; larger
partition ranks bound the selected child rather than replace it with another
process. Successive sizes are not assumed independent. The tail retains positive
length and its empty countercase. Same-execution source-cost transport retains
its coefficient and invalid-empty offset. Historical median/rounding/adaptive
query, worst-path and tree-shape obligations remain at their source scopes;
nothing in the new clients silently replaces those stronger statements.

## Documentation, public coverage and unfinished mathematics

README's added workstream, the new textbook integration correspondence and
potential correspondence, source catalog changes, public-entrypoint diff, donor
dispositions and current local requirements/process records were inspected.
The entrypoint additions preserve existing imports and expose the connected
clients and incoming module families. Actual complete coverage and exhaustive
axiom validation remain the checker gate; source inspection does not substitute
for them.

The integration correspondence correctly separates source provenance, semantic
connections, validation and whole-book acceptance. INT-020 retains extra FDSA
tree/ADT/logarithm/probability/Chapter 4 work; INT-021 retains five VFA standalone
draft families. The preserved refs and capability dispositions provide exact
owners and continuation points. No redundant active framework is required merely
to keep a historical filename. PFDS's normalized historical output is not
activated as a second copy. Source-page coverage, paper obligations and forward
cost contracts are not closed by import success or by these three connections.

The supplied patch-reconstruction evidence reports that the 3,512,080-byte
binary-capable unified patch reconstructs exact tree 70a8cab7 from the fixed base
using a private index. It does not replace this Standards assessment.

Root also reported an inherited extra blank line at EOF in
`Applications/Search/AbstractSet.lean:90`. It is a cosmetic observation without
an identified mathematical or architectural consequence, not an additional
Standards defect. Root owns any cleanup and the resulting new candidate capture.

## Inherited findings and required evidence

The complete PFDS 39-ID canonical register and eight aliases remain in
`books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md`,
section 5. It was read for this assessment. The 23 repair/static-development
closures, two explicit boundaries and 14 open validation IDs retain their
historical meaning. This report neither erases them nor retroactively marks old
runs successful.

The Standards-owned/shared open PFDS validation IDs are IMPORT-VAL-004,
CH02-PRE-005, SUSP-STD-VAL-001, PURE-STD-VAL-001, COUNT-STD-VAL-001,
PERSIST-ACC-STD-VAL-001, BODY-COUNT-STD-VAL-001 and SIGNED-POT-STD-VAL-001. Their
paired Spec IDs remain independently owned. SUSP-STAT-001 and PREP-10019-02
remain boundaries, not defects to erase. VFA ST-002 and the paired Spec
SP-VAL-001 remain historically unresolved; ST-006's old source repair is not
reopened without contrary evidence. FDSA XT03-CP01/XT03-DOC01 and Chapter 4's
original base, 76 obligations and 11 exercises remain in deferred INT-020 scope.

The current source analysis supports retaining the static repairs and explicit
boundaries. A successful new full check can satisfy current integrated validation
obligations only for its actual candidate and scope; it does not change the old
incident record or establish whole-book completion. Any resulting cross-reference
or closure must preserve each original ID and distinguish current evidence from
historical outcomes.

Durability prerequisite 003 is supplied by `intake/003-delivery.json`, with
completed/durable_uploaded both true and archive SHA-256
`d25cd846e815c3185796cced6a14499be71343f0490a80a8d08372374794d49e`.
Root reported full `./check.sh --candidate HEAD` running for 337c29ff after the
source/coverage/version preflight. No terminal full-validation receipt was
presented to this reviewer. Focused development success and running-log prefixes
do not meet the full gate.

Before final approval: resolve INT-ST-001; present the corrected immutable
candidate and matching applicable full build/exhaustive audit evidence; reassess
the correction while retaining this full original scope; obtain both independent
axes on that same candidate; and perform the required final candidate verification
and snapshot comparison. Durable delivery remains root's prerequisite for
handoff/session completion. No further compiler or setup work is delegated to
this reviewer.

**Final round-1 accounting:** base 9175737c2b14ef738cfb6c2cdc68d885c0805ddd;
candidate 337c29ff2e2b969e701a9deb84840d6b148dd175; new source findings 1,
worst source severity Low; validation pending; Standards outcome **Blocked**.
