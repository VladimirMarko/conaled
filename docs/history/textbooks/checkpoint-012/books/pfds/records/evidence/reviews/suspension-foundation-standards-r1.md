# Local10014 suspension foundation — independent Standards review, round1

## Outcome

**Blocked. Static review is complete, with zero code or prose findings.** The
reviewed candidate has no successful full exact-candidate build, exhaustive
audit, matching verification record, or immediate final verification. Those
mandatory acceptance gates remain open as **SUSP-STD-VAL-001** below. Focused
development results do not close that blocker.

This is the first independent Standards assessment in the existing
`reviews/suspension-foundation.md` loop. It is not an implementation report,
Spec assessment, chapter acceptance, or reuse of an earlier approval. The
reviewer performed read-only source/evidence inspection and wrote only this
report. No compiler, Lake, check command, dependency mutation, Git mutation, or
GitHub write was performed.

## Immutable scope and requirements

| Item | Reviewed identity |
|---|---|
| Candidate | `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` |
| Frozen checkout | `/workspace/scratch/ca9a61d0bf30/validation-suspensions-r3` |
| Ticket base | `99a29dcd02eb529fbefbb675e244a8c47b78cdef` |
| Complete integration base | `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4` |
| Ticket diff | `git diff 99a29dcd02eb529fbefbb675e244a8c47b78cdef...a3feaff319ad5fad912fb8bdc113f33fea4e2a60` |
| Complete integration diff | `git diff 69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4...a3feaff319ad5fad912fb8bdc113f33fea4e2a60` |
| Scope | 38 ticket files / 8 commits; 42 integration files / 10 commits; no exclusions |
| Manifest | `validation/suspension-candidate-r3.json` |

I independently checked HEAD, clean Git status, both merge bases, the exact
changed-file sets, and every manifest file hash. Both named bases are ancestors
and both diffs are nonempty. All 38 ticket and 42 integration hashes match the
frozen checkout. I read the entire changed suspension source and client scope,
the public-entrypoint additions, the research document, and the five existing
file import changes. The complete integration commit list is:

1. `804eb96598bad5eb5d4734b0f464dc1445612aa7`
2. `1639dc8b125e2779d9c2a4513c729aecf934fabe`
3. `fe7447099052ab68eac90dfeece891b90ad6a3fb`
4. `76456b1738c546017d162c4216a5731d0c98f22a`
5. `fd3605e4efbd6a388b3afc06814088ec567d3398`
6. `b422800fb5b6dc1253823057c0ea71644274d77c`
7. `c8ea1f8267b701f9797a52b1c8d3f9156422ccf6`
8. `c372c470008cdda3043040683451662f61131f81`
9. `99a29dcd02eb529fbefbb675e244a8c47b78cdef`
10. `a3feaff319ad5fad912fb8bdc113f33fea4e2a60`

Requirements read in full were `requirements/REQUEST.md`,
`requirements/REQUEST-union-v2.md`, and
`requirements/suspension-foundation.md` version1, whose recorded SHA256 is
`56828fa549b0f96b76db9c2451b82106ea12cf4c6e15bd7cd0fc5ecdf3a98f3e`.
The dispatch and existing coordinator record were also read. The whole-user
request, local-only tracking, chapter order, and checkpoint rules remain
binding. Local10019 is absent from this candidate and is not reviewed or
accepted here. Neither foundation acceptance nor this report would accept
Chapter4 or the whole AppendixA union.

## Applicable standards and primary evidence

The assessment applies candidate `AGENTS.md`,
`docs/agents/architectural-quality.md`, `docs/agents/domain.md`, `GLOSSARY.md`,
the ADR index and ADR0001/0006/0010, `docs/language-direction.md`, README build
and audit requirements, the code-review workflow/heuristics, and the full
example-driven-development statement guidance and worked example. The
coordinator retains the existing review loop and reviewer identities. The
source-specific repeated case analyses were evaluated as Lean induction
proofs, not treated as smell violations merely because their cases resemble
one another.

Primary evidence was inspected directly, rather than treating the implementation
reports as a proof of conformance. The exact source files remain outside the
repository and report payload. Their hashes were independently checked:

| Source | SHA256 | Relevant direct inspection |
|---|---|---|
| Attached Cambridge book | `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41` | Printed pp31–33: creation, demand, scope of dollar, derived force, strict lazy-function sugar and force/delay observation; p33 render checked to resolve code tokens |
| Linked1996 thesis | `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072` | Printed pp7–12 and AppendixA pp131–135; p133 rule render checked, including the write before the inner pattern and modified Rule158 |
| Official1990 Definition | `2ad9e869db05f5a4316bc60b7170fb00789410436651c1a8f425a88098e8e9d1` | Reconstruction PDF34–37,69–70,74: equality/imperative attributes, scheme instantiation, exact nonexpansiveness/Clos, finite Rec, state/exception conventions, simultaneous bindings and generative exceptions |

The union identities, inherited-core audit, complete suspension inventory,
static-development report, import-change record, and force-observation
development report were used as provenance and navigation. The distinction
between the thesis's1990 base and the book's1997 citation is preserved in the
candidate. No manuscript was added to the diff or this report.

## Architecture and statement assessment

The added domain has an appropriate boundary. `Store` separates operations
from validity and footprint laws. It reuses `Durability.Heap`, `put`, and
`Extends`; `Extends` is used for fresh allocation/creation, not for memoization
or SRec. I inspected those unchanged storage definitions. `Machine.step`
instantiates the existing `Progress.Machine`; finite results, uniqueness,
search soundness and finite completeness consume the existing `Evaluates`
interface. The unchanged Progress definitions were read. `Observation` uses
`Resources.Measured`, `run`, `reweight_run`, indexed membership observations,
and `Relational.compose`; the relevant unchanged Measured, Workload,
Optimization.Relations, and SquareKit.Relations definitions were inspected.
There is no second generic evaluation or resource framework.

The new transition is source-specific: its continuation stack exposes demand,
body steps, memoization, inner matching, and exception unwinding. Arbitrary
body evaluation is not hidden in one successful-force transition. Primitive
functions, map updates, and recursive-environment construction still have
their stated abstract-transition cost; the documentation explicitly requires
later algorithmic clients to justify host or primitive costs separately.

The following covers every changed formal family, including helper claims,
its assumptions, and its retained connected clients. Counts mean transitions
of the explicit machine, including final delivery.

| Modules / claims | Statement and client assessment |
|---|---|
| `Syntax`, `Store`, `AddressRange` | Finite closure triples and one Rec unrolling retain the source meaning. Runtime lookup uses the first effective binding. The target-range theorem follows effective lookup, including shadowed entries. Boundedness controls occupied addresses, not addresses nested in captures. Fresh allocation is a witness of the independent fresh-choice relation, not an identification of all source choices. Replacement/domain laws keep occupancy hypotheses. `SuspensionStore` exercises original capture, distinct creation, shared reference space, SRec footprint, a self-address capture, and later successful overwrite. `SuspensionRenaming` distinguishes shadowed addresses from effective targets. |
| `Grammar`, `Names`, `Namespace` | Dollar is excluded as the exact reserved identifier, with the full-production precedence and grouped alternatives represented separately. Opaque inherited phrase categories and source identifier classification are explicit boundaries. Conservative name support includes exception-pattern lookups and binders; it is not misrepresented as exact free-variable support. The even/odd adapter proves lookup/update separation and does not claim to translate unencoded closure syntax. Grammar clients distinguish the two expression and constructor-pattern parses; namespace clients use equal underlying indices without collisions. |
| `Static` | Attributed variables, simultaneous instantiation, independent equality/imperative restrictions, and1990 Clos are explicit. The source's expansive applicative generalization is retained. Generalization sees effective finite-map bindings and ambient variables. Recursive typing fixes a monomorphic group environment, distinct binders and permitted RHS shapes. Weakening and lazy typing expose the extra ambient-type support premise; the client showing an unused unscoped parameter changes Clos explains why term freshness alone is insufficient. Open signature scoping is separate and concrete signatures discharge it. The fragment and omitted elaboration features are documented. |
| `Rules`, `Machine`, `Correspondence` | Source forcing/reference/ordered-clause schemata are independent definitions parameterized by inherited judgments. Their instantiation with finite machine runs is stated explicitly, and the finite iff proofs use actual continuation decomposition. Normal values, raised packets, matched environments, mismatch and stuck are separate. Cached forcing still matches the inner pattern; uncached forcing uses captured body environment and caller matching environment. The machine and source clients preserve changed states through failed and exceptional patterns. The actual appendix three-clause failure and fourth-clause result are retained. |
| `Continuation`, `Return` | Appended-tail proofs distinguish nonterminal steps, empty-stack delivery boundaries and uncatchable stuck faults. The count subtracts exactly the isolated final-delivery step. The converse requires a finite non-stuck plugged answer and does not assume body termination or type safety. Return-mode preservation concerns control protocols, permits raised/stuck outcomes and cannot be mistaken for value-type preservation. Concrete mismatch, Match/Bind, cache continuation and expression-result clients exercise these distinctions. |
| `Derived` | Force laws start the body in the allocated state, retain reached normal/raised state, and prove both directions with overhead12/10. Lazy formation keeps strict argument execution and stores its ordered match, with overhead9/4. Theorems neither erase private memory nor equate arbitrary closure environments. `SuspensionDerived` connects literal/reference/exception runs and all four converse families. Its composed case forms in13 steps, performs an intervening assignment in6, then forces in39; it verifies the delayed reference read, fallback clause and both cache writes. |
| `Recursive` | `Permitted` is RHS shape only; distinct binders, identifier classification and nonempty matches remain separate. Creation uses one outer environment, proves its target-thunk applicability premise under boundedness, and connects the creation fold to actual three-step-per-binding execution. Closing preserves source domain/names/outside cells and extends selected thunk captures. The exact creation/closing prefix is `3 * length + 2`; finite whole/body correspondence retains the entire answer and does not assume termination. Clients use a function/suspension group, unrelated old thunk/reference, typed delayed RHS, cyclic body returned without forcing, recovered body execution and raw rejection with retained allocation. |
| `Invariant`, `Prefix` | Finite memory requires pending memoization-frame addresses below the current frontier as well as bounded memory. The forged-frame client demonstrates the missing premise if only memory boundedness were used. The cyclic prefix permits two frames for the same address; all-budget boundedness is not presented as divergence. Prefix completion iff retains actual steps bounded by budget. An unfinished result retains the full reached configuration. |
| `Renaming`, `Relocation`, `ForceObservation` | Renaming descends through records, constructors, closure captures and finite recursive environments. Memory relatedness retains represented lookup absence as well as values, exception names and frontier; private cells are deliberately omitted. Injectivity and successor/frontier conditions justify allocation, and primitive equivariance is a distinct operation law. Both finite execution directions and individual event transport are proved. Force/direct normal and raised comparison additionally requires bounded initial memory, fixed existing cells and a fixed explicit capture; these are initial-data premises, not assumed conclusions about body runs. Forward/reflected clients establish old-reference7/new-reference9 at relocated addresses and13/25 or13/23 counts. The3/10-step dangling-capture faults show why bounded empty memory alone is insufficient. No force/direct fault, unknown-budget, divergence or equal ordered-trace result is inferred. |
| `Observation` | Ordered events compose through the free additive monoid and existing workload executor. Delivered answers absorb unused budget without events. Completion equals existing search with the actual event/transition count, and reweighting is a supplied homomorphism. Indexed squares retain input and count while explicitly selecting result/effect observations. The delay client checks budgets0,1,2,9, retained allocated unknown memory, no body event, and the unchanged two-event completed result. |

All15 suspension client files were reviewed. Their public-result connections
are substantive: stored-footprint cases use Store laws; source clients use
correspondence and determinism; concrete executions enter `Evaluates` through
`search_sound` or explicit transitions; relocation/force clients consume the
transport laws; recursive and invariant clients discharge applicability and
boundedness premises. Closed reductions are used for independently specified
outcomes, not equations of a definition with itself. Existing cases also
cover helper results without a synthetic one-case-per-lemma quota.

### Preserved source-sensitive boundaries

**SUSP-STAT-001 remains a checked counterexample boundary, not a defect to hide
or a general type-safety result.** `cachedReference_boolean` types the exact
public `Examples.SuspensionMachine.cachedReference` term. The runtime theorem
executes that same term, and `cached_reference_type_mismatch` joins Boolean
typing with a finite integer0 return and unequal atom types. The concrete
signature is closed/scoped. The claim is confined to the represented1990 plus
AppendixA fragment; it does not assert an unqualified result about a complete
SML implementation. The primary1990 Clos/nonexpansiveness text supports the
deliberate static boundary.

The reentrant overwrite client actually records two body entries and two
cache writes, ending in8. The outer-exception client retains the inner7 cache,
and its handled continuation hits that cache. Repeated exceptional bodies
remain uncached, while successful outer bodies can remain cached after an
exceptional inner pattern. No inspected claim silently adds blackholing,
rollback, exception caching, a backward-address DAG invariant, or unconditional
at-most-once evaluation. The pure self-forcing claim remains assigned to10019
outside this candidate.

## Existing-file changes and public integration

`Applications/Progress/Evaluation.lean` changes only its aggregate tactic
import to `Mathlib.Tactic.Common`; its definitions, theorem statements and
proofs are unchanged. The candidate hash matches
`research/suspension-progress-import.json`. This narrows an import dependency;
it does not authorize a weaker proof policy, changed cost model, or higher
proof budgets. Static inspection found no new mismatch in the Progress
interface, but its full affected-consumer check remains part of the blocker.

The four separately incorporated consumer changes add direct imports for the
existing uses of `monotone_nat_of_le_succ` in FRP Demand, finite-set lattice
operations in FRP Finite, the real Archimedean instance used by `exists_nat_gt`
in Examples.FRP, and `Nat.size_pow` in Examples.IndefiniteService. I inspected
their complete diffs and the relevant consumers. No statements or proof bodies
change. This does not reuse the separate10018 prerequisite review as approval
of the complete10014 integration.

The17 public-entrypoint imports bring all20 suspension domain modules and
all15 client modules into the public closure through their dependencies.
The exhaustive public-coverage and proof-audit checks still have to run. Static
inspection found no admission, new axiom, native proof shortcut, disabled
linter or raised proof budget in this change. It is not a substitute for the
mandatory audit.

## Focused evidence inspected and its limitations

I inspected the terminal records/log endings and relevant recorded source
hashes, rather than treating the list of reported successes as validation of
the complete candidate.

| Focused record | What it establishes as development evidence |
|---|---|
| Static r8 | Exit0,775 jobs, tracked inputs unchanged; the recorded Static/Names/Grammar/static and grammar clients/machine inputs match this candidate. |
| Correspondence r3 | Exit0,747 jobs, start/end unchanged; all9 recorded input hashes match this candidate. |
| Derived r8 and r10 | r8's log has terminal success for the core and earlier clients. The durable r10 record is `validation/checkpoint016-progress/suspension-derived-r10.json`, with exit0 and start/end unchanged; all8 recorded inputs match this candidate and include the composed later-force client. |
| Invariant r3 | Exit0,745 jobs; all10 recorded final input hashes match this candidate. |
| Recursive r3 | Exit0,778 jobs, unchanged during that run. Its Recursive source hash is `9e711dbb5e8b6f07e54997ee1c798bcccca970a86bb099875b6ac9aed9dcb258`, whereas the candidate's clarified source is `525f56b2104c5d89807682bcea36bc444a57e0f959cee633e44d05e93556960f`. The other recorded hashes match. The later documentation boundary is reviewed here; the old pass is not exact-current-file validation. |
| Renaming r3 | Exit0,745 jobs; all7 recorded input hashes match this candidate. |
| Relocation r6 | Exit1 overall: core compiled, example failed. It is not a passed complete check. |
| ForceObservation r1 | Exit1 overall: corrected Relocation example and ForceObservation core compiled, force-observation example failed. It is not a passed complete check. |
| ForceObservation r2 | Exit0,751 jobs; queue/start/end unchanged and all16 recorded inputs match this candidate. This is the terminal successful connected chain for the corrected clients. |

Historical failed and interrupted rounds remain historical. A subset hash
match and successful focused target do not establish the dependency-wide
candidate gate, source-policy/coverage check, exhaustive axiom audit, or clean
exact-candidate approval record.

## Findings and remaining gate

**Code/prose findings: 0. Worst static issue: none identified.** No heuristic
rewrite is requested without a concrete defect or caller consequence.

### SUSP-STD-VAL-001 — full exact-candidate validation unavailable

- **Classification/severity:** acceptance-blocking evidence gap; not a static
  code finding.
- **Location:** frozen checkout `validation-suspensions-r3` at
  `a3feaff319ad5fad912fb8bdc113f33fea4e2a60`,
  `validation/suspension-candidate-r3.json`, and absent
  `validation-suspensions-r3/.lake/verification.json`.
- **Rule:** README Build and audit, ADR0010, code-review validation requirements,
  and foundation requirement Architecture/validation/delivery require full
  exact-candidate validation, exhaustive audit, matching success record, and
  immediate final verification. Missing mandatory evidence cannot pass.
- **Evidence:** the dispatch/manifest explicitly mark the gate not started;
  the candidate has no verification record. Available terminal successes are
  focused development checks on the implementation worktree. Current recursive
  documentation and all affected consumers still need the full candidate gate.
- **Consequence:** no acceptance claim is justified for this integration,
  regardless of zero static findings. Predecessor or upstream approvals and
  subset compilation cannot cover this candidate automatically.
- **Required resolution:** root supplies a successful unchanged pinned
  `./check.sh --candidate HEAD` on this frozen exact candidate, the matching
  `.lake/verification.json` and complete build/audit/source-policy/coverage
  evidence; then the same review loop reassesses that evidence and records the
  immediate `./check.sh --verify-candidate HEAD` before acceptance. Corrections
  must preserve findings and receive exact new-candidate assessment. Upstream
  prerequisite and Chapter2 acceptance remain separately tracked.

Final identity: ticket base `99a29dcd02eb529fbefbb675e244a8c47b78cdef`;
complete integration base `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`;
candidate `a3feaff319ad5fad912fb8bdc113f33fea4e2a60`.
**Standards outcome: Blocked; full static coverage complete; zero static
findings; one acceptance-blocking validation gap.**
