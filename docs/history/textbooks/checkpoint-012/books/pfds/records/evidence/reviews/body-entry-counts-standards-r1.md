# Local10022 — independent Standards review, round1

Reviewer: `/root/body_entry_counts_review/standards`, 2026-11-03 UTC.
This is the Standards axis of the existing body-entry accounting review loop.
The reviewer did not author the implementation, inspect the independent Spec
report, change source/Git/cache state, or run any compiler, gate or optional test.

## Outcome and exact scope

**Outcome: Blocked.** Complete static review found **zero source-level Standards
findings**. One required-validation blocker remains:
**BODY-COUNT-STD-VAL-001, High, unresolved**. Focused compilation is successful;
the exact candidate's own full acceptance check, exhaustive audit, matching
verification record and immediate final verification are still missing.
This report is not approval or formal acceptance.

| Item | Reviewed identity |
| --- | --- |
| Candidate | `5e048f781aa04be9ce993f1e7455bdc82df22bff` |
| Bounded base | `577be121e074ddb5de6727a7481c115cb61b3b27` |
| Original integration base | `577be121e074ddb5de6727a7481c115cb61b3b27` |
| Observed merge base | `577be121e074ddb5de6727a7481c115cb61b3b27` |
| Immutable candidate ref | `pfds/body-counts-review-r1` |
| Isolated checkout inspected | `/workspace/scratch/ca9a61d0bf30/body-counts` |
| Complete difference | 11 files, 1424 insertions, 4 commits, no exclusions |
| Requirements | `requirements/body-entry-counts.md`, version1 |
| Requirements SHA256 | `1483d8bfc4470c4aa700c809209b3083db89fa713def40821e1968d9e3ce2a58` |

Commands defining scope:

```
git diff 577be121e074ddb5de6727a7481c115cb61b3b27...5e048f781aa04be9ce993f1e7455bdc82df22bff
git log 577be121e074ddb5de6727a7481c115cb61b3b27..5e048f781aa04be9ce993f1e7455bdc82df22bff --oneline
```

The four commits are `2a33089d30fd2514b6fd601c275e438b41302f0b`,
`cf3a9750ded32e9f876556794518771a6e92e882`,
`6971fd2a9647d077594ad66f24b5d0f29641cc5b`, and the candidate above.
HEAD and merge base resolved exactly and the checkout was clean. All 11 changed
file hashes matched the candidate manifest, frozen worktree and `git show`
bytes. All 71 focused input hashes independently matched both Git and worktree.
No earlier independent10022 finding or approval exists.

## Applicable standards and evidence read

The review applied candidate `AGENTS.md`, `README.md` development/build/audit
and proof-boundary rules, `docs/agents/architectural-quality.md`, domain guidance,
`GLOSSARY.md`, the ADR index and ADR0001/0006/0010, and
`docs/language-direction.md`. The review workflow, heuristics, shared review-loop,
example-driven statement review and worked-example guidance were read. No
additional applicable nested AGENTS, CODING_STANDARDS or CONTRIBUTING file was
found for these paths; isolated experiment guidance is outside this scope.

The complete original request, union clarification, task requirements and
dispatch were read. The user's local ticket/checkpoint instructions override
GitHub tracking, and the cross-cutting permission applies to this bounded
semantic foundation. Chapter2 remains earliest unaccepted. Nothing in this
review advances the chapter frontier or accepts the whole book/thesis union.

Author evidence read includes the complete body-accounting, pending-retention,
pure-body-count and body-realization reports and the separate final correction
report. Historical pending-compile statements were interpreted with their
explicit later terminal records, without rewriting their provenance. Source
context was checked through the full Chapter4 readiness and pure-cache-count
notes, the suspension inventory's relevant dynamic-order/retry/reentry sections,
and exact manuscript identity metadata. This review does not claim a new
exhaustive inspection of the book or thesis or a new source-fidelity acceptance
of all predecessor developments.

## Static architecture and statement assessment

All changed modules and documentation were read in full, including derivations,
not only names or author summaries. Necessary unchanged interfaces were also
inspected: the raw machine's event and force/write/unwind rules, continuation
append/boundary/stuck laws, Prefix observation and absorption, measured
Observation/workload/reweighting, pending membership, FreshEntries, boundedness,
value-cell persistence, successful-write provenance, finite pure freshness,
and the existing persistent realization interpreter.

### Existing semantics and reusable observations

`Applications/Suspensions/EventCounts.lean` uses an ordinary additive map from
the existing `FreeAddMonoid Event` to `Nat`. Its list-count definition, singleton
law and free additive lift agree. Successor, concatenated-budget, monotonicity
and finished-suffix facts use the original measured workload and actual
intermediate state. It introduces no alternate evaluator, trace generator,
resource executor or trajectory.

The new body projection is also an additive map. The compatibility theorem in
`BodyAccounting.lean` identifies the unchanged public `cacheWrites` map with the
corresponding selected-event count. Existing cache-write definitions/results
were not edited. The requirements explicitly permit adding this observation
without retrofitting earlier cache proofs. Similar induction shapes therefore
do not establish an actionable duplication finding under the review heuristics.

### Structural retention and explicit conditions

`PendingRetention.lean` defines exceptional unwind by actual raised control and
the selected address's exposed memoize frame. The classification proof splits
an existing pending frame from its earlier continuation, then uses
`step_append`, `step_boundary` and `step_stuck_append`. Its case analysis covers
terminal boundary kinds rather than copying the complete transition evaluator.

The classification has no boundedness, purity, initial Nodup or termination
premise. Its alternatives are inclusive, as required when duplicate pending
addresses are allowed. `PendingOrValue` keeps a real cell-or-frame disjunction;
it does not require unchanged cached payloads. Bounded memory is used where
value-cell preservation needs it. The finished outcome deliberately asserts no
residual-stack or cached-value fact, since subsequent observations are absorbing.
The actual body-entry successor comes from existing event-origin and transition
laws and pushes the same physical address.

`BodyAccounting.lean` defines `NoMemoizeUnwind` over actual unfinished prefix
states. It does not define the condition by the desired count, forbid every
exception, or derive it from normal final return. Its current, successor-shift
and finite-completion helpers preserve that scope. The raw count proof combines
this separate condition with existing FreshEntries and ConfigBounded. A first
entry establishes pending protection; the following zero-count result rules
out later entries. Zero budget, unfinished execution, delivered answers and
fault answers remain covered by the underlying sum/absorption cases. No initial
pending uniqueness or arbitrary raw termination premise is inserted.

### Pure source specialization and public use

`Pure/BodyCounts.lean` retains represented memory/environment, code and environment
admissibility, compatible primitives, hereditary output preservation, allowed
world and an actual finite `Progress.Evaluates` witness. It derives boundedness
through `start_bounded` and freshness through `finite_fresh_entries`. The extra
selected-address no-unwind premise remains explicit before the arbitrary budget.
The direct event-list corollary is a usable specialization of the same theorem.
It does not replace semantic hypotheses with a guessed execution bound.

The requirements exposed here fit the architecture's preference for ordinary
direct interfaces with explicit necessary laws. No large additional model or
global type-class bundle is forced on callers. The source and raw layers remain
separate and the earlier source domain is not silently narrowed to forbid
handlers or uncached exceptions.

### Occurrences, support and resource interpretation

`BodyRealization.lean` preserves order and multiplicity in `bodyAddresses` using
`List.filterMap`, then proves its per-address count correspondence. Ordinary
List Nodup and Finset cardinality laws establish the conditional passage from
occurrences to support; support cardinality is never declared additive.

The existing `realizeStep` and `Resources.run` receive singleton physical body
identities, empty support for other events and zero unshared charge. Their
general result counts distinct identities. Equality with total body-entry
occurrences requires the derived count/Nodup condition. Equal code at distinct
addresses remains distinct. The raw observation corollary connects the same
conditions and actual trace for every budget. No new interpreter is hidden
inside these proofs, and no arbitrary body-work or host-runtime claim follows.

### Connected examples and independent expectations

| Checked use inspected | Actual public connection and distinction |
| --- | --- |
| Unforced delayed literal | Reuses the prior two-transition execution; completed-zero theorem gives all-budget zero body entries, workload append uses the actual intermediate state, and reweighting uses the existing executor law. |
| Pending frame cases | `body_entry_pending`, `pending_mem_after_step` and `step_pending_or_value` supply the resulting frame/write/value facts. Normal write, exceptional loss, a buried frame, raw active reentry and duplicate initial pending frames remain separate. |
| Successful repeated force | No-unwind is proved over every actual prefix before completion21; the finite source theorem yields every-budget counts. The unfinished budget9 explicitly retains pending0, one body entry, zero writes and the universal bound's application. |
| Equal distinct allocations | The original source witness shows identical bodies/captures at0 and1 after6 transitions. The all-budget source theorem and conditional debit equality derive distinct charge2 at completion34. |
| Handler inside body | The source has an actual raised control at prefix13 with a handler above memoize. All30 relevant pre-completion prefixes discharge no-unwind, then the general source bound and realization theorem derive charge1; the condition does not ban exceptions. |
| Handler outside and retry | The unchanged finite pure program returns normally at50 with body/write/hit counts2/0/0. Applying the new source bound under an assumed no-unwind premise produces a contradiction. The actual list[0,0] has two occurrences and support/interpreter charge1. |

The positive debit charges depend on the new conditional bridge and public
source bounds, rather than only evaluating a closed resource expression.
Negative support/count results use the general arbitrary-word bridge and public
source count witness. Direct `rfl`/`decide` computations supply independently
specified instance data; they do not replace the public-theorem connections.
No native evaluation shortcut is introduced.

### Integration, documentation and proof policy

The nine new formal modules are explicitly imported by `SquareApplications.lean`.
Placement follows the existing suspension domain and checked-client layout;
the cross-domain resource adapter imports the existing persistent library.
The stable API document describes conditions, actual event meaning and open
work boundaries. It contains no local workflow/ticket status masquerading as
mathematical content. Formal claims remain Lean declarations; manuscript prose
is not a proof dependency. No manuscript, cache or generated output enters the
source difference.

Every new Lean file retains `autoImplicit false` and `warningAsError true`.
Static inspection found no new axiom, admission, unsafe/native proof shortcut,
proof-budget increase, linter suppression, toolchain/configuration alteration
or gate weakening. This lexical/source assessment is distinct from the still
required exhaustive transitive axiom audit. The four commit messages conform
to the local Conventional Commit convention with ticket10022 suffixes.

## Validation evidence and proof-repair history

The focusedr5 record is terminal, exit0, at the exact candidate. All71
queued/start/final input maps agree and independently match captured Git and
worktree bytes. Its raw log ends with successful completion of971 jobs. Earlier
targets are valid incremental replays; the final client compiled142s. This is
not a claim of a fresh recompilation of every target or of a full project gate.

| Round | Recorded source identity | Inputs | Actual terminal result |
| --- | --- | --- | --- |
|r1|577 baseline plus recorded new development inputs|68|exit1; reserved binder parsing failure; exact failed source reconstructed and hash-matched openly|
|r2|2a33089d30fd2514b6fd601c275e438b41302f0b|71|exit1; explicit filterMap reductions and source-client syntax/tactic problems|
|r3|cf3a9750ded32e9f876556794518771a6e92e882|71|exit1; tactic applied to already closed prefix goals|
|r4|6971fd2a9647d077594ad66f24b5d0f29641cc5b|71|exit1; final client needed explicit count/list-length bridges|
|r5|5e048f781aa04be9ce993f1e7455bdc82df22bff|71|exit0; all nine requested targets successful|

Every round's start/final input maps match. The final three correction commits
were inspected against the initial committed source; mathematical statements,
programs, captures, budgets and expected observations remain unchanged. The let
delimiter correction completes the intended proposition's syntax; the other
changes repair proof normalization/scheduling. The earlier reserved-binder rename
is separately documented with a reconstructed source matching the actual failed
input hash. Failed rounds remain evidence of their real errors, not successful
proof checks or invented mathematical counterexamples.

Successful focused evidence:

- `validation/body-entry-counts-r5.json`,26091bytes,SHA256
  `f2964a36e01bbcff0f68b66fb8755b97faa8a29d3f2c6d6ce46c301936175671`.
- `validation/body-entry-counts-r5.log`,6082bytes,SHA256
  `0d07a51ee2fe2f4c720f16869c39d76918ba5870f73dd51fb6b77b5dce9ce39e`.
- Finished at2026-11-03T03:31:14.967932UTC, with the pinned Nix
  `env LEAN_NUM_THREADS=1 lake build` invocation and all nine targets recorded.

The candidate's `.lake/verification.json` was absent during this review. The
manifest explicitly leaves its own full gate pending. Existing successful
focused outputs and the separate predecessor's running full check cannot
establish this candidate's integrated acceptance.

## Complete findings

### BODY-COUNT-STD-VAL-001 — exact-candidate integrated validation absent

**Severity:** High. **Status:** Unresolved. **Category:** Required validation,
not a static source defect.

**Rule:** `README.md` Build and audit / Proof and execution boundary;
ADR0010's public coverage and exhaustive-audit requirements; shared review-loop
Validation of the candidate; and the saved task's completion requirements.

**Evidence:** `validation/body-entry-counts-candidate-r1.json` records own full
gate pending and acceptancefalse. Focusedr5 invokes nine module targets through
`lake build`; it does not run stock source-policy/public-entrypoint coverage,
the full integrated build and exhaustive audit. No matching candidate verification
record or immediate final verification result is available.

**Consequence:** These successful focused proofs do not establish all integrated
consumers and exhaustive permitted-axiom policy for exact5e048f7. Standards cannot
be marked Passed or the candidate accepted from the available evidence.

**Required resolution:** Root must complete the unchanged pinned-Nix
`./check.sh --candidate HEAD` in the isolated stable clean checkout at exact
`5e048f781aa04be9ce993f1e7455bdc82df22bff`, preserve the terminal full log/result
and matching `.lake/verification.json`, and supply them to this retained review
loop. No source/toolchain change means the normal documented incremental mode
is the applicable gate unless an actual fresh-mode trigger arises. After both
independent axes pass, root must run stock `./check.sh --verify-candidate HEAD`
immediately before acceptance and confirm identical delivered bytes. Any failed
or mismatched result requires investigation and applicable revalidation.

No source correction is requested by this round. The existing predecessor and
chapter sequencing gates remain in force; no approval is inferred from ordinary
output transfer or another candidate's validation. Reuse this report and stable
finding for the same-candidate gate continuation; a changed candidate requires
both full-scope review continuations with all prior findings retained.

## Closing record

Base `577be121e074ddb5de6727a7481c115cb61b3b27`.
Candidate `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
Standards: **Blocked**; **0 static findings**, **1 unresolved validation blocker**,
worst severity **High**. The reviewer remains available for this loop's
corrections or exact-validation continuation.
