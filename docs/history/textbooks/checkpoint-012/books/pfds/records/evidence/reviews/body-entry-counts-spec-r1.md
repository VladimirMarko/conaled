# Local 10022 — independent Spec review, round 1

**Outcome: Blocked.** Complete static review found **zero code or specification
findings**. One required-validation blocker remains:
**BODY-COUNT-SPEC-VAL-001 (Blocking)**. No formal acceptance, chapter completion
or whole-union completion is established by this review.

Reviewer: `/root/body_entry_counts_review/spec`, independent of implementation
and of the Standards axis. This report was submitted without reading the
Standards report. The coordinator supplied scope and mechanical identity
evidence; this reviewer independently inspected the complete source change and
the mathematical connections described below. No compiler, audit, optional test,
output adapter, cache operation, Git mutation or remote write was performed.
Only this assigned report was written.

## Pinned scope and requirements

- Candidate: `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
- Fixed bounded, original integration and merge base:
  `577be121e074ddb5de6727a7481c115cb61b3b27`.
- Exact diff: `git diff 577be121e074ddb5de6727a7481c115cb61b3b27...5e048f781aa04be9ce993f1e7455bdc82df22bff`.
- Exact log: `git log 577be121e074ddb5de6727a7481c115cb61b3b27..5e048f781aa04be9ce993f1e7455bdc82df22bff --oneline`.
- Frozen isolated checkout: `/workspace/scratch/ca9a61d0bf30/body-counts`,
  clean at the candidate; reachable review ref `pfds/body-counts-review-r1`.
- Complete scope: **11 files, 1,424 insertions, four commits, no exclusions**.
  The commits are `2a33089d30fd2514b6fd601c275e438b41302f0b`,
  `cf3a9750ded32e9f876556794518771a6e92e882`,
  `6971fd2a9647d077594ad66f24b5d0f29641cc5b` and the candidate.

The complete governing texts are `requirements/REQUEST.md`, SHA256
`b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499`;
`requirements/REQUEST-union-v2.md`, SHA256
`3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c`;
and `requirements/body-entry-counts.md` version 1, SHA256
`1483d8bfc4470c4aa700c809209b3083db89fa713def40821e1968d9e3ce2a58`.
The exact candidate manifest is `validation/body-entry-counts-candidate-r1.json`,
SHA256 `99f2dab381933f68fa349b8e25d803bf234c3d40d9641808c440b46606ad7ea8`.

The user-authorized cross-cutting scope is respected. This task derives a
conditional consequence of the existing source semantics and connects one
selected event observation to the existing debit interpreter. It does not
implement a later chapter algorithm or close local 10017's complete source
incidence, primitive-cost or actual-work correspondence. Chapter 2 remains
the earliest unaccepted chapter. Local tracking and uploaded checkpoints
replace GitHub writes.

I applied the candidate's AGENTS and relevant README environment/build/audit
rules, shared review procedure, code-review and example-driven statement review
guidance, including its worked example. Architectural-quality, domain/glossary,
language-direction and ADRs 0001, 0006 and 0010 provide the applicable semantic,
composition and acceptance context.

## Source and author evidence

The source-scope inventory, Chapter 4 readiness note, pure-cache source report,
union source identities and all five current author/statement-review reports
were considered. Historical uncompiled handoffs were read as historical evidence;
their later corrected, focused-green source is the pinned review target.

For the decisive source boundary I directly read the existing extracted book
pages 31–33 and thesis Appendix A pages 134–135, and visually checked the supplied
thesis page 134 render. Book 31–32 explains delayed evaluation, successful
memoization and subsequent reuse. Appendix A134 explicitly preserves uncached
exceptional attempts; A135 distinguishes effectful self-reentry and its possible
overwrites from pure finite execution. The conditional scope and retained retry
case agree with that union. This review does not claim fresh inspection of the
entire book or thesis or acceptance of their complete semantics.

Author evidence inspected: `research/body-accounting-implementation.md`,
`research/suspension-pending-retention.md`,
`research/pure-body-counts-source.md`,
`research/suspension-body-realization.md`, and
`research/suspension-body-realization-correction-r1.md`. The complete retained
implementation record and initial design preserve the intended mathematics and
independent expectations. Direct code inspection, rather than author agreement,
supports the assessments below.

## Complete requirement assessment

### Actual events and their additive observation

`Applications/Suspensions/EventCounts.lean:17–37` defines an ordinary additive
map on the existing `FreeAddMonoid Event`. Its value is literal list occurrence
count; the lift theorem identifies the selected zero/one event indicator.
It neither synthesizes events nor substitutes a numerical upper bound for an
observation. The first-step equation reads the actual `transition` event and
then the actual successor workload. Concatenated budgets use the reached
intermediate state, preserving execution order.

The monotonicity and completion results at lines 75–120 use unchanged workload
append and absorption. A larger budget does not emit extra events after an
answer. The completed-zero result separates earlier budgets, bounded by the
completed count, from later absorbing suffixes. This supplies an actual
all-budget conclusion without claiming termination from fuel exhaustion.

`BodyAccounting.lean:79–88` selects the existing `.body address` event and exposes
the count equation. Its compatibility result for `cacheWrites` preserves the
old observation exactly. No old write-count theorem or public behavior changes.
The requirements expressly permit this compatibility law without a retrofit of
older cache-write proofs.

### Pending retention and the exact exceptional exit

`PendingRetention.lean:25–28` defines `UnwindsMemoize` from raised control and
the actual top memoize frame for the selected physical address. It is independent
of the desired count bound, excludes no unrelated address by definition, and
allows an exception whose handler is above the selected frame.

`pending_mem_after_step` at lines 33–90 splits the actual stack at an existing
memoize frame using `pendingAddresses_mem_iff` and ordinary list membership.
The isolated prefix's continuing case invokes `Continuation.step_append` to
retain the whole selected suffix. The terminal cases use `step_boundary` and
`step_stuck_append`; only the exposed memoize boundary needs inspection. A value
emits the actual write; a raised packet supplies the structural unwind; invalid
match boundaries and stuck results cannot be the supplied continuing successor.
This reuses the established continuation argument without duplicating the
evaluator or assuming the desired retention conclusion. The disjunction is not
claimed exclusive, which matters when an address occurs more than once.

`PendingOrValue` is the actual disjunction of a value cell and pending membership.
Its preservation theorem requires bounded memory for existing value-cell
preservation, plus the particular no-unwind premise. It requires neither a
unique pending frame nor fixed cached payload. A successful write branch obtains
the actual stored value through `cacheWrite_event_iff` and `memoize_lookup`.
The finished branch of `OutcomePendingOrValue` is intentionally `True`; it
does not invent residual stack or heap information. This is sound for the later
count argument because the existing observer makes finished outcomes absorbing.

`body_entry_pending` at lines 135–148 uses `body_event_iff` and `body_transition`
to construct the actual immediate successor with the selected frame pushed.
No assumption excludes an older occurrence. The one-step classification and
body-entry witness are unrestricted raw statements; their proofs introduce no
purity, totality, pending-Nodup or numeric-bound premise.

### Conditional count and its quantifiers

`BodyAccounting.lean:26–60` quantifies `NoMemoizeUnwind` over every actual
unfinished `Prefix.observe` state. The zero-budget current lemma and
one-step shift use the same observer. The finite-completion helper requires
every unfinished index strictly before completion to be safe, then invokes
`Prefix.stays_finished` for all later indices. It does not infer safety from
normal return alone or silently check only the final state.

The new zero-count theorem at lines 92–110 assumes actual `ConfigBounded`,
existing `FreshEntries`, selected-address no-unwind and initial pending-or-value.
At each step, value/thunk incompatibility or freshness excludes the selected
event; the disjunction and the two prefix properties advance to the actual
successor. Terminal branches contribute zero further events.

The at-most-one theorem at lines 115–141 considers the actual first event.
When it is the selected body event, `body_entry_pending` establishes the
successor premise of the zero-count theorem. Otherwise its selected indicator
is zero and induction continues. Thus it derives the count bound rather than
embedding it in a hypothesis. Its conclusion covers every finite budget,
including unfinished or faulting observations and unused budget after an answer.
It has no initial pending-Nodup, raw termination or purity requirement.

I inspected the unchanged `ConfigBounded`, `step_bounded`, `HasValue`,
`step_hasValue`, `hasValue_no_body`, `FreshEntries`, prefix and event-origin
interfaces used here. Freshness forbids entry while that address is already
pending; no-unwind prevents exceptional loss of the selected frame. They are
distinct semantic conditions, and neither is a restatement of the conclusion.

### Finite pure source specialization

`Pure/BodyCounts.lean:30–73` retains compatible raw/pure parameters, hereditary
primitive output preservation, admitted world/code/environment, represented
state/capture and an actual finite `Progress.Evaluates` witness. The selected
address is followed by its explicit no-unwind proof and then the arbitrary
observation budget. Boundedness comes from `state.bounded` and `start_bounded`;
freshness comes from existing `finite_fresh_entries` with the initial
representation and code admissibility constructed.

I inspected the unchanged `Pure/CacheCounts.finite_fresh_entries`,
`Pure/NoReentry.finite_body_entry_not_active`, source representation and
primitive compatibility/preservation interfaces. Freshness follows from the
actual finite pure execution and the earlier nonreentry theorem; callers are
not asked to assume body uniqueness. The new result preserves the separate
no-unwind premise and makes no claim that pure normal return establishes it.
The list-count corollary is the same observation, not a second trace semantics.

### Ordered projection, support and interpreter correspondence

`BodyRealization.lean:24–77` filters only body events to their physical addresses,
retaining order and multiplicity. The projection's per-address count equals the
actual body-entry count. The Nodup equivalence uses ordinary list counts, and
length equals finite-support cardinality only with the explicit Nodup premise.
`totalBodyEntries` counts occurrences and is additive; the support cardinality
is not incorrectly made additive.

The singleton `bodyDebits` map at lines 81–83 preserves each physical address,
including distinct allocations with equal code/captures. Every other event
has empty support. `body_realization_cost` applies the unchanged
`Resources.Persistent.realize_run_cost` with zero unshared charge and empty
initial support. The result is the number of distinct addresses for any event
word, including words with repetitions. The following conditional laws replace
support cardinality by actual occurrence count only after nonrepetition has
been established. The raw observation theorems derive that condition from
the public body-count theorem at every address and every budget.

I inspected unchanged `realizeStep`, `realizationSupport`, its exact run-cost
law and `Resources.run`/reweighting. No alternate resource executor, desired-cost
definition or body-work assumption has been substituted. The zero unshared
charge selects this event metric; it does not establish zero cost for non-body
machine work. Documentation and theorem comments retain the explicit remaining
primitive, body-work, source-incidence and algorithm obligations.

## Connected cases and nonvacuity

All four new clients were inspected in full, including their use of public
theorems and the premises they discharge. Exact reductions provide independent
instance data; they do not stand in for the universal-law connections.

| Case | Checked connection and meaning |
| --- | --- |
| Unforced delay | `SuspensionEventCounts.unforced_body_zero` applies the generic completed-zero law with the existing two-step completion and independent zero-body observation. The split-count case uses the actual intermediate state; expected allocation summands remain 1 and 0. |
| Buried memoize frame | `SuspensionPendingRetention.ordinary_prefix_retains_pending` uses the classification and excludes its write/unwind alternatives for the constructor-frame case. |
| Successful return | `normal_return_writes_and_preserves` derives the actual write from classification and the resulting value-cell fact from `step_pending_or_value`. |
| Exceptional exit | `exceptional_unwind_loses_protection` derives the unwind alternative and separately shows the resulting thunk has neither a value cell nor pending frame. |
| Raw reentry and duplicate frames | `active_entry_fails_freshness` contradicts `FreshEntries.current` at an actual body event while control is not unwinding. `duplicate_pending_is_allowed` applies preservation despite an actual duplicate pending list. These are local raw boundary cases, not claims that every raw reentrant program terminates. |
| Repeated force | The 21-step source execution is admitted and finite; all actual precompletion prefixes establish no-unwind. `Repeated.all_budgets` applies the public source theorem for every address and budget. Exact body/write/hit counts remain 1/1/1. |
| Unfinished first force | `Repeated.first_force_pending` exhibits the actual budget-9 residual configuration and pending frame, count 1 and write count 0, and includes the universal theorem's bound at that prefix. |
| Identical distinct cells | The budget-6 witness has equal literal bodies and empty captures at addresses 0 and 1. The 34-step trace enters both identities once. Its all-budget result derives from the source theorem, and the debit client derives charge 2 through the public bridge. |
| Internal handler | The 30-step admitted finite program catches the actual raised packet above memoize at prefix 13. All 30 preceding states satisfy the structural condition, including the raised state. It applies the source theorem and yields 1/1/1, then bridge charge 1. |
| External handler/retry | The original 50-step admitted finite normal-return program retains exact body/write/hit counts 2/0/0. Assuming no-unwind contradicts the new public source count law. The body list is `[0,0]`; Nodup fails, occurrence length is 2, support and general interpreter charge are 1. |

The positive debit cases consume `body_realization_cost_of_nodup` or
`body_realization_cost_of_counts` supplied by public source all-budget bounds.
The retry case deliberately uses the unconditional distinct-support theorem.
This preserves the intended distinction between a successful memoization count,
actual attempts and distinct debit identities.

## Integration, repair history and validation evidence

The exact full scope comprises the five new core modules, four connected
clients, `SquareApplications.lean` and `docs/research/pfds-body-counts.md`.
All nine Lean modules are imported by the public entrypoint. Existing machine,
cache-write, source-domain and resource-interpreter definitions are unchanged.
The API document explains the conditional theorem, physical identity,
exception boundary and body-entry-only metric. It does not assert algorithm
complexity or whole-source completion.

The direct diff from initial committed implementation `2a33089` through the
candidate confirms that later repairs add explicit filterMap reductions,
the intended let delimiter, tactic scheduling on remaining goals, and explicit
count/list-length bridge proofs. They do not change source programs, captures,
count expectations, observation budgets, theorem premises or numerical proof
limits. The earlier reserved-binder repair is retained separately with its
failed-source recovery record. These were elaboration/proof-script problems,
not evidence of changed intended mathematics.

I read the complete successful focused log and the terminal round records.
Rounds 1–4 each ended with exit 1 and unchanged recorded inputs. Round 5 ended
with exit 0 at the exact candidate on 2026-11-03T03:31:14.967932UTC, with all
nine targets successful in 971 jobs. The final client compiled in 142 seconds;
other targets could be reused from their matching completed outputs. Success
does not mean every target was freshly compiled in that final invocation.

The recorded 71 queued/start/final source/configuration maps agree. The
coordinator also directly compared every entry with both the exact Git blob
and frozen checkout. The matching evidence is:

- `validation/body-entry-counts-r5.json`, SHA256
  `f2964a36e01bbcff0f68b66fb8755b97faa8a29d3f2c6d6ce46c301936175671`.
- `validation/body-entry-counts-r5.log`, SHA256
  `0d07a51ee2fe2f4c720f16869c39d76918ba5870f73dd51fb6b77b5dce9ce39e`.

The focused invocation used the recorded pinned Nix shell and Lake targets.
It is not the stock complete candidate command. I directly confirmed that
`body-counts/.lake/verification.json` is absent. There is no supplied own full
candidate build/audit/record or final-verification success. Predecessor evidence
and checkpoint restoration cannot fill that acceptance gap.

## Complete findings

### BODY-COUNT-SPEC-VAL-001 — exact full candidate acceptance evidence absent

**Severity: Blocking. Status: unresolved. Category: required validation.**

**Requirement:** `requirements/body-entry-counts.md`, “Statement review,
integration and completion,” requires this exact isolated candidate's own
pinned-Nix stock full build and exhaustive audit, matching verification record,
both independent full-scope axes, and immediate final candidate verification.
README “Build and audit” and `docs/agents/review-loop.md` define the same gate.

**Evidence:** Only focused development success is available for candidate
`5e048f781aa04be9ce993f1e7455bdc82df22bff`; its manifest marks the own full gate
pending and acceptance false. Its `.lake/verification.json` is absent. The
predecessor `577be121e074ddb5de6727a7481c115cb61b3b27` is also unaccepted.

**Consequence:** Static mathematical review and matching focused targets cannot
establish public-entrypoint policy, complete project integration, exhaustive
transitive axiom audit or a valid acceptance record for this candidate. The
specification's completion criterion has not been met, even though no static
source defect was found.

**Required resolution:** Root must supply actual successful
`./check.sh --candidate HEAD` evidence in the stable isolated exact candidate,
including its terminal full log and matching verification record; continue both
retained independent axes on that scope and evidence; then run
`./check.sh --verify-candidate HEAD` immediately before accepting identical
reviewed bytes. If source or relevant inputs change, preserve this finding and
continue full-scope review of the new candidate. No source change or extra
optional test is requested by this finding.

## Result and continuation

Static code/specification findings: **0**. Required-validation findings: **1**,
worst severity **Blocking**. Spec outcome: **Blocked**, not Passed.

Base `577be121e074ddb5de6727a7481c115cb61b3b27`; candidate
`5e048f781aa04be9ce993f1e7455bdc82df22bff`. Reuse this complete assessment only
when base, candidate, full requirements, standards and relevant inputs match.
Preserve BODY-COUNT-SPEC-VAL-001 and the failed-round history during continuation.
I remain available for exact-gate evidence or full-scope correction review.
