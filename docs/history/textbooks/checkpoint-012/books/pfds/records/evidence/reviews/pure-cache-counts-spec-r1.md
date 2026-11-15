# Local 10020 — independent Spec review, round 1

Review completed: 2026-11-03 UTC. Evidence last inspected at approximately
00:07 UTC. Reviewer: `/root/cache_count_review/spec`.

**Outcome: Blocked. Static Spec findings: 0. Required-validation findings: 1.**
The complete static review found no concrete mathematical, assumption, example,
or requirement-coverage defect. This is not acceptance: the exact candidate's
own full build, exhaustive audit, matching verification record and immediate
final verification are absent. `COUNT-SPEC-VAL-001` remains unresolved.

## Immutable scope and requirements

- Candidate: `3dd930c3e3989f3e5530463f3ac937a629551335`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/validation-cache-counts`.
- Branch: `pfds/cache-counts-review-r1`.
- Bounded task base: `361f5f3f6bb3de1974510ce355883dac2bf25333`.
- Original full integration base: `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`.
- Both bases are ancestors and their own merge bases with the candidate.
- Task scope: 13 files and 3 commits. Full integration scope: 14 files and
  4 commits. No exclusions.

I verified the resolved candidate and clean checkout, both ancestry relations,
the complete task/integration file sets, and the manifest's candidate file
hashes. I reviewed the full integration diff, not only its final commit. The
full commit list is `361f5f3f6bb3de1974510ce355883dac2bf25333`,
`78ed1a1501a955a5579a7a098910a5d4bc1361be`,
`0ebbf185d084b2cfe0b11501e8c7d4998932c16a`, and the candidate above.

The requirements used are the complete saved `session/requirements/REQUEST.md`,
`REQUEST-union-v2.md`, and `pure-cache-counts.md` version 1. The bounded
requirements SHA256 is
`fa5b5c01205aea18cc19aa53047cc7e0d57c0bb225534f0152bc04d7c87e569e`.
The dispatch is `session/reviews/pure-cache-counts-3dd930c-dispatch.md`.
The candidate manifest is `session/validation/pure-cache-counts-candidate-r1.json`,
SHA256 `14764869f0f8d659d8b894b5ec13d04658ffc9acd8c85085ade0e718a31a93a9`.

The source boundary is the uploaded book/thesis union, with this consequence
located at book printed pp31–33 and thesis Appendix A printed p135. The exact
source identities and existing page inspection are retained in
`session/research/union-source-identities.json` and
`session/research/suspension-foundation-inventory.md`. I inspected those records;
this review does not claim a new manuscript-wide or chapter-wide source audit.
The chapter frontier and the independent acceptance of local 10019/local 10014
remain outside this ticket's acceptance claim.

## Review method and complete file coverage

I followed the candidate's `AGENTS.md` pointers, README acceptance rules,
code-review/shared review-loop procedure, formal example-driven statement-review
guidance, domain and architectural direction, glossary, and applicable
ADRs 0001/0006/0010. The Spec assessment independently checked actual definitions,
proof derivations and clients. Author handoffs were evidence to investigate,
not substitutes for those checks. I did not read the Standards report or run
any compiler, build, test, audit, or cache operation.

Every full-integration file was reviewed:

| File | Spec assessment |
| --- | --- |
| `Applications/Suspensions/Pending.lean` | Actual memoize-frame extraction, transition provenance and conditional distinctness preservation. |
| `Applications/Suspensions/CacheWrite.lean` | Actual write characterization, settled state, frame disappearance and future no-write argument. |
| `Applications/Suspensions/CacheAccounting.lean` | Actual ordered-event charge, prefix freshness, count laws and raw conditional bound. |
| `Applications/Suspensions/Pure/CacheCounts.lean` | Finite pure nonreentry consequence and complete source specialization. |
| `Applications/Suspensions/TraceObservation.lean` | Exact existing traced evaluator/observer agreement, including an arbitrary prior log. |
| `Examples/SuspensionPending.lean` | Successful first push and an unrestricted duplicate pending-address case. |
| `Examples/SuspensionCacheWrite.lean` | First write, older-frame overwrite, mutable payload and outer-exception retention. |
| `Examples/SuspensionCacheAccounting.lean` | Exact five-event execution, general count use, prefix distinctness and later-hit zero counts. |
| `Examples/SuspensionPureCacheCounts.lean` | Required source cases, public theorem use, zero counts and unchanged unrestricted two-write observation. |
| `Examples/SuspensionTraceObservation.lean` | Actual trace with a nonempty prior log and exact appended event sequence. |
| `SquareApplications.lean` | All five new connected example modules enter the public integration closure. |
| `docs/research/pfds-cache-counts.md` | Claims match the raw/pure distinction, actual observation, finite-run premise and validation limits. |
| `docs/research/pfds-pure-suspensions.md` | Separate new accounting claim and precise exceptional-retention correction. |
| `docs/research/pfds-suspensions.md` | Incorporated documentation correction reviewed against the existing pure development. |

Relevant unchanged definitions were checked in the actual raw machine,
`Observation`, `Invariant`, `BodyEvent`, `ValuePersistence`, and
`Progress/Evaluation`; pure `NoReentry`, `Simulation`, `Memory`, `DomainState`,
`Domain`, `Compatibility`, and `WorldDomain`; and the existing cached-closure,
effectful reentrant-overwrite, and exception-retry examples. This resolved
whether the new hypotheses encode the intended semantics or assume the desired
count indirectly.

## Requirements and semantic assessment

### R1–R3: provenance, pending frames and the first successful write

`pendingAddresses` retains repeated addresses rather than deduplicating them.
Its membership theorem recovers an actual `.memoize` frame. The unchanged raw
transition's unfinished output either retains a sublist of old pending addresses
or adds the address of its actual `.body` event. The raw provenance result does
not assume purity, valid input state, or uniqueness.

`cacheWrite_event_iff` characterizes an actual `.cacheWrite address` by value
control and a top memoize frame. It correctly does not require the current cell
still to be a thunk: an older raw memoize frame can overwrite an inner successful
write. This is essential to retaining the unrestricted counterexample.

`Settled address config` is the conjunction of an existing value cell and absence
of that address from the pending frames. The no-write consequence uses frame
origin. Preservation uses bounded memory and the existing value-constructor
persistence law; a new same-address body entry would contradict that law.
`cacheWrite_settles` uses actual write evidence and distinct pending addresses
to remove the unique matching frame. Subsequent observation results retain the
necessary configuration-bounded premise.

The distinctions are meaningful. `ConfigBounded` checks memory/frontier and
memoize-address validity, not pending-address uniqueness. `HasValue` permits
payload replacement. The raw older-frame example contains a value and a pending
same-address frame, so it is not settled and does write again. The assignment
example replaces 7 by 8 through `.referenceWrite`, preserving the value constructor
without asserting payload constancy or counting assignment as memoization.

### R2, R4 and R5: the pure theorem discharges the raw premises

`FreshEntries` quantifies over actual unfinished `Prefix.observe` configurations
and their actual next body event. It says that event's address is absent from
the current pending list. It neither refers to write counts nor presupposes
termination. `FreshEntries.observe_pending_nodup` obtains distinctness from
this property and initial distinctness using actual transition provenance.

The raw `cacheWrites_observe_le_one` theorem requires exactly configuration
boundedness, initially distinct pending addresses and `FreshEntries`. Its
induction distinguishes a target write from another event. A target write
establishes settled status and therefore a zero-count suffix. Otherwise the
required invariants and freshness pass to the actual successor. The argument
does not require a finite-completion premise at this reusable raw layer.

`Pure/CacheCounts.lean:31–44` proves `finite_fresh_entries` from the existing
`finite_body_entry_not_active`. Membership in the extracted pending list is
converted back to a particular memoize-frame index; the existing nonreentry
theorem excludes that actual body entry using the actual finite raw evaluation.
That dependency itself derives the contradiction through representation,
active histories, pure recurrence and finite correspondence. Nonreentry is not
an added premise in the source theorem.

At `Pure/CacheCounts.lean:50–68`, `source_cacheWrites_le_one` derives initial
configuration boundedness from `StateRep.bounded`, initial distinctness from
the empty source-start stack, representation from `ConfigRep.start`, and allowed
control from allowed captures and code. The result then consumes the preceding
freshness consequence. Thus the raw uniqueness and freshness obligations are
discharged rather than passed on to a source caller. Composition with
`FreshEntries.observe_pending_nodup` also gives distinct simultaneous pending
addresses at every source prefix; the count proof carries that fact inductively.

Primitive compatibility, hereditary primitive-result preservation, allowed
represented world/state/captures, allowed code, and a genuine
`Progress.Evaluates` witness all remain explicit. `StateRep` and cached-cell
representation provide bounded memory and justified pure cache certificates,
not a history of at-most-one writes. `ConfigAllowed` describes admitted code
and values, not a count conclusion. Empty primitive types in the primitive-free
examples legitimately discharge primitive obligations; nonempty terminating
source programs supply the other premises, so the main claim is not vacuous.

The finite witness is a derivation of the unchanged deterministic evaluator.
Successful concrete `search_sound` uses construct that derivation. They do not
establish arbitrary termination from a merely chosen observation budget.
The theorem's separate address and budget parameters are universally quantified;
budgets may stop early or extend beyond the known answer. No claim is made for
arbitrary nonterminating pure executions, universal body-attempt bounds,
type safety, or host runtime complexity.

### R4: counts are the existing ordered observation

`cacheWrites` is an additive map on `FreeAddMonoid Event`, equal both to the
actual list count of `.cacheWrite address` and to the existing resource
reweighting construction. The successor and finished laws use the actual
`measuredStep`/`observe` definitions. Monotonicity, absorbing finished suffixes,
settled zero counts and completed-zero propagation cover both partial and
post-answer budgets. The pure list-count corollary at lines71–87 measures the
same trace; it does not introduce a second evaluator or assumed cost formula.

`traced_evaluates_observe` in `TraceObservation.lean` proves equality of the full answer
and of the exact appended ordered event list for an actual finite traced
evaluation. It explicitly separates an arbitrary prior log from the newly
observed events. The nonempty-prior client exercises that distinction; the
empty-prior specialization supports the preserved negative example.

### R6: connected source cases and counterexamples

The source examples actually apply the public pure count theorem with discharged
domain/representation premises and actual executions:

| Case | Connected evidence and discriminating boundary |
| --- | --- |
| Repeated successful literal force | Actual 21-step source execution returns 9; exact body/write/hit counts distinguish one evaluation from a later cache hit; the general list-count theorem supplies the arbitrary-budget bound. |
| Cached recursive closure | Uses the existing public 53-step `raw_source_execution` and admitted recursive program, whose closure captures its suspension and later forces the completed cache. This is an existing computed result, not an assumed cache certificate. |
| Two identical-body allocations | Actual 34-step source execution; the budget 6 prefix has distinct addresses 0 and 1 with the same thunk code and capture. Each address has its own successful write and the source theorem applies to every address/budget. |
| Handled exception retry | Actual 50-step source execution retries the fixed captured exception without reference effects or generative exceptions; two body entries, zero writes and zero hits. Completed-zero propagation proves zero writes at every address/budget. |
| Unforced delay | Actual 2-step completion plus completed-zero propagation proves arbitrary-budget zero writes. |
| Unrestricted reentrant overwrite | The original effectful source remains unchanged and the new statement still asserts `cacheWrites 1 (observe ... 300 ...).2 = 2`. It is outside the admitted pure domain. |

The final negative proof reuses the existing actual traced execution, the exact
trace/observation bridge, an independently checked 76-step completion,
deterministic evaluation uniqueness and finished-suffix absorption. It does not
weaken the expected count, reduce the required observation budget, or change
reduction limits. I inspected these proof connections and the existing source
definitions; I did not independently rerun or hand-enumerate all 76 transitions.

The lower-level clients also matter to the intended scope: actual raw reentry
creates duplicate pending addresses; an older memoize frame can overwrite;
assignment changes a value's payload; and an outer exception retains an inner
successful cache. The documentation now states that an exceptional frame skips
its own successful write while retaining the reached memory. Unchanged-thunk
retry is correctly attributed to its particular example. The separate 10019
`PREP-10019-02` boundary is not retroactively erased.

## Validation evidence and limits

The five successful focused records are terminal with exit 0 and stable
queued/start/final input fingerprints. I compared every final recorded input
hash to this immutable candidate and inspected the raw log endings. The matching
input counts are 20, 26, 29, 26 and 58 respectively. All seven earlier failed focused
attempts remain preserved: Pending r1/r2, CacheWrite r1, Accounting r1/r2 and
PureCacheCounts r1/r2. The latter failed in the negative client's default reduction
depth; the retained successful result has the original 300/2 statement.

| Focused record in `session/validation` | Record SHA256 | Raw log SHA256 |
| --- | --- | --- |
| `suspension-pending-r3` | `fa70cd81af7ce36993895c3fceecf8f0f8c47fcd678451ceb0710f63b86d2b1b` | `1f8ce3b7c369a0b1531cae45a0d0fa5df88279b62e6083a1f4828f03ff2934b5` |
| `suspension-cache-write-r2` | `d757b317c8837fa5ef56f30b4956154f9272d075e2d2392974d4e8a67797a6f3` | `18961a456eb4d6a8ca24c8b83011a75b663b848a64fde06a51f51df4abc74f1a` |
| `suspension-cache-accounting-r3` | `3a487946d56ebd5c603d2c269830fd697e8173e6e9847192d1f10c00f20e374f` | `3f530b71192dd6c01b4ff35f5beec66f29657c7319766e514895319374ea982a` |
| `suspension-trace-observation-r1` | `6381183ca50ec59499b92d7b75e835a6f1a4e84690ad5e5fde7a26671c5acaf9` | `65aaf8af1caa6fae39d0e5902af8b24d40bfbd8b2ec934b55263ce111b81985e` |
| `suspension-pure-cache-counts-r3` | `b7be6defc6d17bc1e7611afb1c262098ef5ae9122f66b156849d08f699ec74f3` | `8d535b14b3c8d456312bb3e74eb83f53c17a361184d51e6ce0f93ea48a6aeb7d` |

The pure count library had already compiled in its first focused round; its
input hash also matches the current candidate. The final focused round reuses
that ordinary output and checks the corrected connected client. This is
development evidence only. Neither focused builds nor ordinary output copying,
a donor record, or a predecessor's full gate establishes this candidate's own
acceptance. This reviewer did not run optional mechanical checks.

## Complete findings

### COUNT-SPEC-VAL-001 — exact candidate acceptance evidence is incomplete

- **Severity:** Blocking.
- **Class:** Required validation; separate from static mathematical findings.
- **Status:** Unresolved.
- **Requirement:** The bounded specification's acceptance section; candidate
  `README.md:157–192`, especially the clean committed-candidate procedure at
  lines170–189; and code-review/shared-loop requirements that missing required
  validation prevents a passing outcome.
- **Exact evidence:** Candidate
  `3dd930c3e3989f3e5530463f3ac937a629551335` has matching focused evidence as
  described above, but no completed own successful stock
  `./check.sh --candidate HEAD` with exhaustive audit and no matching success
  record. Direct read-only inspection found
  `/workspace/scratch/ca9a61d0bf30/validation-cache-counts/.lake/verification.json`
  absent. No own successful immediate `--verify-candidate HEAD` result is
  supplied. The dispatch explicitly retains this gap; root owns the full gate.
- **Consequence:** Static review and focused compilation cannot establish the
  mandated integrated build/audit acceptance of these exact source bytes.
  This axis cannot be marked Passed or used to accept local 10020.
- **Concrete remedy:** Root completes the documented stock pinned-environment
  full candidate check and exhaustive audit on the frozen candidate, retains
  the matching verification record and complete evidence, and returns that
  evidence to the existing review loop. Reconcile this finding and both axes
  against the exact candidate; run the documented immediate final verification
  before accepting and delivering those same bytes. Ordinary source fixes, if
  needed, require the existing loop's candidate update and reevaluation; they
  do not justify reusing an older approval record.

There are no additional static Spec findings. The claims remain explicitly
limited to the stated raw conditional results and finite admitted pure source
runs. They establish neither chapter completion nor a complete book/thesis
formalization.

## Final disposition

Bounded base `361f5f3f6bb3de1974510ce355883dac2bf25333`; original full integration
base `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`; candidate
`3dd930c3e3989f3e5530463f3ac937a629551335`.

**Spec: Blocked. Static findings 0; required-validation findings 1; worst issue:
unresolved blocking `COUNT-SPEC-VAL-001`.** Remain in this same review loop for
the exact candidate gate or correction continuation.
