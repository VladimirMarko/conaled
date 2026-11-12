# Cost ledger and measurement limits

This ledger separates shared admission/setup, author work and coordinator review.
It does not estimate active work from elapsed time or rank routes from laptop
wall time. Historical engine, preparer and reviewer labor is unavailable. The
four-hour preparer/reviewer planning values were not enforced or measured as
active-time ceilings; missing effort is unknown, not zero.

## Shared upfront work

| Cost category | Evidence and accounting |
|---|---|
| Existing reusable Lean/toolchain infrastructure | Pinned Lean 4.35.0, repository dependency/configuration receipts and production source policy/auditor. Historical labor unavailable; not charged per author. |
| #423 converter implementation and admission | Accepted source 1d9d4357; soundness/completeness of conversion, normal forms and typed substitution/renaming are supplied library obligations. Source acceptance receipts are retained. Historical implementation/review effort unknown. |
| Fixture and negative-oracle admission | Ten staged modules including direct/service references, separating model and Validate; full fixture audit and six negative controls. This work is shared upfront cost, not author work. The retained stage's older candidate label is reconciled by exact source correspondence before acceptance; it is not relabeled as a fresh check. |
| Execution package and preparation | Freeze, route assignment, recorder, twelve route/phase native smoke states, six private warm caches, bootstrap verification and release setup. Actual metadata and input hashes retained. Prior preparation ledger records its own wall interval and explicitly unknown active time/tokens. Later setup is additional, not covered by that partial ledger. |
| Shared review | Existing source/package reviews and later trial/report reviews are distinct from author work. Active reviewer time and total historical effort unavailable. Report review pending. |

The supplied model is admitted once into the comparison: authors receive scoped
Lean syntax and equality laws, with conversion available only to the service
route. The producer had to prove the library contract and check fixture source
and index obligations, including the private negative separating interpretation.
These costs are not hidden by the short service-side proofs, and are not charged
again for each scale instance. The trial does not admit an external source
language, lossless importer, richer identity witnesses or a new surface.

## Incremental author observations

Counts below are recorder commands, including cached commands, not model turns.
Policy invocations and compile invocations remain distinct in each summary.
The pre-Lean slot-1 missing-context error is an additional retained setup event,
not a recorder command. Failed attempts remain in the totals.

| Slot / route | Recorder commands | Failed commands | Selected source lines | Nonblank lines | Recorded command seconds |
|---|---:|---:|---:|---:|---:|
| 1 service | 14 | 1 | 130 | 94 | 19.269564 |
| 2 direct | 14 | 1 | 208 | 171 | 15.586583 |
| 3 service | 21 | 4 | 132 | 99 | 17.820686 |
| 4 direct | 13 | 1 | 130 | 110 | 11.462585 |
| 5 direct | 18 | 1 | 324 | 286 | 15.647927 |
| 6 service | 13 | 1 | 120 | 93 | 12.047675 |

Line counts include imports, options, comments and inline helpers in all selected
files. Repeated helper source counts at each retained occurrence; historical
unselected drafts and failure snapshots are recorded separately, not deleted.
They are physical source measurements, not effort or Lean syntax-node counts.
Caller syntax-node counts were not measured. Generated object-syntax node
counts, redex depths, widths, substitution counts and index sizes are the
separate frozen [fixture metrics](../fixture-metrics.json); the convention is
unchanged across routes. Source-node counts do not measure caller-written proof
size. Per-file bytes and both line counts are in each author summary.

Recorded command seconds are sums of each final receipt's monotonic finish minus
start, including command overhead. They exclude reasoning, phase coordination,
setup outside the recorder and subsequent replay/audit. No active reasoning
duration is available. Phase release/completion UTC and monotonic observations
are retained; subtracting tool time from their intervals would not recover
active reasoning or hidden suspension. Original receipts record hibernation,
throttling and background-load observations as unknown where unobserved.

## Raw usage observations

The table shows each frozen capture's last reported **cumulative** provider
counter. The raw event sequence also retains last-turn fields; successive
cumulative records must not be added. Cached input is a subset of input, and
reasoning output is a subset of output. No subset is added to the provider total.
The sessions began with generic inherited instructions and a metadata-only
bootstrap, so cumulative usage includes that context and repeated/cached inputs.
These counters are not unique authored content or measured effort.

| Slot | Input | Cached input (subset) | Output | Reasoning output (subset) | Provider total |
|---|---:|---:|---:|---:|---:|
| 1 | 1207157 | 1139328 | 9505 | 336 | 1216662 |
| 2 | 1431822 | 1392640 | 13225 | 1031 | 1445047 |
| 3 | 1270529 | 1211264 | 8227 | 370 | 1278756 |
| 4 | 1238396 | 1207424 | 9437 | 528 | 1247833 |
| 5 | 1267523 | 1235456 | 8404 | 450 | 1275927 |
| 6 | 1071358 | 1019648 | 8788 | 196 | 1080146 |

All these cumulative observations exceed the original 24,000 planning value.
The owner-approved policy treats it as a sanity-review trigger, not a hard
failure, replacement rule or performance grade. Phase-boundary decisions and
available counters are retained. Authors themselves reported unavailable usage;
coordinator-selected local rollout fields supply these later observations.
The 75-minute and 15/20/shared-repair-20/10/10-minute values were likewise sanity
checkpoints. No extension was used; completed phases proceeded after review.
The two repair releases share one interval. No hard token cap was enforced.

The records contain only selected session metadata, model/effort fields and raw
usage events. They do not include original rollout transcripts, prompts, hidden
instructions, credentials or unrestricted environment dumps. Slots 1–2's retained
raw usage format contains token events without a type tag; their bootstrap
metadata records configuration. Slots 3–6 also retain selected turn-context
fields. Exact serving revision and unreported internal activity remain unknown.

## Coordinator and total cost

Coordinator work includes all initial metadata/input checks, staged definition
compiles, source/import inspection, phase archiving, repair output isolation,
usage capture and freezing. It is separate from author command totals. The
coordinator's own commands and scripts are retained where recorded; unrecorded
active time remains unknown. Slot 1's supplied-definition root mismatch and
slot 2's first replay search-path failure are coordinator setup costs.

All six fresh replay sets and native policy passed. Production auditing is still
pending: one full context each for slots 1, 3, 4 and 6; two for slot 2; six for
slot 5. Their import-order and helper-origin work is review cost for the same
submissions, not additional authors or extra trial successes. Audit durations,
lock waits, full results and final review costs cannot be reported as zero while
pending. Root serializes these checks with other integration work; author
background-load observations do not establish comparable benchmark conditions.

No total-cost number or amortization break-even can be justified while historical
labor and active-time observations are unavailable. The ledger nevertheless
shows the upfront obligations, incremental checks/repairs/helpers and remaining
review costs separately. Equal completion in this small cohort does not establish
an authoring advantage, an industrial scaling law or a long-term maintenance
claim. No route adoption recommendation is made from source length or raw tokens.
