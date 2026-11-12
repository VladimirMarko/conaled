# Preparing the matched author trial

This package prepares six copied author trees, sealed phase files and records for
one check at a time. It does not launch agents, allocate goals, select a new model,
execute the trial or claim an authoring advantage. The amended
[protocol](../../../docs/research/dependent-conversion-authoring-protocol.md)
remains authoritative. Preparation and final source acceptance must pass before
exposure; the containing batch was still awaiting its final fresh receipt when
this package was prepared. Those prerequisites subsequently passed before
exposure. The [dated trial report](../results-2026-11-12/README.md) now records all
six submissions, successful focused replays and twelve passing full trial audit
contexts. Independent report acceptance and publication are recorded at the
exact revision on #423. The preparation and freeze history below is retained.

The coordinator owns `freeze.json`, `phase-policy.json` and sealed material.
Authors receive only their public inventory, instructions and their own work.
The frozen inherited request is gpt-6-astra / medium / openai through fresh
collaboration contexts without history forks or overrides. Parent metadata is
only parent evidence. Record each child's requested/reported configuration,
automatically inherited instructions, session ID and available context/usage
metadata before releasing a task. Exact serving revision stays unknown unless
reported. A changed effective model/configuration starts a separately labeled
cohort. No paid API purchase is authorized.

## Prepare copies and validate them

From the pinned repository development shell:

```sh
python3 experiments/dependent-conversion-authoring/execution/prepare_bundles.py \
  --repo . \
  --freeze experiments/dependent-conversion-authoring/execution/freeze.json \
  --output /absolute/new/coordinator-preparation
python3 experiments/dependent-conversion-authoring/execution/test_record_attempt.py
```

Use `direnv exec .` for noninteractive invocation from the repository. The output
must be new. Hash mismatches or symlinked inputs abort preparation. The tool
copies no Git history, private solutions or compiled artifacts. It copies five
project library sources for direct authors and ten for service authors. The
extra five implement normalization/conversion. Native `.ilean` import metadata
provided the provisional module list; the pinned native header parser and actual
compilation must check closure before exposure. Implicit `Init` imports are
supplied by the pinned Lean toolchain. Neither route needs a full project
umbrella or the repository artifact root.

`prepared.json` records the seed, randomized route assignment, input provenance
and copied file hashes. Exactly three of six fixed slot IDs receive each route.
Execute sequentially in numeric slot order as frozen in `freeze.json`, not in
the hash-sorted assignment order; otherwise all direct slots would run first.
Session IDs and reported child configuration remain null until recorded before
exposure. Prepared trees are not sessions or evidence of independent authors.

For each route, use a private source tree and private output root. Set LEAN_PATH
to that output root plus only explicitly inventoried toolchain resources, never
the full checkout's project artifact directory. Run the unchanged
`scripts/lean-source-info.lean` on the explicit source list; compare the returned
imports against the route/phase inventory and permitted Init. Compile in import
order with the pinned Lean executable:

```text
lean -R SOURCE_ROOT -o OUTPUT_ROOT/MODULE.olean SOURCE_ROOT/MODULE.lean
```

Retain command, cwd, source/import inventory, log, exit status and output hashes.
Check all six cumulative release states for both routes, including repair
baseline and full repair. Copy only these inspected generic/task-definition
artifacts into per-slot warm caches; never copy reference proofs or another
author's work. Record exact per-slot source/artifact identities before exposure.
An author's own helpers may persist, but changed inputs and their dependents
must be recompiled at the repair transition. Retain earlier outputs as history;
do not let them shadow the revised module.

The focused smoke checks are not a replacement for final exhaustive auditing.
The coordinator later checks submitted sources with the unchanged production
source policy and full candidate source-inventory mirror, matching all imported
origins and fresh submitted outputs. The author does not receive that full
mirror, ProofAudit, private oracle, or other authors' submissions. Final replay,
statement review and audit are separately recorded coordinator effort.

## Release phases without revealing later tasks

The output's `slots/SLOT/public` contains only initial tasks and that route's
library. `sealed/PHASE` contains later file copies and must stay coordinator-only
by policy. Directory separation is not an OS sandbox on this unrestricted host.
Do not point an author at the preparation root. Log commands/exposure, forbid
outside reads, and retain any accidental exposure rather than silently replacing
it with a clean attempt.

The phase order and continuation rules are frozen in `phase-policy.json`.
For each transition, the coordinator first archives the submission and current
release manifest, records the completion/checkpoint decision, and verifies the
next sealed file hashes against `prepared.json`. Then copy just that phase's
files into the slot's public tree and issue a new immutable release receipt with
slot/session, phase, decision, source hashes and actual UTC/monotonic observations.
Keep the previous receipt. No release function or background scheduler is
provided: release and metadata binding are explicit coordinator actions.

The repair baseline is an exact line selection from the hash-pinned accepted
Repair.lean. It retains assignment/typedness, before/beforeTarget, oldIndex and
BeforeTask. It omits after/afterTarget, newIndex and Task. The change release
replaces that module with the complete accepted file; all earlier declarations
are unchanged. These are frozen line selections, not a new Lean parser.
Compilation and statement comparison check the extraction. Preserve the
pre-change attempt, whether completed or sanity-stopped, before the change.
Both repair releases share the repair phase's checkpoint and single extension.

All authors receive the same task statements. Initial and scale phases require
the source derivations and retained index equations. Repair requires its revised
source equality/index and rejection of the old index. Held-out maintenance uses
the author's prior helpers. The HeadTask statement remains unchanged in the
negative file, but author success does not require rebuilding the private sheaf
model: require rejection of the changed-head equation with reason/evidence;
record uncertainty separately from rejection and checked inequivalence. Unknown
is not a proof. The sealed accepted model certifies nonderivability before the
trial; optional author inequivalence proofs are a separate observation. Both
routes must supply a checked IndexTask proof. The coordinator confirmed this
common rubric on 2026-11-12. No private solution is released at any phase.

## Record each check

`record_attempt.py` runs one supplied argv command, without a shell. It snapshots
the input, keeps context and source hashes, records command/cwd, UTC/monotonic
start and finish, output and exit status, and refuses an existing attempt path.
A separate `{source}` argument names the retained source; `{sources}` names its
one-element JSON source-path list for the native policy tool. For example, with
paths and environment supplied by the coordinator:

```text
python3 record_attempt.py --source Draft.lean --attempt OUTPUT/Policy01 \
  --cwd PUBLIC --context CONTEXT.json -- \
  lean --run PUBLIC/tools/lean-source-info.lean {sources}
python3 record_attempt.py --source Draft.lean --attempt OUTPUT/Attempt01 \
  --cwd PUBLIC --context CONTEXT.json -- lean {source}
```

Run both through the pinned environment, on the agreed CPU/build-lock policy.
The recorder does not choose environment variables, compile dependencies, enforce
import admission or decide whether a theorem meets the task. The coordinator
must check native source-policy output and imports against the released inventory;
a failed policy check cannot be accepted because a later Lean command succeeds.
Run any helper compilation through the recorder too, specifying its explicit
output path. Do not use project-wide `lake` targets from an author context.

Context requires slot, session, route, phase, release_sha256 and
environment_sha256. Bind those hashes to retained non-secret receipts. Record
assistance, actual usage and interruption observations in separate append-only
phase/event records, retaining raw provider fields and their provenance. Never
dump credentials or unrestricted configuration/environment contents. The
recorder's observation defaults are unknown/null, not measurements of zero.
Its durations do not measure active reasoning. Cached/reasoning token fields
must not be added again into a provider total that includes them. Provider totals
can include repeated and cached input; they are not author effort. Distinguish
per-turn from cumulative records and never sum successive cumulative totals.
Use 24,000 only as a recorded sanity-review trigger where the counter semantics
are usable, never as performance grading.

Ordinary check failures and command-start failures have final receipts. SIGINT
and SIGTERM request process-group cleanup and retain an interrupted receipt and
partial output. Cleanup sends SIGTERM, observes group existence for up to two
seconds, then sends SIGKILL to any remaining group even if its leader exited,
and observes for up to two more seconds. The cleanup observation records the
process-group ID, signals sent, errors and outcome. `confirmed-absent` means an
OS lookup reported no such group. `cleanup-unconfirmed` means the group still
existed at the deadline (possibly only unreaped zombies); `cleanup-failed`
records an OS error without confirmed absence. `no-child-handle` means no
process handle was available to clean up. These outcomes all retain status
`interrupted` and exit 130; only confirmed absence supports rescheduling without
further cleanup investigation. Unconfirmed/failed cleanup requires coordinator
intervention before continuing, and its output hash is only an observation at
receipt time because surviving work might still write. The recorder reaps only
its immediate child and cannot stop descendants that escape the group. These
are bounded OS observations, not a containment guarantee.
SIGKILL, host loss or an interrupted write may leave only a
started receipt: preserve it as incomplete, never infer success or zero usage.
Read-only snapshots and exclusive directory creation prevent accidental
replacement through this tool; they are not tamper-proof storage against an
unrestricted author or subprocess. No tool output is silently deleted.

The initial 75-minute/24,000-token values and 15/20/20/10/10 phase values are
sanity checkpoints. One equal-sized extension per phase is available for
unresolved work in a usable environment. Review before continuation; record
partial work, remaining obligations, interruptions and decisions. Infrastructure
interruptions pause/reschedule the same exposure where possible; replacements
stay separately labeled. Correctness defects stop the affected cohort and
require a new freeze after normal repair. Raw laptop wall time cannot rank
routes. Missing live token telemetry does not block this amended protocol.

## Remaining gates

Before dispatch, bind final source acceptance, independent package review,
native source-policy/import and phase compilation receipts, per-slot warm output
inventories, non-secret child configuration/exposure records, and coordinator
release authorization. Record all setup effort and missing active-time data.
Neither successful synthetic tests nor prepared directories satisfy these gates
by themselves. At package preparation time, no author trial had run.
