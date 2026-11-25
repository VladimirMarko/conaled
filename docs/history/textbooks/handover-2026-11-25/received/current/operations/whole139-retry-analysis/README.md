# Whole139: read-only retry and environment analysis

Prepared by `/root/certificate_size` on 2026-11-24 for the root-owned continuation.
This is research and a proposed operational plan. It is not a compiler result,
acceptance record, independent review, or permission to change resource settings.
No compiler, process-control, output repair, cache cleanup, source mutation, Git
mutation, or GitHub action was performed for this task. The earlier frozen
certificate research and connected-example sets were preserved.

## Recommendation

After the **actual whole139 terminal** has been recorded and root has established
exclusive ownership of the acceptance outputs, the smallest fully guarded retry
is the same normal incremental command on the same candidate:

`./check.sh --candidate 50581179674f0ccf364ca3c372b5e07e5c70c80e`

Use the existing pinned native adapter and actual-result recorder. Keep the
checkout, candidate, dependencies, compiler, source scope, ordinary flags and
default scheduler/settings unchanged. Successful normal outputs from the first
attempt remain reusable; the ordinary pre-guard handles missing or invalid
project outputs through its existing repair policy. An unchanged failed build
does not itself require a wholesale cache clean. See `RETRY-PLAN.md` for the
prepared command and its terminal gates.

Root's alternative of completing failed targets one at a time through ordinary
Lake builds is a **documented development route** and can produce reusable normal
Lake artifacts. It is technically compatible with a subsequent complete guarded
check. Direct focused builds bypass the project's integrity guard and do not run
the complete inventory/audit; they are preparation, with separately recorded
results. A one-target invocation also retains Lake's default scheduling of its
dependencies, so this is not a claim of internally serial compilation or a cure
for exit137. Neither route is demonstrated to resolve the observed startup
delay. The plan is finite and conditional on the original invocation ending.

Primary sources: `work/acceptance139/docs/development.md` (focused development,
guarded incremental route, failed partial outputs and verification matrix),
`scripts/check.py`, `scripts/lake_integrity.py`, and
`docs/agents/lake-integrity-incidents.md`. Their observed hashes and important
execution inputs are bound in `OBSERVATIONS.json`.

## Exact failure evidence and source identities

The parent preserved a log prefix at 09:37:15Z in
`work/continuation/whole139-failure-prefix143.log`. It contains seven messages
reporting Lean subprocess exit137. The prefix is 1,268,672 bytes with SHA256
`57bada2a6addee30e05f6b7517580c5f68ef3f25848cf61c16ce2985e97547be`.
The companion `whole139-failures-observed143.json` records that this was a live
observation, not a terminal result. At a further read-only observation at
09:46:01Z both `whole139.child-exit.json` and `whole139.result.json` were absent.

| Prefix line | Affected module | Source bytes |
| --- | --- | ---: |
| 6469 | `Examples.CartesianFilling` | 12,910 |
| 6491 | `Examples.CartesianLargeFamilyConstructors` | 11,498 |
| 6506 | `SquareKit.Internal.Cubical.CartesianUniverse` | 129,109 |
| 6856 | `Examples.CubicalConstructorState` | 21,214 |
| 7129 | `SquareKit.Internal.Cubical.CocycleOrdinaryAction` | 1,751 |
| 7155 | `Examples.CubicalFrozenActionHomotopy` | 2,499 |
| 7332 | `Examples.DependentFunctionConversionSemantics` | 3,260 |

For every row, a direct read and Git blob comparison established:

`acceptance139 working bytes = candidate139 blob = public prerequisite M blob`.

Candidate139 is `50581179674f0ccf364ca3c372b5e07e5c70c80e`; public prerequisite M
is `ec4949a94ed70084d70f5b273fb0cc6dca8b2647`. All seven individual SHA256 values
are in the observation file. This rules out a direct source edit to those seven
files in candidate139 relative to M. It does not establish equivalence of all
transitive dependencies, successful compilation, the source of exit137, or an
absence of environmental problems. In particular, neither OOM nor a disk-full
event has been demonstrated. The complete terminal log may identify more failed
targets and must govern any eventual focused-target list.

The checker, its integrity helper, development guidance, shell entry point,
toolchain selector, root Lake configuration, manifest and ProofAudit also match
their M blobs byte for byte. All nine current dependency HEADs match their
manifest revisions. These are identity observations, not claims that this child
performed the full candidate cleanliness gate or validated dependency outputs.

## Why the normal incremental route is sufficient as a retry route

The pinned `check.py` performs the following actions on the ordinary path:

1. It removes any previous verification receipt, checks the exact clean
   candidate/dependency identities and pinned compiler, obtains the actual Lean
   parser/lexer inventory, checks the aggregate import coverage and source policy,
   and includes ProofAudit in the checked module closure.
2. It disables artifact-cache restore/write internally, calls the project
   integrity pre-guard with repair enabled, and invokes ordinary Lake with
   `--no-cache --rehash build` and every explicit inventoried module target.
   Lake owns incremental scheduling.
3. After successful compilation, it runs the nonrepairing post-guard and invokes
   `lake env lean -EhasSorry ProofAudit.lean` afresh. Cached module compilation
   never replaces the exhaustive audit.
4. It rechecks candidate/compiler identity and writes a matching successful
   verification receipt only after the full sequence succeeds.

A failed Lake command exits the checker before its post-guard, audit and success
receipt. The existing integrity helper checks normal trace/output identities.
Its pre-guard can invalidate the affected module artifacts and sidecars when
necessary; this is the established checker policy, not manual cache cleaning.

The repository explicitly documents that focused `lake build Module` is useful
for development and bypasses the guard. Therefore a focused success may be used
as a preparatory observation only. The complete acceptance retry still runs all
normal guards and the full inventory/audit, on the same immutable candidate.
No independent fresh output may be injected into Lake's build directory, and no
trace or hash metadata may be fabricated.

The unchanged validation implementation and seven exit messages alone do not
trigger a finding of stale-artifact corruption. If new evidence creates that
specific concern, use the repository's applicable integrity/verification rules;
do not pretend that this limited retry plan establishes the stronger boundary.
This analysis neither opens an integrity incident nor authorizes public issue
messages. The user's prohibition on issue558 progress remains in force.

## Native route and the delayed `lake env` diagnostics

The preserved native setup guidance supports both ordinary focused builds and
the exact guarded check in an independently managed isolated checkout. The
adapter verifies its profile/project pins, changes to the selected project, and
executes the requested command under the preserved runtime. It does not add a
command timeout or resource limit. The direct route requires one output owner;
it is not a managed-build lock service. Root's existing `run_recorded.py` uses
that adapter, records the actual child exit before post-run input hashing, and
refuses to overwrite older evidence. Its options must precede its positional
run name.

Root reported prompt successful bare `lean --version` and `lake --version`
diagnostics, while `lake env lean --version` and two source probes had not yet
returned. This child did not run or repeat any diagnostic executable.

The installed pinned Lake sources give a concrete distinction:

- `Lake/CLI/Main.lean`, `Lake.env`, calls `loadWorkspace` and constructs the
  augmented environment **before** spawning the requested command when a package
  configuration exists. A delay here need not involve the requested Lean proof
  elaboration.
- `Load/Workspace.lean` loads the root and dependency configurations. Configuration
  caches are located under each workspace's `.lake/config/<package-index>` by
  `Load/Config.lean`, so the author and acceptance configurations are separate.
- `Load/Lean/Elab.lean` opens the configuration trace with a shared blocking lock
  before a cached configuration import. Reconfiguration has a separate
  nonblocking `.olean.lock` attempt and an exclusive trace lock. Thus the absence
  of Lake's old whole-build lock does not imply absence of all startup locks.
- `Load/Materialize.lean` returns before a Git fetch when the checkout HEAD is
  already the exact requested revision. All nine observed HEADs match their
  manifest pins. This narrows the ordinary revision-resolution path; it does not
  establish that all other configuration evaluation or I/O is fast.

At the earlier metadata observation, the author and acceptance mathlib and
proofwidgets cached configuration traces/oleans retained their initial setup
timestamps. Their traces recorded the pinned Lean hash, platform and expected
configuration options; no `.olean.lock` filename was present in those indexed
directories. These facts do not identify the blocking instruction or owner of
any lock, and a missing lock filename does not rule out open handle locks.

No concrete stall cause was established. There is no evidentiary basis here for
removing a lock, changing the Lake configuration, disabling environment checks,
altering compiler settings, or assuming that further source edits would fix the
delay. The parent's denied ptrace attempt is preserved separately; this analysis
does not escalate it or substitute an unobserved diagnosis.

## Disk footprint and reproducible retirement boundaries

At 09:46:01Z, `statvfs` reported a volume of 20,957,446,144 bytes with
1,829,433,344 bytes available to the current user. An earlier read-only `df -h`
displayed 20G total, 17G used, 1.8G available and 91% use. Space pressure is
concrete, but these figures are not evidence that it caused exit137.

Approximate allocated-size observations from completed read-only `du` calls:

| Holding | Size | Operational boundary |
| --- | ---: | --- |
| `work/conaled/.lake/packages` | 7.3G | Active pinned shared dependencies; retain |
| `work/acceptance139/.lake/build` | 2.9G | Live normal build outputs; retain |
| `work/external-tools/lean-4.35.0-linux` | 3.0G | Active complete pinned toolchain; retain |
| `work/conaled-public` | 517M | Separate public source checkout; conditional candidate only |
| `work/checkpoint139-preparation` | 42M | Frozen preparation; conditional candidate only |
| `work/checkpoint140-preparation` | 70M | Failed-attempt preparation; conditional candidate only |
| `work/checkpoint140a-preparation` | 103M | Frozen corrected preparation; conditional candidate only |
| `checkpoints` | 50M | Actual retained archives; retain |
| `restored` | 121M | Original history and recovery instructions; retain |

The main consumption is in the active dependencies, toolchain and acceptance
outputs. There is no established large disposable cache in this evidence.

Two conditional reproducible retirement possibilities can be assessed by root,
without involving compiler artifacts:

1. Completed checkpoint preparation/frozen copies total approximately 215M.
   They may be retired only after an exact survivor mapping proves that every
   useful unique file is present in the retained verified/saved recovery record,
   no active packing job reads them, and all operational receipts remain outside
   the targets. Checkpoint139 and140a have actual saved/recovery receipts.
   Failed140 was not saved or accepted; its useful failure evidence must be
   accounted for in the successor rather than assumed redundant.
2. The separate public checkout is approximately517M and has its own Git common
   directory. Neither author nor public repository uses Git object alternates.
   This removes one possible object-storage dependency, but does not prove that
   the public checkout is unused or has no unique refs, edits, objects or needed
   path references. The complete publicM source must remain recoverable from an
   independent retained repository/source. Root must check these conditions
   before treating this checkout as reproducible; this analysis does not mark it
   ready to delete.

The existing `work/checkpoint140a-results/retire140a-copies.py` demonstrates the
session's stronger retirement practice: exact save/archive/recovery identity,
actual exit0 receipts, explicit target allowlist, symlink rejection, surviving
path checks, and separate intention/completion evidence. Its authorization
covers exactly three already-retired stage/extract/recovery copies, not these
new candidates. Its retained-path list explicitly kept the preparation and
public checkout. It must not be rerun or generalized as silent authorization.

Any new retirement should preserve the current author source, isolated
acceptance checkout, active dependencies/toolchain, Git retention refs and
objects, original histories, complete archives, useful research/drafts,
continuation logs and actual save/recovery/validation receipts. Logical byte
counts are not guaranteed free-space deltas while other work continues.

## Reading and outcome limits

The local pinned checker, integrity helper, development/runbook guidance and
native setup/run path were read. The relevant installed Lake workspace loading,
configuration import/locking and materialization paths were read; the entire
Lake implementation, all transitive module dependencies and OS process/lock
state were not audited. Root owns the running builds and all later execution.

The original complete textbook programme, qualification counts, review findings,
requirements and same-cutoff single-archive policy are unchanged. This report
adds no mathematical acceptance or completion claim. Preserve it as additive
environment evidence in the next single recovery checkpoint.
