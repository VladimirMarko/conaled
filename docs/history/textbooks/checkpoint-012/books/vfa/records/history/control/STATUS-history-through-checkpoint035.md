# Resume the VFA formalization

**Whole-book work is in progress. No chapter is accepted.** This handoff follows
checkpoint 034. [STATUS-history-through-checkpoint026.md](STATUS-history-through-checkpoint026.md)
is the verbatim previous entry point, including post026 updates, preserved before checkpoint027.
Read [REQUIREMENTS.md](REQUIREMENTS.md), [AMENDMENTS.md](AMENDMENTS.md),
[tickets.json](tickets.json), and [conaled AGENTS.md](../conaled/AGENTS.md) with its
README/workflow pointers. The current disposition supersedes historical status statements.

## Objective, source and chapter sequence

Formalize all of Appel's *Verified Functional Algorithms* in Lean, harmonized with
conaled's interfaces and proof policy. Optional/advanced exercises, executable and
resource obligations, and Lean adaptations of Coq mechanics remain in scope.
Tickets, reviews and commits are local; **no GitHub writes are authorized**.
Create, restore-check, expose and upload complete source/history/tracking checkpoints
promptly. The accepted optional-cache amendment preserves these obligations.

Chapter order: **Preface → Perm → Sort → Multiset → BagPerm → Selection → Merge
→ Maps → SearchTree → ADT → Extract → Redblack → Trie → Priqueue → Binom → Decide
→ Color.** Finish each chapter's gates before implementing its successor;
cross-cutting preparation remains permitted. Preface (#1001) and Perm (#1002)
are current; Sort (#1003) follows acceptance. Plans/staging checks confer no chapter credit.

The pinned reference is **VFA 2.1, 2026-08-24 10:11**. Recover its official
[versioned archive](https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz)
and verify archive SHA-256
`f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`
and chapter identities using [SOURCE-RECOVERY.md](source/SOURCE-RECOVERY.md) and
the source inventories. [tickets.json](tickets.json), [specs/](specs/),
[source/](source/) and [reviews/](reviews/) index complete plans, coverage,
assumptions, resource models and reuse boundaries.

## Exact candidate and execution state

| Item | Identity |
| --- | --- |
| Formal candidate | `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec` |
| Fixed enclosing review base | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| Original main checkout | `/workspace/scratch/0c54f2db1fdf/conaled` |
| Original isolated validation checkout | `/workspace/scratch/0c54f2db1fdf/vfa-validation` |
| Full review history | [reviews/1002-Perm.md](reviews/1002-Perm.md) |

Both original independent Round 8 source reviews cleared the full corrected
23-file scope. **ST-001 is fixed; ST-002 and SP-VAL-001 are open. Both overall
review outcomes are Blocked.** Retain those source assessments and their full
history when assessing completed evidence; source clearance is not approval.

The previous fresh1 attempt used one worker:

```sh
LEAN_NUM_THREADS=1 nix develop --command ./check.sh --fresh --jobs 1 --candidate HEAD
```

**That attempt is incomplete; its actual exit status and cause are unknown.**
The monitoring handle and execution session became unavailable. Two scoped
native observations found no members of original group **426051**; the second
found no task validation working directory or log/private-output descriptor.
No success record exists. The retained log ends after module161; its final
recorded completion is not a full gate result. Fresh2 was launched under the separately reviewed recorder described below.

Read [the interruption assessment](validation/1002-fresh1-interruption-assessment.json),
including its frozen log/run copies, scan limits and resource observations.
The original [launch record](validation/1002-candidate-3279bac-fresh1.launch.json)
and `validation/1002-candidate-3279bac-fresh1.run.json` are preserved unchanged;
the latter's `running` state is stale, not evidence of a live or successful process.
Local **#1029** owns durable outcome/heartbeat recording and the unchanged-candidate retry.
Do not infer a compiler failure, OOM, storage failure or tool-layer cause from the loss.

The #1029 recorder is now accepted at
`f2dd147823effc78974d7b2e5363c993afb0f278`, after both independent reviews passed
and root verified the delivered files against the tested candidate. Read
[its acceptance record](validation/1029-recorder-acceptance.json),
[complete review record](reviews/1029-validation-recorder.md), and
[launch/monitor instructions](validation-recorder/README.md). Seven focused
real-process tests passed; no Lean command was a recorder test. The
[preflight](validation/1029-fresh2-preflight.json) observed clean formal checkouts,
no former owned-run paths/processes within its stated scope, and root-free
capacity above the existing launch floor. This does not establish full-build
peak fit or universal quiescence. **Fresh2 is running**, launched at **2026-11-02 21:34:09 UTC** after
checkpoint028 was uploaded and verified and root repeated the scoped ownership
and capacity check. It uses the same candidate, pinned environment, one job and
one Lean worker. [Session record](validation/1002-candidate-3279bac-fresh2-session.json),
[launch](validation/1002-candidate-3279bac-fresh2/launch.json),
[run state](validation/1002-candidate-3279bac-fresh2/run.json),
[heartbeat](validation/1002-candidate-3279bac-fresh2/heartbeat.log), and
[direct child output](validation/1002-candidate-3279bac-fresh2/child.log) retain evidence. **The recorder became unavailable while the checker continued.**
At 22:43:58 UTC, a scoped native scan found original checker578204 (same group/session,
now PPID1) and its Lean child, but did not find recorder578140. The tool session98080
also returned `Unknown process id`; the last complete heartbeat is 22:41:39 UTC.
Read [the assessment](validation/1002-fresh2-recorder-unavailable-assessment.json)
and [native observation](validation/1002-fresh2-handle-loss-first-observation.json).
[Later bounded native observations](validation/1002-fresh2-native-observations.log)
retain original process/start identities; they are historical observations, not
current-process or completion guarantees after recovery.
`run.json` is now stale recorder state. Keep its null return and unknown cause;
do not infer a terminal result. **Leave the observed active checker undisturbed
and do not start a duplicate.** Both original reviewers have clarified the existing native-record protocol in
[this prospective note](reviews/1002-fresh2-record-protocol-clarification.md):
if this checker completes and its genuine matching fresh record is corroborated,
quiescence established, and the pinned `--verify-candidate HEAD` succeeds,
recorded fresh build/audit completion can be established while the original raw
return remains unknown. [Root reconciliation](validation/1029-fresh2-record-protocol-adoption.json)
retains the earlier checklist unchanged. No gate is waived and no attempt or
chapter is approved by this prospective clarification. Source/coverage/compiler checks passed;
complete compilation/audit and all later gates remain pending.

Root owns validation. **After workspace loss, every saved session handle and
process ID is historical.** Establish actual ownership/state before creating
a replacement; an archive does not resume a process. Do not duplicate a still-active owned run.

## Integrity incident and evidence limits

The earlier incremental `3279bac` attempt ended with **ENOSPC, raw return 120**, on
2026-11-02 at 15:44 UTC. Before compilation, its guard had reported `.olean`
mismatches for `Applications.Resources.BoundedSummary`, `Examples.BoundedSummary`,
`Applications.Sequences.ByteBuffer` and `Examples.ByteBuffer`. Those mismatches
precede the storage failure. Their cause is unresolved; inactive-path recreation,
an observed reader, ENOSPC and the upstream GraphEmission incident are not an
established explanation.

Read [the reopened incident](validation/1025-integrity-reopening-20261102.json),
[the failed-run record](validation/1002-candidate-3279bac-enospc.json), and
[the affected-artifact manifest](validation/1028-affected-artifacts.json).
Original mismatched output/trace bytes were automatically invalidated and are
unavailable. Surviving/regenerated files have different provenance. Their local
`incident-evidence/1028-enospc` payloads remain outside complete source checkpoints,
but all 54 saved files are now preserved in the separate
[incident001 evidence archive](https://chatgpt.com/library?file_id=libfile_a3a4694ca8648191af74f70b39d404a5&account_id=personal),
715,268 bytes, SHA-256 `490921941ddf178563745ce0e9bf35b0de5ce538f7506499f4b0af944ae4b859`.
[Its verification](validation/1028-incident-archive001-upload-verification.json)
binds the successful upload and checks every payload against the original manifest.
This is evidence only; do not install it as a cache. The original mismatched bytes
remain unavailable, and the retained ENOSPC log may be incomplete.

Local #1025 is blocking; #1028 records capacity/validation recovery. The
[one-time capacity decision](validation/20261102-inactive-mathlib-retirement-after-enospc.json)
authorizes no recurring deletion of returned paths. Keep inputs stable, assess
actual capacity and preserve relevant evidence before repair or cleanup.

The [fresh2 capacity census](validation/1029-fresh2-capacity-assessment.json)
records selected allocations at 21:49 UTC and their limits. Root chose no
cleanup: it does not establish a full-build shortage or a causal growth rate.
At 23:01 UTC, root made a separate one-time decision to retire local025 after
[the exact full-read assessment](validation/1029-checkpoint025-retirement-assessment.json)
and an immediate identity/binding recheck.
[The action record](validation/20261102-checkpoint025-local-retirement.json)
retains its actual time, identity and capacity observations. Its successful saved
copy and receipts remain; no recurring deletion is authorized if the path returns.
A [second bounded census](validation/1029-fresh2-capacity-assessment-2318.json)
at 23:20 UTC observed unchanged allocations in the selected ordinary/dependency
build roots and only12,013,568 bytes of private fresh growth. Selected changes did
not account for the full free-space decrease; no cause was established.
After [separate full checks of026–029](validation/1029-checkpoints026-029-retirement-assessment.json),
root retired those four exact local duplicates once.
[The ordered action record](validation/20261102-checkpoints026-029-local-retirement.json)
preserves individual identities, outcomes and actual capacity observations.
All saved copies and receipts remain. No active build output was removed, and no
repeat deletion is authorized if these paths return.

On 2026-11-03 at 00:03 UTC, root separately retired the exact local030–032 duplicates
after [their complete eligibility assessment](validation/1029-checkpoints030-032-retirement-assessment.json)
and immediate identity/binding rechecks. [The action record](validation/20261103-checkpoints030-032-local-retirement.json)
records all three successful removals and observed root-free space of2,356,858,880 bytes afterward.
Their saved copies and receipts remain, as does latest complete local033. No repeat removal
is authorized if a path returns; no active compiler output or cache was changed.

The [single bounded resource observation](validation/1029-fresh2-resource-assessment.json)
at 23:53 UTC matched the original checker start identity and found no obsolete or
inactive high-memory task process suitable for termination. The cgroup was near
its8GiB limit with no recorded OOM kills; this does not establish a performance
or recorder-loss cause. [Root's disposition](validation/1029-fresh2-resource-disposition.json)
is to leave processes, flags, source and OS/cgroup settings unchanged.

The [workspace-only metadata census](validation/1029-workspace-capacity-assessment-0003.json)
at 00:04–00:05 UTC on November3 found10,818,228,224 allocated bytes in the task
workspace, including908,570,624 outside the earlier selected roots. Those omitted
areas have no earlier complete baseline. Matching ordinary/dependency build roots
were unchanged; private fresh output grew983,040 bytes since23:20. No cause or
newly eligible inactive cleanup target was established. [Root retained the same
no-additional-cleanup disposition](validation/1029-workspace-capacity-disposition-0003.json).

After checkpoint034 was saved and verified, root separately retired the exact
local033 duplicate at00:08 UTC on November3 following its full eligibility assessment
and immediate identity/binding checks. [The action record](validation/20261103-checkpoint033-local-retirement.json)
retains actual timing and capacity observations;034 and all saved copies remain.
No repeat deletion is authorized if033 returns.

The [returned-archive assessment](validation/1025-returned-archives000-012-013-assessment.json)
found exact legacy saved-content hashes for returned000/012/013, but all current
local Library bindings were absent. Before any new cleanup decision, root preserved
the exact three payloads plus current identities and prior removal/reappearance
history in [incident002](https://chatgpt.com/library?file_id=libfile_d3edb2d0713081918ac070597465019a&account_id=personal),
434,339,840 bytes, SHA-256 `a34d9162d2a050ae72f8915c358386805490d182b8d60e1e30e2253c75d1a697`.
[New upload verification](validation/1025-incident-archive002-upload-verification.json)
binds the saved companion; no old binding was reconstructed and no origin is established.
The current source recovery checkpoint remains034. [Root retained the historical
no-repeat exclusion](validation/1025-returned-archives-preservation-disposition.json)
and chose no removal of returned000/012/013. Observed free space increased without
a corresponding task cleanup; its cause remains unknown.

## Remaining gates, in order

Apply [the prospective checklist](validation/1002-acceptance-evidence-checklist.json)
in the same clean isolated candidate and pinned Nix environment. Focused checks,
cache companions and partial runs waive no stage below.

1. **Obtain a completed fresh validation.** Fresh1 was incomplete; retain its unknown
   actual return. Fresh2 was launched through the accepted #1029 recorder; the recorder is now unavailable while its original checker was observed active. The original null raw return must remain unknown unless directly recovered.
   Require complete compilation/audit and a genuine matching `fresh` success
   record. Preserve the actual return when observed; never infer zero. If the
   original wait status remains unavailable, apply the original reviewers'
   [native-record clarification](reviews/1002-fresh2-record-protocol-clarification.md),
   including attribution, completed-log assessment, quiescence, and a successful
   pinned `--verify-candidate HEAD` with its new actual result. Preserve the
   command, direct log, raw-status uncertainty, verified record and input
   identities before a later check removes the record.
   Private fresh outputs are temporary; success does not repair the normal cache
   or establish external-cache provenance.
2. **Inspect and preserve before the repairing guard.** This is planned, not
   executed. Once the checkout is stable and idle, follow
   [1025-pre-guard-preservation-plan.json](validation/1025-pre-guard-preservation-plan.json):
   `validate_layout`, then `inspect_outputs`, with normal targets and pinned inputs.
   [The static execution handoff](validation/1025-pre-guard-execution-handoff.md)
   supplies the exact one-shot body, environment, result semantics and capture paths;
   it is preparation, not an executed inspection.
   Classify discrepancies and preserve all surviving known/new suspect
   families, including currently consistent known families, traces, sidecars and
   available setup/command provenance, outside managed caches before repair.
   Durably preserve newly material incident evidence before the repairing guard.
   This non-repairing inspector invokes a pinned Lean helper and temporary manifest;
   it is not metadata-only, may report only the first reason per module, has no
   built-in helper timeout, and does not freeze inputs. Failure/interruption is
   not a clean result. The cache companion is not an incident-preservation tool.
3. **Run separate guarded incremental recovery** when preservation and incident
   disposition permit:

   ```sh
   LEAN_NUM_THREADS=1 nix develop --command ./check.sh --candidate HEAD
   ```

   Require success, classified invalidations, post-build integrity checking,
   a new exhaustive audit and a separate matching `incremental` record. This
   task retains both modes; preserve their evidence separately.
4. **Build the managed audit prerequisite, then run its regression:**

   ```sh
   LEAN_NUM_THREADS=1 LAKE_ARTIFACT_CACHE=false nix develop --command lake --no-cache --rehash build +ProofAudit
   LEAN_NUM_THREADS=1 nix develop --command lake env python3 scripts/test-proof-audit.py
   ```

   Proceed to the second command only after the first succeeds. Preserve exact
   outcomes: unused external axiom accepted; private transitive forbidden axiom,
   private admission and unsafe declaration rejected. See
   [the prerequisite record](validation/1002-audit-regression-prerequisite.md).
   Unexpected project-dependency rebuilds require recording and corresponding
   guard evidence to be re-established before regression. Do not hand-install artifacts.
5. **Complete both original review axes** on exact-candidate evidence, with supported
   ST-002/SP-VAL-001 dispositions. Candidate recovery may be accepted while #1025's
   origin remains open; record mitigation, not a proven cause or race freedom.
   New unexplained mismatch, drift or invalidation requires assessment.
6. **Root performs final verification immediately before acceptance:**

   ```sh
   nix develop --command ./check.sh --verify-candidate HEAD
   ```

   This checks the current record/identities; it does not rebuild, audit or rehash
   artifacts. Never restore an older record to mask failure. After all gates pass,
   accept Preface then Perm and applicable cross-cutting tickets; immediately
   create/upload an acceptance checkpoint before implementing Sort.

## Durable recovery and preparation

The latest uploaded complete source checkpoint is
[conaled-vfa-checkpoint-034-resource-and-capacity-evidence.tar.gz](https://chatgpt.com/library?file_id=libfile_fd1aadbc81288191ac3f5ac46476d128&account_id=personal),
**146,225,283 bytes**, SHA-256
`1408e77e0f8803f7c5a6116ac9275e330f5e9775b076250462d6916306b57e59`.
[checkpoints.json](checkpoints.json) and
[its upload receipt](validation/checkpoint034-upload.json) record the verified
identity. Its own receipt is later state for the next complete checkpoint.

Use the archive's `RESTORE.md` / `restore.py`; keep latest source/history and
work-state together. Follow [environment.md](environment.md) for pinned tooling
and an isolated checkout; fetch dependencies there without deliberately duplicating
the main cache. Keep writable outputs independent and verify input identities.
Source checkpoints restore neither processes nor compiled caches.

Optional [cache001](https://chatgpt.com/library?file_id=libfile_92fa73b259e4819190db24b064241592&account_id=personal)
remains bound to the exact uploaded **source023**, never to a later source checkpoint. Its identity,
successful receipt and immutable023 binding are in
[cache-companions.json](cache-companions.json) and
[cache-companion001-source-binding.json](validation/cache-companion001-source-binding.json).
Follow [CACHE-RECOVERY.md](CACHE-RECOVERY.md) and the accepted utility's
[README](cache-companion/README.md) for compatible, explicitly idle installation
into absent/empty project outputs; retain the latest work-state as task history.
It is optional unaccepted cache data and cannot satisfy the currently required
fresh validation or reconstruct the original mismatches.

The separate accepted utility candidate is
`a43cef4881d4eb303a81ef25f5ccff0b801a12fe`; acceptance and subsequent concrete-guide
review are recorded in [1027-acceptance.json](validation/1027-acceptance.json) and
[1027-operational-followup001-acceptance.json](validation/1027-operational-followup001-acceptance.json).
Local #1027 is complete as durability work, with no chapter credit; preserve its records.

[tickets.json](tickets.json) indexes later plans and sorting/table/resource/positive-key
drafts with exact hashes/reviews. Root owns integration, tracking, checkpoints and acceptance.

The [bounded external Lean reuse survey](source/EXTERNAL-LEAN-REUSE.md) is
advisory research only. It identifies small VFA-shaped sorting/accumulator
proof-script references, without a validated complete port, immutable dependency
pin, conaled compilation or axiom audit. It changes no plan, dependency, chapter
order or acceptance gate.
