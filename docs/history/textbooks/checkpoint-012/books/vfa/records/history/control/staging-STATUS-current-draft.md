# Resume the VFA formalization

**Whole-book work is in progress. No chapter is accepted.** This handoff follows
checkpoint 026. [STATUS-history-through-checkpoint026.md](STATUS-history-through-checkpoint026.md)
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

The most recent fresh attempt used one worker:

```sh
LEAN_NUM_THREADS=1 nix develop --command ./check.sh --fresh --jobs 1 --candidate HEAD
```

**That attempt is incomplete; its actual exit status and cause are unknown.**
The monitoring handle and execution session became unavailable. Two scoped
native observations found no members of original group **426051**; the second
found no task validation working directory or log/private-output descriptor.
No success record exists. The retained log ends after module161; its final
recorded completion is not a full gate result. No replacement formal run has started.

Read [the interruption assessment](validation/1002-fresh1-interruption-assessment.json),
including its frozen log/run copies, scan limits and resource observations.
The original [launch record](validation/1002-candidate-3279bac-fresh1.launch.json)
and `validation/1002-candidate-3279bac-fresh1.run.json` are preserved unchanged;
the latter's `running` state is stale, not evidence of a live or successful process.
Local **#1029** owns durable outcome/heartbeat recording and the unchanged-candidate retry.
Do not infer a compiler failure, OOM, storage failure or tool-layer cause from the loss.

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
`incident-evidence/1028-enospc` payloads are outside work-state and excluded from
complete source checkpoints; the manifest/diagnostics survive. Do not assume
those raw files survive workspace loss. The ENOSPC log may be incomplete.

Local #1025 is blocking; #1028 records capacity/validation recovery. The
[one-time capacity decision](validation/20261102-inactive-mathlib-retirement-after-enospc.json)
authorizes no recurring deletion of returned paths. Keep inputs stable, assess
actual capacity and preserve relevant evidence before repair or cleanup.

## Remaining gates, in order

Apply [the prospective checklist](validation/1002-acceptance-evidence-checklist.json)
in the same clean isolated candidate and pinned Nix environment. Focused checks,
cache companions and partial runs waive no stage below.

1. **Obtain a completed fresh validation.** Fresh1 was incomplete; retain its unknown
   actual return and assess #1029's outcome-recording plan before retrying.
   Require exit 0, complete compilation/audit and
   a matching `fresh` success record. Preserve its command, log, actual return
   code, record and input identities before a later check removes the record.
   Private fresh outputs are temporary; success does not repair the normal cache
   or establish external-cache provenance.
2. **Inspect and preserve before the repairing guard.** This is planned, not
   executed. Once the checkout is stable and idle, follow
   [1025-pre-guard-preservation-plan.json](validation/1025-pre-guard-preservation-plan.json):
   `validate_layout`, then `inspect_outputs`, with normal targets and pinned inputs.
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
[conaled-vfa-checkpoint-026-fresh-validation-progress.tar.gz](https://chatgpt.com/library?file_id=libfile_68c9ebaea698819196afd2b02009130a&account_id=personal),
**146,023,732 bytes**, SHA-256
`0068b157b143a50bce71590a083bf4f3bad1e56498c2a8ea81b355b66c5c3c70`.
[checkpoints.json](checkpoints.json) and
[its upload receipt](validation/checkpoint026-upload.json) record the verified
identity. Its own receipt is later state for the next complete checkpoint.

Use the archive's `RESTORE.md` / `restore.py`; keep latest source/history and
work-state together. Follow [environment.md](environment.md) for pinned tooling
and an isolated checkout; fetch dependencies there without deliberately duplicating
the main cache. Keep writable outputs independent and verify input identities.
Source checkpoints restore neither processes nor compiled caches.

Optional [cache001](https://chatgpt.com/library?file_id=libfile_92fa73b259e4819190db24b064241592&account_id=personal)
remains bound to the exact uploaded **source023**, never to026. Its identity,
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
