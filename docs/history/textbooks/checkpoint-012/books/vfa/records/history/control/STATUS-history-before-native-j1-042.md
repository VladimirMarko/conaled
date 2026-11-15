# Resume the VFA formalization

**The pinned compiler now works natively, and its external compatibility adapter
has passed independent Standards and Spec review. No VFA chapter is accepted.**
The user explicitly requested alternatives to slow QEMU execution. The exact
QEMU guide/launcher remains preserved in checkpoint038 as a fallback.

Read REQUIREMENTS.md together with AMENDMENTS.md, tickets.json and the source
AGENTS.md/README.md. Nix is optional under the user's exception; all compiler
pins, formal gates, chapter order, local tracking and checkpoint rules remain.

## Current identities and environment

- Formal candidate: `c988f183887896c00b09aaff9077a6ea7fb8d68f`, clean; two foundation imports narrowed.
- Previous formal candidate: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`; all other source bytes retained.
- Fixed enclosing review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Native operational base: `c411e6c04b4001b80f5b0da812b6792ee9190861`.
- Native operational candidate: `e41336d46dffd7bddd42b242a7ea7484a6055e43`.
- Native operational review: [1033-native-environment.md](reviews/1033-native-environment.md), both Passed, zero findings.
- Root final source/snapshot comparison: [acceptance.json](validation/1033-native-environment/acceptance.json).
- Lean4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake5.0.0-src+eb6cafb.
- All nine dependency revisions acquired clean; QEMU cache retrieval completed9,031 files, actual exit0.

The complete [native instructions](tooling/NATIVE.md), C source, launcher and
boundary test are saved under tooling/. The adapter supplies only the current
program's known executable path when its explicit identity matches AT_EXECFN.
It changes no official compiler bytes, host permissions or proof policy. It
does not synthesize RSS or claim accurate RSS-limit enforcement.

Captured-candidate isolated setup validation passed all17 commands, including
rebuilding the exact shim, parent/child versions, real boundary cases and two
Init-only kernel proofs through each route. Native and QEMU compilation of
unchanged Squares produced byte-identical .olean files. These are environment
results, not project validation or chapter acceptance.

## Interrupted attempt and new isolated checkout

QEMU fresh3 passed source/version/coverage checks and compiled Squares. The user
then requested native alternatives. Root interrupted owned tool session93349
with Ctrl-C; the tool reported exit130. The recorder did not flush a terminal
run record, and its last heartbeat preceded interruption. The raw child result
and descendant quiescence remain unestablished; quiet files are not proof of
quiescence. Keep [the actual interruption record](validation/1002-candidate-3279bac-fresh3-interruption.json).
No full fresh success or candidate verification record resulted. Historical
fresh1/fresh2 outcomes remain unknown and unchanged.

The new `vfa-native-validation/` worktree is clean at the exact formal candidate
and owns separate project output directories. Its external packages refer to
the existing nine clean pinned source/cache trees; no dependency writer is
scheduled. Neither old project output nor a prior success record is copied.
See [native-candidate-isolation.json](validation/1033-native-environment/native-candidate-isolation.json).
Every saved PID/session is historical after restore; do not signal it.

## Current performance investigation and next action

Native execution works, but the unchanged Squares sample took136.82seconds
wall time,2.99seconds user CPU and35.04seconds system CPU, with144,730 major
faults and peak RSS844,264KiB. This is evidence of substantial file-backed
paging/I/O, not an emulator-only bottleneck or attribution to another process.
The aggregate host observation shows no swap and does not establish the task's
actual memory limit. Do not infer a safe multi-process worker count from it.

A bounded scratch experiment changed only Squares' first line from import Lean
to import Init. All remaining definitions/proofs stayed byte-identical and
compiled successfully in4.79seconds, peak RSS491,512KiB and2,944 major faults.
The [experiment record](validation/1033-native-environment/import-footprint-experiment.json)
is not an integrated change or a general speed guarantee. Local#1034 has a completed
[bounded dependency assessment](validation/1034-import-footprint-plan.md), recommending
exactly the first-line Lean→Init replacements in Squares and Dependent, preserving
every other source byte. The other actual metaprogramming imports stay unchanged.
The two recommended import lines are now committed under #1034. Every
mathematical body remains unchanged; see validation/1034-integration.json.

The accepted native route was saved in checkpoint039 before source edits. The
two-line correction is captured in c988f18; full scope is25files,+496/-17 against
the unchanged enclosing base. The exact six-foundation checker then passed
(actual child, recorder and tool exits0), using copied exact-candidate source
bytes and separate output files. Its existing axiom reports and concrete cases
are retained in [1034-foundation-completion.json](validation/1034-foundation-completion.json).
This focused check does not replace the exhaustive integrated gate.

**Native fresh4 is now active** in vfa-native-validation/, through the unchanged
accepted recorder: [run.json](validation/1002-candidate-c988f18-native-fresh4/run.json),
with sibling child/heartbeat/launch logs. Live tool session:98926. The invocation
wraps ./check.sh --fresh --jobs1 --candidate HEAD with pinned_native_toolchain.py,
using one external compiler job and the LEAN_NUM_THREADS=1 environment setting.
This setting controls Lake's ordinary pool, not Lean CLI internal workers; the
current compiler launcher retains its CLI default. Actual preflight is
[1002-native-fresh4-preflight.json](validation/1002-native-fresh4-preflight.json).
It passed version/source/coverage checks, compiled Squares in5.33seconds and
Applications.AD.Core in430.83seconds;
no full terminal result or chapter acceptance is implied. Preserve its actual
completed outcome and fresh verification record before the next mode replaces it.

Disk free space fell to1.43GB at launch. The independently assessed one-time
retirement of the verified installer archive and9,031 completed compressed .ltar
downloads finished at16:52:34UTC, releasing1,068,105,728 allocated file bytes.
Actual free space immediately after was2,476,781,568bytes and continues to vary.
See validation/1034-current-capacity-assessment.json and
validation/1034-disposable-download-retirement.json. All installed/compiled
inputs, source/history/evidence and checkpoint copies remain. No other cleanup
or attribution of unrelated allocations is authorized by that finite record.

## Formal acceptance sequence remains

Use the existing [acceptance checklist](validation/1002-acceptance-evidence-checklist.json)
and the native adapter in tooling/NATIVE.md. Commands run in the clean isolated
formal candidate; wrap the checker directly, never inside lake env.

1. Full fresh candidate build and exhaustive audit, one module job initially.
   Preserve its actual result, complete log and matching fresh verification record.
2. The existing non-repairing artifact assessment, preserving any actual suspect
   surviving families before repair. Ordinary cold absences are not corruption.
3. Separate guarded incremental candidate build, classified invalidations,
   successful post-build integrity and a newly executed exhaustive audit. Preserve
   its separate incremental verification record.
4. Managed no-cache, rehashed +ProofAudit prerequisite, followed only after success
   by all four audit regression outcomes. Record unexpected prerequisite rebuilds
   and re-establish corresponding guarded evidence where needed.
5. Both independent formal axes on the same exact candidate. Reuse unchanged
   source analysis explicitly; ST-002 and SP-VAL-001 remain open until supported
   by the full new evidence. Incident origin may remain unresolved after supported
   candidate mitigation; do not claim a causal or race-freedom proof.
6. Root --verify-candidate immediately before accepting Preface then Perm.
   Upload the acceptance checkpoint before implementing Sort.

Chapter order: Preface → Perm → Sort → Multiset → BagPerm → Selection → Merge
→ Maps → SearchTree → ADT → Extract → Redblack → Trie → Priqueue → Binom → Decide
→ Color. All optional/advanced mathematics and explicit resource boundaries
remain in scope. Tickets/commits stay local; no GitHub writes.

## Durability

Latest saved source checkpoint:039,148,513,364bytes, SHA-256
`ec4310f49bb8845b968a8503fcee8dbc78dbc5f516cfb22992c72b5a9ffaf399`,
Library ID `libfile_e2e4ee38fd3c819186b3a7100b7e3b24`; creation/upload/local
verification receipts are retained. It preserves the native setup, full
operational review history, QEMU fallback and pre-correction formal source.
The two-line c988f18 source change, focused result and native fresh4 launch
postdate that capture. Next checkpoint identifier:040,
`conaled-vfa-checkpoint-040-native-foundations-validation.tar.gz`, preserving
the new candidate, successful focused check and active full-validation prefix.

Source checkpoints exclude downloaded toolchains/generated overlays/caches.
Restore into a new directory, keep work-state beside conaled, and use tooling/
NATIVE.md for native reconstruction. Prior state is retained in
STATUS-history-before-native-039.md and its linked histories.

## Checkpoint 040 saved

`conaled-vfa-checkpoint-040-native-foundations-validation.tar.gz` has been uploaded as `libfile_39f9c6c115388191b2b63a52472ffd53` (148,778,193 bytes; SHA-256 `f36118bc211f0067b4984e5ab89903a65b1eae4a2d224411cacf43292589b2be`). It captures current candidate `c988f183887896c00b09aaff9077a6ea7fb8d68f`, exact native setup, foundation success, and fresh4 evidence prefix. See creation/upload/verification receipts; no full formal acceptance is implied. Earlier latest-checkpoint pointers in chronological notes are superseded by this entry.

## Recovery follow-up after checkpoint 040

The exact versioned VFA archive was recovered again over ordinary verified TLS: all seventeen chapter hashes and the license match the preserved inventory. Reference bytes are under excluded `reference/vfa/vfa/`; see `validation/1030-vfa-source-recovery-current.json`. This changes no source scope.

A new finite capacity assessment rechecked saved identities for checkpoint036–039. Only those four generated local archive copies were then retired, reclaiming590,221,312 allocated bytes; their saved versions and exact receipts remain. Current040 and attached035, all source/history/evidence, installed runtimes and dependency outputs are retained. See `validation/1034-checkpoint-copy-retirement.json`; earlier statements that every local checkpoint copy remains are superseded by this dated entry.

The read-only `validation/1033-native-environment/native-performance-followup.md` records pinned loader/module/snapshot behavior and concludes there is no demonstrated drop-in speed optimization beyond the accepted native route and already-made import correction. Current validation inputs remain frozen.

## Thread-control correction and prospective assessment preparation

A pinned-source audit corrected earlier claims that `LEAN_NUM_THREADS=1` establishes one internal Lean CLI worker. It bounds Lake's ordinary build pool; the CLI uses `-j`/`--threads` separately and the frozen launcher passes no such flag. See `validation/1033-native-environment/concurrency-and-mmap-assessment.md`. A single explicit `-j1` FirstOrder probe completed0 in16.318s with the same `.olean` digest as the foundation check, under uncontrolled concurrent conditions; it establishes no causal speedup or full gate. Runtime/helper/wrapper inputs remain unchanged. The NATIVE.md prose correction is operational candidate `0afe0faa014512a0375bb158b6c8a56817075319`, base `e41336d46dffd7bddd42b242a7ea7484a6055e43`, pending its independent documentation axes.

The new `validation/1034-pre-guard-assessment-handoff.md` prepares a bounded read-only inspection after actual fresh completion. It targets the correct native candidate and explicitly permits only the nine same-name dependency targets in `vfa-validation/.lake/packages`; it retains revision/cleanliness checks. The helper passed22 synthetic checks and a narrow advisory after six recorded preparation fixes. It has not inspected real artifacts and its preparation checks are not formal review approval. Do not run it during active writers or treat it as permission to repair.

## Checkpoint 041 preparation

The NATIVE.md thread-control correction has passed both independent operational documentation axes and root's exact six-file delivery comparison. See `validation/1033-native-environment/thread-doc-acceptance.json`. Candidate `0afe0faa014512a0375bb158b6c8a56817075319` changes prose only; all native compiler/helper/wrapper and formal inputs remain unchanged. The corroborated small C++ source copies and upstream license/notice are preserved under that evidence directory's `pinned-source/`.

Space fell to149,397,504bytes. The completed installer and checkpoint036/037 paths were observed present again after their recorded one-time deletion; cause/writer is unknown. They are retained, not repeatedly removed. See `validation/1034-returned-download-and-checkpoints.json`. A separate newly assessed one-time cleanup removed only three redundant temporary files (verified partial installer prefix plus superseded checkpoint-stage bundle/source copies), reclaiming284,229,632 allocated bytes. See `validation/1034-superseded-temporary-retirement.json`. Immediate free space was611,422,208bytes, but the volume continues to vary.

Fresh4 remains active, with six successful compilation tasks through Applications.AD.Compiler952.81s and SquareKit.Relations4.88s at the latest observation. Actual formal completion, guarded incremental, audit regressions and both formal review axes remain required. The next complete checkpoint captures this ongoing evidence prefix and corrected setup; it is not chapter acceptance.

## Checkpoint 041 saved and capacity-accounting clarification

Latest saved checkpoint: `conaled-vfa-checkpoint-041-native-threading-and-recovery.tar.gz`,148,851,324bytes,SHA-256 `1c268a4bcd9132edd7880e5d6ab8154cc363d4b4f1b62638502f19547596e259`, Library identity `libfile_5b17af7751308191b12369a67c086059`. Actual creation exit0, bundle verification, restore/source/index and stability checks all passed, followed by successful upload/finalization and local metadata/digest checks. It supersedes earlier latest-checkpoint pointers, without chapter credit. Its own creation/upload receipts are naturally recorded after capture.

The earlier disk figures used `shutil.disk_usage.free`, which is available blocks, not all unallocated blocks. A subsequent statvfs observation showed0 available bytes but3,404,398,592 unallocated bytes; execution UID/EUID was0. No permission/reservation changes were made. The actual successful041 capture shows that zero available-block reporting did not establish a write failure. Neither figure guarantees future capacity or captures any task-specific quota. See `validation/1034-capacity-accounting-clarification.json`; use actual outcomes and both counters instead of claiming total disk exhaustion from the available-block field alone.

## Fresh4 handle unavailable; explicit CLI worker follow-up

At 2026-11-03T18:25UTC, polling saved live tool session98926 returned `Unknown process id`. The latest saved heartbeat is18:19:59UTC; the child log records123/953 modules through SquareKit.Internal.PathTransport.RawReindex. No terminal child/recorder/tool outcome or success verification record is available. Original run records remain unchanged. Silence and the lost handle do not establish descendant quiescence. See `validation/1002-candidate-c988f18-native-fresh4-handle-unavailable.json`; this supersedes earlier descriptions of a known active fresh4 session.

The #1035 original-Squares advised probe completed0 in6.9525seconds; the subsequent readlink-only explicit-j1 control completed0 in2.4449seconds. Both output hashes equal the earlier known compiled file. Cache/order/concurrent conditions were uncontrolled and observed peak RSS increased. No causal speedup or memory reduction follows. The mmap prototype will not enter production: its narrower practical result is available without interposition. `specs/1035-native-j1-adoption.md` records a separate two-file helper/guide iteration with unchanged official binaries/readlink shim, distinct overlay and explicit Lean CLI-j1. Operational captured-candidate validation/reviews/checkpoint remain pending before a new complete formal attempt in a separate checkout. No chapter credit.
