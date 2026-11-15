# Resume the VFA formalization

**The pinned Lean/Lake installation runs natively. The separate launcher with
an explicit Lean CLI worker setting has passed isolated validation and both
independent operational reviews. No VFA chapter is accepted.**

Read REQUIREMENTS.md, AMENDMENTS.md, tickets.json, the restored AGENTS.md and
README.md. The user allows exact pinned programs outside Nix. Chapter order,
local tickets, all proof/build/review gates and immediate checkpoint uploads
remain required. No GitHub writes are authorized.

## Current identities

- Formal candidate: `c988f183887896c00b09aaff9077a6ea7fb8d68f`.
- Fixed enclosing formal review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Current operational native-j1 candidate: `c1121c5b99e8714a0d91eab0db6bb60f7c650f2c`.
- Its review base: `0afe0faa014512a0375bb158b6c8a56817075319`.
- Operational acceptance: [1035-native-j1-acceptance.json](validation/1035-native-j1-acceptance.json).
- Existing operational review history: [1033-native-environment.md](reviews/1033-native-environment.md).
- Formal review remains Blocked: [1002-Perm.md](reviews/1002-Perm.md); ST-001 fixed,
  ST-002 and SP-VAL-001 open.

The formal diff against its fixed base is25files,+496/-17. The only changes
from3279bac are `import Lean` to `import Init` on the first lines of Squares.lean
and Dependent.lean. All mathematical bodies and the previously reviewed23files
are unchanged. The six-foundation check passed; the full candidate gates have
not passed. See validation/1034-integration.json and1034-foundation-completion.json.

## Native setup and actual validation

Use [tooling/NATIVE-J1.md](tooling/NATIVE-J1.md), with
[tooling/NATIVE.md](tooling/NATIVE.md) for official installation and the accepted
readlink-shim build. The original QEMU guide/launcher remains available in
`tooling/README.md`, `tooling/pinned_toolchain.py` and
`environment-guides/user-supplied-lean-lake-qemu-guide.md`.

The new `pinned_native_j1_toolchain.py` creates its own
`toolchains/lean-4.35.0-native-j1` overlay. It uses unchanged official Lean4.35.0
(commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc), Lake5.0.0-src+eb6cafb,
and the same accepted executable-path shim. Existing native/QEMU helpers,
overlays and guides remain unchanged. Dependencies stay pinned to the manifest,
including Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679.

Three separate controls apply: fresh-check `--jobs 1` limits external compiler
jobs; `LEAN_NUM_THREADS=1` controls Lake's ordinary pool; the new Lean wrapper
prepends an actual `-j1` CLI option. Later explicit compiler options can override
it; supported acceptance commands do not. This is not an all-OS-thread bound.
Unavailable procfs RSS enforcement is not supplied by the shim.

Captured-candidate validation completed with15recorded commands, all exit0.
It covers versions, exact wrapper argv, direct and Lake-env Init proofs with
no reported axioms, ordinary Lake compiler selection, private LEAN_PATH and
`--run` literal argument preservation, known original Squares output bytes,
and protected-input identity. See
[1035-native-j1-validation-completion.json](validation/1035-native-j1-validation-completion.json).
The first validation runner had a preserved substring-assertion false positive
before compilation; its corrected run used the same unchanged production
candidate in a new isolated checkout. Both independent operational axes Passed,
with zero findings, and root independently compared all8delivered source files.

The original Squares experiment with explicit-j1 plus MADV_RANDOM completed0
in6.9525seconds; the subsequent readlink-only-j1 control completed0in2.4449seconds.
Both matched the previously known compiled output. The captured-candidate
Squares check also matched (7.55seconds). Cache/order/concurrent conditions were
uncontrolled; no causal or whole-project speed guarantee follows. Peak RSS was
higher in the fast samples, so no memory reduction or safe increased process
concurrency follows. **The mmap prototype is not adopted.** Preserve its source,
boundary tests and outcomes under validation/1035-mmap-random-prototype/.

## Lost fresh4 session and prepared next attempt

The previous native fresh4 live handle98926 returned `Unknown process id` at
18:25UTC on2026-11-03. Its saved heartbeat stops at18:19:59UTC, and its log
contains123/953 module completions. There is no terminal child/recorder/tool
result and no candidate success record. Original records are unchanged. See
[handle-unavailable.json](validation/1002-candidate-c988f18-native-fresh4-handle-unavailable.json).
Do not infer success, termination or descendant quiescence, signal saved numeric
PIDs, or combine that prefix with a later run. Older unknown/interrupted runs
remain historical; their limitations are retained in the history and evidence.

A new clean candidate checkout is prepared at `vfa-native-j1-validation/`, with
separate project outputs and no copied success record. Its9package links point
to the same-name clean exact-revision dependency trees under
`vfa-validation/.lake/packages`. No dependency writer is scheduled. See
[1035-formal-candidate-isolation.json](validation/1035-formal-candidate-isolation.json).
These generated checkouts/runtimes/caches are not included in source checkpoints;
reconstruct them on restore from the exact source and setup guides. All saved
session/PID values are historical after restoration.

The next full attempt is `1002-candidate-c988f18-native-j1-fresh5`, through the
unchanged accepted recorder and new native-j1 helper, with one external compiler
job. **It has not started at this checkpoint preparation.** First finish
checkpoint042 creation/upload, then perform live preflight and launch it.

## Formal acceptance sequence

1. Complete a new full fresh candidate build and exhaustive audit. Preserve its
   actual terminal outcomes, complete log and matching fresh verification JSON.
2. Establish stable idle inputs and run the non-repairing assessment before any
   repairing guard. The context-correct prospective command is
   [1035-pre-guard-invocation.json](validation/1035-pre-guard-invocation.json), using
   the unchanged collector and scope described in1034-pre-guard-assessment-handoff.md.
   It targets the new native-j1 checkout and new fresh provenance. It has not run.
   Cold absences are not corruption; preserve actual suspects before repair.
3. Run a separate guarded incremental candidate check, classify invalidations,
   retain successful post-build integrity and a newly executed exhaustive audit,
   and preserve its separate incremental verification record.
4. Complete the managed no-cache/rehashed `+ProofAudit` prerequisite, then all4
   audit regression outcomes. Investigate unexpected prerequisite rebuilds and
   reestablish corresponding guarded evidence where required.
5. Both independent formal axes review the exact full candidate and evidence,
   explicitly reusing unchanged source analysis. Resolve ST-002/SP-VAL-001 only
   with actual support. Historical mismatch origin may remain unknown; supported
   mitigation does not prove cause or race freedom.
6. Root runs `./check.sh --verify-candidate HEAD` through the same launcher
   immediately before acceptance. Accept Preface and Perm only when all gates
   pass; upload that acceptance checkpoint before implementing Sort.

Chapter order: Preface → Perm → Sort → Multiset → BagPerm → Selection → Merge
→ Maps → SearchTree → ADT → Extract → Redblack → Trie → Priqueue → Binom → Decide
→ Color. All optional/advanced mathematics and explicit resource boundaries
remain in scope. Existing chapter/source inventories and reviewed plans remain;
do not restart planning or create another enclosing review workflow.

## Durability and recovery facts

Latest actually saved checkpoint at this preparation is041:
`conaled-vfa-checkpoint-041-native-threading-and-recovery.tar.gz`,148851324bytes,
SHA-256 `1c268a4bcd9132edd7880e5d6ab8154cc363d4b4f1b62638502f19547596e259`,
Library identity `libfile_5b17af7751308191b12369a67c086059`.
Next:042, `conaled-vfa-checkpoint-042-native-j1-validation-readiness.tar.gz`,
preserving the accepted new native route, closed experiment, actual validation,
lost fresh4 outcome, local tickets/reviews and all source/history. Its actual
creation/upload receipts will necessarily be recorded after capture. No full
formal gate or chapter acceptance is claimed by that checkpoint.

The exact VFA2.1 source archive was recovered again at the recorded versioned
URL; all17chapter hashes and the license match the preserved inventory. Evidence:
validation/1030-vfa-source-recovery-current.json. Reference bodies/toolchains/caches
are excluded from source checkpoints as recorded by ADR0001 and SOURCE-RECOVERY.md;
exact URLs/hashes and the external-source availability limitation remain.

Capacity observations must distinguish available blocks from all unallocated
blocks. Zero available bytes did not establish write failure; actual041creation
passed, and a later observation showed over3GBunallocated. Neither counter
proves future capacity or task quota. No permissions/reservations were changed.
Completed finite cleanup records do not authorize repeated deletion. Returned
installer/checkpoint036/037 paths were retained after being observed again;
the writer/cause remains unknown. See the capacity/returned-file records.

Prior chronological state is retained in
[STATUS-history-before-native-j1-042.md](STATUS-history-before-native-j1-042.md)
and its linked histories. Prefer these current pointers over superseded progress
claims in those historical notes.
