# Resume the VFA formalization

**The whole book remains unfinished. No chapter is accepted.** The user now
permits direct acquisition of the correct required programs without Nix/direnv.
The exact official Lean distribution has been acquired, but the compiler cannot
initialize in this sandbox because `/proc/<its-pid>/exe` is unavailable. Local
**#1031** owns this concrete runtime blocker. No fresh3 or other new formal
validation was launched.

Read [REQUIREMENTS.md](REQUIREMENTS.md) together with [AMENDMENTS.md](AMENDMENTS.md),
[tickets.json](tickets.json), and the restored [AGENTS.md](../conaled/AGENTS.md)
with its pointers. The user's direct-toolchain amendment supersedes only the
Nix/direnv requirement. The prior entry points are preserved verbatim in
[STATUS-history-through-checkpoint036.md](STATUS-history-through-checkpoint036.md)
and [STATUS-history-through-checkpoint035.md](STATUS-history-through-checkpoint035.md).

## Current source and requirements

| Item | Identity or status |
| --- | --- |
| Formal candidate | `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec` |
| Fixed enclosing review base | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| Formal working tree | Clean; no implementation or pin changes |
| Current chapter work | Preface (#1001) and Perm (#1002), acceptance pending |
| Source review | Round8 retained; ST-001 fixed; ST-002 and SP-VAL-001 open |
| Overall formal reviews | Standards Blocked; Spec Blocked |
| Source book | VFA2.1, 2026-08-24; archive and all17 chapter identities reverified in recovery#1030 |
| Environment exception | Explicit user authorization in [specs/1031-direct-toolchain-amendment.md](specs/1031-direct-toolchain-amendment.md) |

The full objective includes all chapters, optional and advanced mathematical
exercises, executable/resource obligations and explicit Lean adaptations of
Coq mechanics. Source algorithms require faithful definitions or proved adapters.
Retain conaled's reusable contracts and proof policy. All tracking and commits
remain local; no GitHub publication or tracker writes are authorized.

Chapter order remains **Preface → Perm → Sort → Multiset → BagPerm → Selection
→ Merge → Maps → SearchTree → ADT → Extract → Redblack → Trie → Priqueue → Binom
→ Decide → Color**. Do not implement Sort before Preface and Perm acceptance.
Existing shared preparation remains indexed by #1018, #1019, #1020 and #1023.

## Acquired direct toolchain and actual blocker

[1031-direct-toolchain.json](validation/1031-direct-toolchain.json) records the
release provenance, distribution/runtime hashes, individual smoke results,
source diagnosis and policy rejection. The official
[Lean4.35.0 release](https://github.com/leanprover/lean4/releases/tag/v4.35.0)
provided `lean-4.35.0-linux.tar.zst`, 594,481,375 bytes, SHA-256:

`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`

The downloaded asset matched its official API digest before safe extraction.
The distribution is unchanged. It is available in this current workspace at
`/workspace/scratch/83865511e965/toolchains/lean-4.35.0-linux`.

The first smoke invocation could not resolve the distribution's shared libraries.
Supplying its own `lib` and `lib/lean` through `LD_LIBRARY_PATH` resolved that
loader error. With those paths:

- `lake --version` exits0 and reports `5.0.0-src+eb6cafb (Lean version4.35.0)`.
- `lean --version` and `lean --print-prefix` each exit1 with
  `error: failed to locate application`, including with the correct `LEAN_SYSROOT`.
- No successful Lean startup or compiler-version invocation is being claimed.

The exact pinned native source explains the failure: Lean initializes search
paths before parsing command-line options; its internal `getBuildDir` uses
`IO.appDir`, and Linux `lean_io_app_path` reads `/proc/<getpid()>/exe` with no
environment or argv fallback. `LEAN_SYSROOT` affects external `findSysroot` and
Lake detection, not this internal startup path. This is a concrete process-path
requirement, not a remaining Nix requirement.

A read-only invocation of the same pinned compiler outside the sandbox was
rejected before execution because the current approval policy disables sandbox
escalation. No outside-sandbox process ran. No binary patch, custom path shim,
mount, access-control change or alternate bypass was attempted. This observation
concerns the exposed execution surface; enclosing-host capabilities are unknown.

**Resume with normal read access to the executing compiler's `/proc/<pid>/exe`.**
The user's authorization to omit Nix is already recorded. Further permutations of
Lean flags or `LEAN_SYSROOT` do not solve the established startup path.

Python3.12.14 is available and satisfies the integrity helper's Python3.11+
`tomllib` requirement. Git2.51.1 and curl8.5.0 are available. The direct environment
is not claimed to reproduce all historical Nix package bytes. The main acceptance
chain does not invoke elan; the separate `test-check.py` suite has an elan-specific
case if that suite is later needed.

## Isolated checkout and historical evidence

A clean isolated checkout was created at
`/workspace/scratch/83865511e965/recovery/conaled-vfa-checkpoint-035-returned-archive-preservation/vfa-validation`
with the exact candidate above. Its dependency cache has not been fetched and
there is no new formal run. On subsequent archive restore, recreate that worktree
from the preserved candidate; do not assume the machine-specific path exists.

Fresh1/fresh2 terminal outcomes remain unknown. Archived process IDs, execution
handles, running flags and heartbeats are historical. Original records are
unchanged. Do not infer old-host process state from a restore or signal old PIDs.
No suspect project-cache payload was included in the source checkpoint. Old
cleanup decisions and literal incident paths do not authorize actions on new
paths. Missing cold-build artifacts are not new unexplained invalidations.
The original mismatch origin remains unresolved. Existing incident descriptions
and separate-archive receipts are preserved without claiming their payloads were
restored here.

## Direct resume sequence

After process-path access is available, use the verified distribution's `bin`
first on `PATH`; use its own library directories if explicit library paths are
needed. Use a task-owned writable `TMPDIR`, `LEAN_NUM_THREADS=1`, and
`LAKE_ARTIFACT_CACHE=false`. Keep `LEAN` and `LEAN_PATH` unset; do not replace
project pins or import paths. Smoke-check actual Lean and Lake versions first.
Record the actual environment and exact results.

Create or verify the clean isolated checkout before fetching dependencies. Run
`lake exe cache get` there, then verify all nine clean Git dependency checkouts
against `lake-manifest.json`. Check actual capacity. A successful cache-download
exit alone is not complete compilation.

Use the unchanged accepted [validation recorder](validation-recorder/README.md)
with a new `1002-candidate-3279bac-fresh3` attempt directory and the direct checker
argv. The recorder has no Nix or /proc dependency in its inspected source; its
ordinary process syscalls still require an actual successful launch. Do not
modify its failure behavior or overwrite historical attempts.

Apply the existing [acceptance checklist](validation/1002-acceptance-evidence-checklist.json),
with only the Nix wrapper omitted under the user amendment:

1. `LEAN_NUM_THREADS=1 ./check.sh --fresh --jobs 1 --candidate HEAD`.
   Require complete build and exhaustive audit; preserve the actual return,
   complete log and matching fresh verification record.
2. Preserve any actual suspect artifacts before repairing them, as required by
   the existing incident plan. Run separate guarded incremental validation:
   `LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`. Retain classified invalidations,
   post-build integrity success, exhaustive audit and the separate incremental
   record. A later validation removes the previous current record, so preserve
   the fresh evidence first.
3. `LEAN_NUM_THREADS=1 LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit`.
   Only after success, run
   `LEAN_NUM_THREADS=1 lake env python3 scripts/test-proof-audit.py`.
   Retain all four expected regression outcomes. Unexpected managed prerequisite
   dependency rebuilds require recording and corresponding guarded evidence to
   be re-established before the regression.
4. Continue both independent review axes against the exact candidate, original
   base and retained finding history, supplying the accepted user amendment.
   Require supported dispositions of ST-002/SP-VAL-001. Nix itself is no longer
   mandatory, but missing formal validation still prevents approval.
5. Immediately before acceptance, root runs
   `./check.sh --verify-candidate HEAD` and preserves its actual success.
6. Accept Preface then Perm and applicable cross-cutting tickets; create and upload
   an acceptance checkpoint immediately, then begin Sort.

No mathematical/proof gate or chapter-order requirement is waived. Candidate
mitigation must not be described as a proven cause of the historical incident.

## Durability

Latest already saved complete checkpoint before this handoff is036, whose
creation/upload records are retained in `validation/checkpoint036-*` and
`checkpoints.json`. The new source/history/tracking checkpoint identifier for
this direct-toolchain handoff is **037**:
`conaled-vfa-checkpoint-037-direct-toolchain-runtime-handoff.tar.gz`.
Its creation and upload results are recorded after capture; a containing archive
cannot include its own final self-hash or later upload receipt. Follow its outer
metadata and the delivered receipt. Subsequent new checkpoint numbers start at038.

Use RESTORE.md/restore.py and keep work-state beside conaled. Source checkpoints
exclude the reproducible downloaded toolchain and dependency caches; this handoff
preserves exact acquisition URLs, hashes and execution evidence. Recovery and
checkpoint success do not constitute chapter acceptance.
