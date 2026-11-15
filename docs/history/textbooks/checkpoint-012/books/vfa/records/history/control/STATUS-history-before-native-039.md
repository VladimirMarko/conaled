# Resume the VFA formalization

**The verified pinned Lean/Lake environment now works through the user-supplied
QEMU launcher. Whole-book work remains in progress; no chapter is accepted.**
The user requested alternatives to slow emulation. **A native executable-path
adapter is undergoing validation/review** under #1033. QEMU fresh3 was interrupted
through its owned tool session (observed exit130); no full check succeeded.

Read [REQUIREMENTS.md](REQUIREMENTS.md) with [AMENDMENTS.md](AMENDMENTS.md),
[tickets.json](tickets.json), and [AGENTS.md](../conaled/AGENTS.md) and its pointers.
The user explicitly permits omitting Nix/direnv when the correct tools are acquired
and explicitly supplied the QEMU execution route. All formal gates remain.
Prior current-state text is preserved in
[STATUS-history-through-checkpoint037.md](STATUS-history-through-checkpoint037.md)
and its linked histories; native startup failures and approval-policy rejection
are historical, not current blockers under the working guest execution route.

## Exact source and current setup

| Item | Identity/status |
| --- | --- |
| Formal candidate | `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec` |
| Fixed enclosing review base | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| Formal source | Clean; no source, dependency-pin, or proof-policy changes |
| Current chapter work | Preface#1001 and Perm#1002, awaiting validation/acceptance |
| Formal review | Round8 source assessments retained; ST-001 fixed; ST-002/SP-VAL-001 open; both overall axes Blocked |
| Reference | VFA2.1,2026-08-24; archive and all17 chapter identities reverified in #1030 |
| Lean | Actual bare and Lake-child invocations report4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake | Actual version5.0.0-src+eb6cafb, from the same official distribution |
| QEMU | Exact user-supplied executable; Ubuntu signature→index→package→binary authentication reproduced locally |
| Dependencies | All9 source checkouts at exact manifest revisions and clean |
| Kernel smoke | Two Init-only theorems compiled through each route; both report no axioms |
| New formal validation | Fresh3 interrupted; native alternative preparation active; no full success |

The complete [setup summary](validation/1032-qemu-environment/setup-summary.json)
links actual provenance, individual command results and effective environment.
[The user's supplied guide](environment-guides/user-supplied-lean-lake-qemu-guide.md)
is retained byte-for-byte, with its complete AppendixA adapter saved as
[tooling/pinned_toolchain.py](tooling/pinned_toolchain.py), SHA256
`a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47`.
The guide's unrelated ADWH checkpoint/branch/status is not part of this VFA work.

## Reproduce the working environment

Use [tooling/README.md](tooling/README.md), the VFA-specific equivalent instructions
requested by the user. It is self-contained with the adjacent complete adapter
and records exact acquisition URLs, hashes, extraction, source checkout procedure,
parent/child launch route, explicit cache execution and full validation sequence.
No other conversation or Library checkpoint is needed for its source instructions.

The helper derives the recovery root from its own location. In this workspace:

- Source: `/workspace/scratch/83865511e965/recovery/conaled-vfa-checkpoint-035-returned-archive-preservation/conaled`.
- Isolated candidate: the sibling `vfa-validation/`.
- Official distribution: `toolchains/lean-4.35.0-linux/` under that recovery root.
- QEMU: `toolchains/qemu-user/bin/qemu-x86_64-static`.
- Generated overlay: `toolchains/lean-4.35.0-host/`.

The official distribution was moved from its earlier scratch-root location into
this layout; its bytes remain unchanged. Historical paths in failed-run records
remain historical. Regenerate overlay wrappers after relocation; they contain
absolute paths. The helper verifies executable hashes and wrapper contents, not
an exhaustive rehash of every shared library. The verified distribution archive
and stable-input discipline remain relevant.

Wrap the **entire project command** with the helper. Do not put check.sh inside
lake env: that injects a LEAN selector rejected by incremental checking. Keep the
helper's default LEAN_NUM_THREADS=1 and fresh --jobs1. The shell launchers preserve
the checker's private fresh LEAN_PATH. QEMU requires no host mount, namespace,
ptrace facility, privileged install, or compiler patch in this route.

## Active formal operation and next action

Cache-tool build and explicit-QEMU cache retrieval both completed with actual
child, recorder and tool exits 0. The tool built 42 jobs; retrieval decompressed
all 9,031 requested files. The [completed setup preflight](validation/1032-qemu-environment/cache-completion-preflight.json)
records both results, a clean primary/isolated candidate, all nine clean exact
dependency revisions, and actual disk capacity. These setup results do not
establish project acceptance.

One QEMU fresh candidate check was launched under the unchanged accepted recorder:
[1002-candidate-3279bac-fresh3/run.json](validation/1002-candidate-3279bac-fresh3/run.json),
with sibling launch, heartbeat and direct child log. Tool session: **93349**.
Its tool returned130 after an explicit Ctrl-C to the live owned session. The
recorder run.json still says running because it did not flush a terminal record;
its last heartbeat preceded interruption. That stale record is not evidence of
a currently live process or a successful result. Child status/quiescence are
not independently established by quiet files; do not invent a raw child return.
See [interruption evidence](validation/1002-candidate-3279bac-fresh3-interruption.json).

The [session record](validation/1002-candidate-3279bac-fresh3-session.json) is
bookkeeping, not a terminal result. Inspect the actual recorder and tool outcome;
do not duplicate an actually active owned check. Every saved session/PID is
historical after a restore; archives do not establish process survival.

Native preparation must preserve exact runtime inputs and pass scoped review
before a new full attempt. Use a separate isolated candidate/output directory
if prior child quiescence cannot be established. No partial run is acceptance.
On a new actual success, preserve its fresh verification record and complete
direct log before separate guarded incremental validation replaces that record.
Historical fresh1/fresh2 terminal outcomes remain unknown. Continue the remaining
sequence below without treating setup, cache coverage, or a checkpoint as
chapter acceptance.

## Unchanged formal sequence

Apply the [existing acceptance checklist](validation/1002-acceptance-evidence-checklist.json)
with the accepted environment amendments. All commands run in vfa-validation/:

1. `python3 ../work-state/tooling/pinned_toolchain.py -- ./check.sh --fresh --jobs 1 --candidate HEAD`.
   Require a completed build and exhaustive audit, actual successful return,
   complete log and matching fresh verification record. Preserve that record
   before another validation replaces it.
2. Preserve any actual suspect artifacts before repairing them under the existing
   incident plan. Run separate guarded incremental validation:
   `python3 ../work-state/tooling/pinned_toolchain.py -- ./check.sh --candidate HEAD`.
   Retain classified invalidations, post-build integrity success, a new exhaustive
   audit and separate matching incremental record.
3. `python3 ../work-state/tooling/pinned_toolchain.py -- env LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit`.
   Only after success, run
   `python3 ../work-state/tooling/pinned_toolchain.py -- lake env python3 scripts/test-proof-audit.py`.
   Preserve all four expected outcomes. Unexpected prerequisite dependency rebuilds
   require recording and corresponding guarded evidence to be re-established.
4. Continue both independent review axes on the same exact candidate/base and
   retained finding history, with the user amendments and completed new evidence.
   Require supported dispositions of ST-002/SP-VAL-001. Setup/source clearance
   alone does not approve the formal candidate.
5. Immediately before acceptance, root runs
   `python3 ../work-state/tooling/pinned_toolchain.py -- ./check.sh --verify-candidate HEAD`.
6. Accept Preface then Perm and applicable cross-cutting tickets; immediately
   upload an acceptance checkpoint before implementing Sort.

The original mismatch origin may remain unresolved after supported candidate
mitigation. Do not describe mitigation as a proven cause or race-freedom result.
No old suspect project-cache payload was restored here, and no old cleanup
recipe authorizes deleting new paths. Cold-build missing outputs are normal.

## Scope and durability

All VFA chapters, optional/advanced mathematics, executable/resource obligations,
and Lean adaptations remain in scope. Chapter order is **Preface → Perm → Sort
→ Multiset → BagPerm → Selection → Merge → Maps → SearchTree → ADT → Extract →
Redblack → Trie → Priqueue → Binom → Decide → Color**. Shared preparations remain
indexed by#1018,#1019,#1020,#1023. Tickets and commits remain local; no GitHub writes.

Latest saved checkpoint is **038**,
`conaled-vfa-checkpoint-038-working-qemu-environment.tar.gz`, SHA-256
`a1ed387f58f0a49dd3033c24da727467ae7ae2e7d4d5425f5ed9e0541395ed9e`,
148,425,489 bytes, Library ID `libfile_2b94c4367a60819194280072b5301481`.
It includes the exact supplied guide/adapter and equivalent VFA instructions,
authentication inputs, source/history/tickets/reviews and setup evidence. Full
bundle, restore smoke and source/index/workflow stability checks passed.
Its creation/upload/local identity receipts are under validation/checkpoint038-*.
The upload and fresh3 launch occurred after its capture. Next identifier:039.

Source checkpoints exclude downloaded toolchains, generated overlays, compiled
caches and full research copies. Restore with RESTORE.md/restore.py, keep
work-state beside conaled, and reacquire dependencies with the included recipe.
Setup or checkpoint success does not establish chapter acceptance.
