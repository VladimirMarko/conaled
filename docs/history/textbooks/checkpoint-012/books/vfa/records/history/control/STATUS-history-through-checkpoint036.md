# Resume the VFA formalization

**Whole-book work remains in progress. No chapter is accepted. No formal validation
run has been launched in this recovered workspace.** The immediate blocker is the
required Nix development environment; this is local ticket **#1030**.

This entry point supersedes the current-state claims in checkpoint035. Its exact
previous STATUS is retained in
[STATUS-history-through-checkpoint035.md](STATUS-history-through-checkpoint035.md).
All historical logs, run records, reviews, requirements and amendments remain.
Read [REQUIREMENTS.md](REQUIREMENTS.md), [AMENDMENTS.md](AMENDMENTS.md),
[tickets.json](tickets.json), and the restored [AGENTS.md](../conaled/AGENTS.md)
with its README and workflow pointers before resuming.

## Verified recovery on 2026-11-03

| Item | Result |
| --- | --- |
| User-supplied checkpoint | 035, returned archive preservation |
| Input archive bytes | 146,256,772 |
| Input archive SHA-256 | `116f495c49cbb6e525ca88dc59164600e048febc602659882ebfe35e54bd5dbb` |
| Input manifest | All 753 entries verified |
| Restored source/index/status | All 1,574 recorded paths and captured state match |
| Git history | `git fsck --full` passed |
| Formal candidate | `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec` |
| Fixed enclosing review base | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| Working tree | Clean; no formal source or tooling pin changes |
| Current upstream AGENTS.md | Downloaded and byte-identical to restored copy |
| VFA source | Official versioned archive matches its pinned hash; all 17 chapter-file hashes and sizes match |

Detailed observations and their limits are in
[1030-recovery.json](validation/1030-recovery.json) and
[1030-environment.json](validation/1030-environment.json). The input attachment's
current Library identity is recorded from this conversation's routing metadata;
no original checkpoint035 upload receipt has been reconstructed.

The restored source root for this turn is
`/workspace/scratch/83865511e965/recovery/conaled-vfa-checkpoint-035-returned-archive-preservation/conaled`.
Use paths relative to the containing recovery directory on subsequent restores.

## Current environment blocker

Nix, Lean, Lake and direnv are not available on PATH in this exposed workspace.
No `/nix` store or installed Nix profile is visible. The official Nix 2.35.4 binary
archive was downloaded and verified against the recorded official SHA-256, but
**was not installed**.

The ordinary installation requires `/nix`, outside this session's writable roots.
The documented workspace-local chroot-store route requires user and mount
namespaces. The one harmless capability check returned exit 1:

```text
unshare: cannot open /proc/self/uid_map: No such file or directory
```

This describes the exposed sandbox, not the capabilities of the enclosing host.
No alternate namespace mechanism, permission bypass, system installation or
escalation was attempted. No approval rejection is being claimed. Merely
supplying a different Lean executable would not satisfy the retained requirement
to use the pinned Nix development environment.

**Resume in an environment with working Nix and permitted store access.** Keep
`flake.lock`, `lean-toolchain` and `lake-manifest.json` unchanged. The recovered
[environment.md](environment.md) records the pinned tooling; its old absolute
paths and old permission approval are historical, not current authorization.
The official installation and local-store documentation are linked in the
environment evidence record. This environmental prerequisite is the concrete
remaining action; further speculative source planning does not unblock it.

## Formal scope and retained review

Formalize all of Appel's *Verified Functional Algorithms*, including optional and
advanced mathematical exercises, executable/resource obligations, and explicit
Lean adaptations of Coq mechanics. Source algorithms need faithful definitions
or proved, explicitly scoped adapters. Preserve conaled's reusable contracts and
proof policy. Tickets, commits and reviews are local; no GitHub publication or
tracker writes are authorized.

Chapter sequence remains:

**Preface → Perm → Sort → Multiset → BagPerm → Selection → Merge → Maps →
SearchTree → ADT → Extract → Redblack → Trie → Priqueue → Binom → Decide → Color.**

Preface (#1001) and Perm (#1002) are the current candidate. Both original Round 8
source assessments cover its full 23-file change. ST-001 is fixed; **ST-002 and
SP-VAL-001 remain open**. Both overall review outcomes remain **Blocked**.
[The complete review record](reviews/1002-Perm.md) is unchanged. This recovery
assessment is not a new formal approval.

## Historical runs and incident evidence

Fresh1 and fresh2 retain **unknown terminal outcomes**. Their archived process IDs,
execution handles, heartbeats and running flags are historical observations. No
process is resumed by extracting an archive. No new formal checker was launched
in this workspace, and no old PID was signalled. Do not infer that the old host's
checker succeeded, failed, or remains active from this restore.

The recovered source has no `.lake` directory. No isolated validation checkout or
incident payload directory was included. There are therefore no restored project
artifacts to repair at those observed paths. Keep the prior mismatches, ENOSPC
failure and unknown causes in the record. Do not replay old cleanup or process
intervention recipes against a new filesystem. Source checkpoints deliberately
exclude caches; ordinary cold-build missing outputs are not a new incident.

The prior optional cache and incident archives are separate historical artifacts,
not attachments in this turn. Their preserved receipts are not evidence that their
payloads were restored or inspected here. If additional artifacts are later
provided, assess their identities and the existing preservation plan before
repairing any suspect output. The plan's old literal paths must not be used
unchanged. Unknown incident origin remains distinct from candidate mitigation.

## Resume and acceptance sequence

First establish the documented Nix shell and verify Lean 4.35.0. Create a clean
isolated candidate before obtaining dependency caches, so the source checkout
does not deliberately acquire a second complete cache. From `conaled/` in the
restored directory, with Nix configured:

```sh
nix develop --command lean --version
nix develop --command git worktree add --detach ../vfa-validation 3279bacaec4087cc0d6b7e6b8ae862109cb2dfec
cd ../vfa-validation
nix develop --command lake exe cache get
```

Check actual disk capacity and dependency identities. A successful cache fetch
alone is not a complete build. Root owns validation; keep the candidate and
writable outputs isolated. Use a new attempt directory with the accepted
[validation recorder](validation-recorder/README.md); do not overwrite fresh1 or
fresh2. Its previously accepted implementation is preserved unchanged.

Apply the existing [acceptance checklist](validation/1002-acceptance-evidence-checklist.json):

1. Complete **fresh** validation and exhaustive audit in the isolated candidate:
   `LEAN_NUM_THREADS=1 nix develop --command ./check.sh --fresh --jobs 1 --candidate HEAD`.
   Preserve its actual command result, complete direct log, and matching fresh
   `.lake/verification.json` before any later check replaces that record.
2. Apply the existing non-repairing preservation assessment to any actual suspect
   artifacts that become available. No such payload was restored here. Complete
   separate **guarded incremental** validation:
   `LEAN_NUM_THREADS=1 nix develop --command ./check.sh --candidate HEAD`.
   Retain classified invalidations, post-build integrity success, exhaustive audit,
   and its distinct matching incremental record. Fresh success alone does not
   discharge this separately retained gate.
3. Build the managed audit prerequisite:
   `LEAN_NUM_THREADS=1 LAKE_ARTIFACT_CACHE=false nix develop --command lake --no-cache --rehash build +ProofAudit`.
   Only after success, run:
   `LEAN_NUM_THREADS=1 nix develop --command lake env python3 scripts/test-proof-audit.py`.
   Retain the four required regression outcomes. If the prerequisite unexpectedly
   rebuilds project dependencies, record that and re-establish corresponding
   guarded evidence before the regression.
4. Continue the same independent Standards and Spec review loop against the fixed
   base and exact candidate, using the preserved finding history. Both axes must
   pass with supported dispositions of ST-002 and SP-VAL-001. Recovery mitigation
   does not establish the unknown incident's cause.
5. Immediately before acceptance, root runs:
   `nix develop --command ./check.sh --verify-candidate HEAD`.
   It must verify the same approved candidate and current successful record.
6. Accept Preface, then Perm, and applicable cross-cutting tickets; immediately
   create and upload an acceptance checkpoint. Begin Sort only afterward.

No gate is waived or replaced by this recovery work. No later chapter
implementation has started. Existing shared-contract drafts, inventories and
preparation remain indexed in tickets #1018, #1019, #1020 and #1023.

## Durability

The next complete source/history/tracking archive is named
`conaled-vfa-checkpoint-036-recovered-environment-handoff.tar.gz`.
Its creation and upload receipts are recorded after creation; its own containing
archive cannot include its final self-hash or post-upload receipt. Consult the
outer `metadata.json`, `MANIFEST.sha256`, and delivered receipt for its identity.
Use `RESTORE.md` and `restore.py`, and keep `work-state/` beside `conaled/`.

Historical checkpoint receipts, incident evidence descriptions, unknown outcomes,
and both formal review axes are retained. Source integrity and a successful
restore do not establish formal acceptance. The complete book remains unfinished.
