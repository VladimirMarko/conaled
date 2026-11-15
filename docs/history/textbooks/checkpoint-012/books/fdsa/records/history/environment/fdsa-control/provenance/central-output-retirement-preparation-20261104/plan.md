# Central generated-output retirement — bounded preparation

Recorded 4 November 2026. **Planning only: no cleanup, cache execution, compiler action, process polling or source/ref/configuration edit was performed.** The author did not traverse any live generated output tree. This plan supports root's conditional resource-retirement decision; it creates no new acceptance or user-approval gate.

## Decision and exact boundary

If the specified terminal, review-durability and checkpoint0100 conditions are met, the nine named central generated build roots may be retired as a single unusable output set. **Mark that state before the first payload mutation, and retain it after any partial failure.** Zero-length `.olean`, `.ilean`, object, hash and trace files are not valid reusable compiler outputs. An old candidate-success record cannot supply current output validity after retirement; preserve it as historical evidence.

The recorded inventory is `../checkpoint0099-preparation/central-output-retirement-planning-inventory.json`, observed **2026-11-04T11:20:43.293013+00:00**, 3,634 bytes / 83 lines, SHA-256 `68b1e58fa74500f9c7f15687d8edd5728116a6cd36106ca9bf05677598deb001`. It predates completion of focused/type work. Its counts are a planning baseline, not a current file-identity certificate.

All paths in this table are relative to the exact central checkout:

`/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch02-top-down/`

| Literal allowed generated root | Recorded files | Apparent bytes | Allocated bytes |
| --- | ---: | ---: | ---: |
| `.lake/build` | 993 | 169,024,513 | 171,724,800 |
| `.lake/packages/mathlib/.lake/build` | 129,375 | 6,583,178,446 | 7,001,104,384 |
| `.lake/packages/plausible/.lake/build` | 195 | 13,066,131 | 13,705,216 |
| `.lake/packages/LeanSearchClient/.lake/build` | 60 | 4,912,859 | 5,107,712 |
| `.lake/packages/importGraph/.lake/build` | 525 | 33,366,439 | 35,078,144 |
| `.lake/packages/proofwidgets/.lake/build` | 195 | 20,102,276 | 20,717,568 |
| `.lake/packages/aesop/.lake/build` | 1,980 | 130,994,252 | 137,449,472 |
| `.lake/packages/Qq/.lake/build` | 210 | 21,008,898 | 21,684,224 |
| `.lake/packages/batteries/.lake/build` | 2,925 | 140,506,590 | 150,294,528 |

Total: **136,458 recorded regular single-link files**, **7,116,160,404 apparent bytes**, **7,556,866,048 allocated bytes (7.03788 GiB)**. These are possible payload savings, not a promised change in filesystem availability. The recorded available space was 4,398,190,592 bytes at that inventory's timestamp. No current space measurement or explanation of filesystem-wide decline was attempted in this planning task.

The companion `guard-manifest.json` lists all nine full absolute paths. Select those exact roots, not `.lake`, `.lake/packages`, the entire central checkout, a `*/.lake/build` glob, or a parent directory. Cli is absent from the nine-root inventory and is not added to the action. Root paths are pairwise disjoint.

**Preserve:** all source and dependency checkouts and their Git data; manifests/pins; the complete native state, compiler/profile/cache helper and compressed `.ltar` archive store; every other worktree; accepted/history refs; checkpoint archives; baseline partials; and all actual command logs, printed-type outputs, audit/verification records and review evidence. In particular the entire primary F tree `BASE/conaled-ch01-review` is outside the mutation scope. Never transplant its outputs into central or vice versa.

## Conditions that must actually be bound

1. All central compiler, cache, focused-build and type-inspection commands have closed, with their real terminal outcomes and complete available logs secured. Root retains exclusive ownership of central for the whole retirement interval. A project advisory lock alone cannot establish this: the kit explicitly excludes other launch paths from its lock guarantee.
2. Both independent XP01 source/type assessments and matching actual inputs/outputs are durable. This means completion and preservation of those assessments, not an invented requirement that the still-blocked whole-unit acceptance pass first. The full eventual acceptance gates remain unchanged.
3. A final preflight is recorded after that quiescence. It inventories the exact roots, establishes the no-follow/private-file conditions below, and reconciles all actual command-evidence locations. If any unique run log, report, result, verification record or other nonregenerable content resides under an allowed root, preserve its exact bytes in control before checkpoint0100 capture. Generated cache `.trace`/`.setup.json` metadata is part of the retired payload set; secured validation evidence is not.
4. Checkpoint0100 is fully verified, uploaded and exposed with the matching source/review/evidence and final preflight. Root binds the exact archive size/SHA, delivery identity, final central commit and assessment receipts in the new execution record. This planning manifest deliberately leaves those future bindings unset.
5. Immediately before mutation, repeat the no-follow inventory and verify that it matches the quiescent preflight. Stop on a changed file set or metadata identity, unexpected link/special file, unique unsaved evidence, unavailable persistence logging, or a renewed central writer. Those are concrete trigger failures; do not silently broaden paths or discard the condition.

At assignment, root reported focused4/session74832 running. Root subsequently reported focused4 and actual20 closed with exit 0, matching actual input identities and complete secured records; both axes were reading the 20 types. Root measured 2,679,386,112 available bytes at 11:31:28 UTC and is preparing the final no-follow preflight before checkpoint0100 capture. These are attributed coordinator updates; this author did not poll commands or inspect live outputs. The final review/checkpoint/execution bindings remain to be supplied, so no cleanup condition is certified by this document.

## Protective action outline

Use one bounded root-owned operation, with all records under a **new** `fdsa-control/provenance/central-output-retirement-.../` directory outside the nine roots. No new general-purpose cleanup utility is needed.

- Open the trusted workspace/base and each literal path component using descriptor-relative `os.open(..., O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC)`. Check directory metadata before descending. A final-component-only `O_NOFOLLOW` check is insufficient if an ancestor is a symlink. Do not resolve/follow links first and then assume the resulting path is safe.
- Enumerate recursively without following links, using directory descriptors and `lstat`/`stat(..., follow_symlinks=False)`. Accept only real directories and regular files with `st_nlink == 1`. Reject symlink files/directories, multiply linked files, sockets/FIFOs/devices, changed root identities and unexpected filesystem boundaries. Compare any existing private-tree identity evidence; no F traversal or mutation is required. Do not use permissions changes to push past a failed guard.
- Record root `(device,inode)` identities, file counts, apparent/allocated bytes and a deterministic digest of the sorted relative-path/metadata stream. The metadata includes kind, device, inode, link count, size, modification and change times. Keep the preflight compact with per-root digests and counts; preserve exact details for any failure. A historical count is not a substitute for this new preflight.
- Record `retiring_unusable` for the whole central output set **before** mutation. Recheck all conditions. For each preflight-approved regular file, open it relative to its already checked parent descriptor with `O_WRONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC`, **without `O_TRUNC` or `O_CREAT`**. Check `fstat` identity/type/link count against the just-read entry before `ftruncate(fd, 0)`, then check zero length and close it. This avoids truncating through a changed symlink or newly shared inode before the check.
- Clear every selected generated payload, including `.trace` files; do not clear just large `.olean` files. Retain directory structure and filenames. Update a compact progress record at each root or bounded batch, including completed counts, original payload/block totals and last completed path. Records must retain actual success/failure and any exception; a partial operation leaves **all** nine roots retired/unusable.

The executable primitive sequence is:

```text
require actual terminal/review/checkpoint bindings and exclusive central ownership
require fresh no-follow preflight matches its checkpointed identity
record whole set = retiring_unusable
for each of the nine literal roots:
    open/verify every directory component without following links
    for each generated regular file from a no-follow walk:
        require current metadata matches the checked entry and link count is one
        open leaf relative to parent fd, without creation or truncation flags
        require fstat still matches regular-single-link identity
        ftruncate(fd, 0); require fstat(fd).size == 0; close fd
        record bounded progress
record actual terminal result; whole set remains retired_unusable
```

This is an action outline, not a cleanup execution. It does not make the historical inventory self-validating or authorize this subagent to perform retirement.

## Separate persistence validation

After the clearing command has actually closed, use a **new command** to re-enumerate only the nine roots with the same no-follow rules. Record every root's existence/identity, regular-file count, nonzero-file count, total logical and allocated file bytes, and any new/changed entries. A successful retirement claim needs persistent zero regular-file payload bytes (or verified absence) and no unexplained new nonzero payload. Record residual allocated blocks honestly. Directory entries may remain; do not claim the trees were removed or regard a residual path as a new empty recovery destination.

Also record source HEAD/status and exact protected refs/pins as read-only invariants, plus filesystem available/raw-free figures. Do not attribute the global space delta entirely to this action: the independently enumerated retired-file blocks and whole-filesystem availability are distinct observations. If any payload reappears, record the exact difference and stop; do not start repeated blind deletion or hydration.

The existing task's `redundant-download-payload-clear-result.json` and separate `redundant-download-payload-clear-persistence.json` document successful zero-payload persistence on seven known files. They do not prove that a larger future operation will succeed. Prior observed unreliable deletion is why this proposal describes explicit payload retirement and independent persistence checks, not an assumed recursive deletion success.

## Later reuse and applicable gates

Keep central marked retired/unusable until its required outputs have been regenerated from the exact preserved sources and pins through the unchanged qualified environment. Retaining source history and recorded semantic/type evidence does not make cleared artifacts usable. Do not satisfy recovery by copying F outputs, widening the launcher, changing pins, lowering space guards, or accepting a partial dependency cache as complete.

There is a specific pinned-cache reason to include generated traces in retirement. `Cache/IO.lean` lines 425–474 parses a trace's JSON `depHash` and skips decompression when it matches the `.ltar` header. If a valid trace survived while its corresponding binary was cleared, that check could still permit skipping. An empty trace cannot parse and `needsDecompression` returns true. The normal get/unpack path then selects available matching archives for decompression (lines 498–529). This is source-supported selection behavior, not proof that a future extraction completed or all required artifacts were restored.

The unchanged native kit `conaled_native.py` lines 355–389 verifies exact private dependencies, uses the dedicated cache helper and enforces its space guard. It exposes only ordinary `get` and `unpack` at lines 518–528; do **not** invent `get!`, `unpack!` or bypass the supported helper. The supported broad recovery command, when central is again needed and actual resources suffice, is:

```sh
python3 "$KIT/conaled_native.py" --state "$STATE" cache --project "$PROJECT"
```

For this command, PROJECT must be the same exact central checkout and KIT/STATE the preserved qualified paths. Offline `cache --project "$PROJECT" --offline` restores available local archives only and does not certify completeness. Capture real exit/log/coverage, ensure required dependency/import coverage, regenerate required project outputs, and run the then-applicable project gates before treating central as reusable. A cache command alone does not restore an earlier acceptance record's validity.

With near-empty dependency outputs, full hydration's guard again requests approximately 8 GiB additional available space; it must not be bypassed. The 7.04 GiB planning figure does not guarantee that resource condition will hold later, especially while F remains active. Do not immediately refill central merely to undo the resource-saving purpose of retirement.

“Fresh exact hydration” here means regenerating the required cache/output payloads from exact inputs. It is distinct from the repository's `check.sh --fresh` acceptance mode. Follow README's real triggers: changed build tooling/toolchain/dependency configuration or suspected stale outputs require `--fresh`. This plan is neither a fresh-mode waiver nor an automatic extra fresh-mode command; root must apply that rule to the actual regenerated state. Any unresolved stale/residual-output uncertainty must be investigated and covered by the fresh rule. F's untouched accepted baseline and live normal-candidate validation are not retroactively invalidated. Full candidate checks/audits, independent final axes and immediate verification remain mandatory in their existing scopes.

## Evidence and honest read boundary

Complete reads: the 83-line inventory, kit `docs/RECOVERY.md`, and the two preserved redundant-download clearing/persistence records. Bounded source reads: kit cache implementation/dispatch and README cache sections; repository README build/fresh/integrity provisions; pinned Mathlib `Cache/IO.lean` lines 425–535 and `Cache/Main.lean` lines 250–300. No cache command, cleanup primitive, process inspection or live-output traversal was executed. Exact document hashes and the source-read ranges are in the companion manifest. This plan does not revise any source, existing control, finding record or earlier planning report.
