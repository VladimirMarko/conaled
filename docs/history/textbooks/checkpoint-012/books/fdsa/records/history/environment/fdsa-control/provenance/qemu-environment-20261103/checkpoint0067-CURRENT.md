# Current continuation handoff

Updated 2026-11-03 after the user's explicit direct-toolchain authorization.
The full goal is all 27 FDSA chapters and Appendices A–C, chapter by chapter.
Use REQUEST.md for authority. Tickets remain local; no GitHub write is allowed.

## Current result and user exception

**No chapter, appendix or shared unit is accepted. Chapter 1 is active.**
No validator is running and no new project verification has been started.

**Nix is no longer required for this task.** The user explicitly allows acquiring
the correct program versions separately. The exact statement and scope are
`provenance/direct-environment-20261103/user-exception.md` and the appended
REQUEST.md section. This changes only the Nix-shell requirement. Preserve every
pin, proof/audit rule, candidate check, review axis and book obligation.
The generic Nix setup step in RECOVER.md must be read under this explicit
exception; a correct directly acquired toolchain is authorized.

The official Lean v4.35.0 Linux release was acquired and verified against its
publisher-provided SHA-256. All nine exact dependency source checkouts were
acquired and verified clean in the current isolated candidate. The released
Lake executable starts when given explicit paths to its own shipped libraries.

**Remaining blocker:** the stock Lean executable fails during startup because
this session does not expose `/proc/<its PID>/exe`. After fixing normal dynamic
library discovery, version, githash, print-prefix and a real import/compile
smoke check all exit 1 with `error: failed to locate application`. Exact source
inspection confirms this unconditional lookup happens before CLI parsing;
LEAN_SYSROOT does not replace it. No supported config/flag fallback was found.
No compiler patch or security-control change was selected.

Read `provenance/direct-environment-20261103/diagnosis.md` for actual outcomes,
primary-source explanation, provenance and precise limits. The earlier Nix
failures remain history; do not ask for a Nix waiver again.

## Preserved source and acceptance identities

- Main branch `work/fdsa-book`:
  `1aabd512284fe86254278ac631eda061d311050b`.
- Chapter 1 repaired candidate, branch `work/fdsa-basics-cost-models`:
  `07e480f6ec9958d4975bb90151005b84f2907614`.
- Original full-scope review base:
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Current isolated candidate: `../conaled-ch01-review`, detached and clean.
- Complete fourteen-path scope, original and frozen supplemental requirements,
  all draft refs and SPEC-001/002/003/V001 are retained unchanged.
- The original mathematical request bytes remain a prefix of REQUEST.md;
  only the explicit user environment exception has been appended.
- Initial Chapter 2 shared prefix remains exactly
  `c80eec92f5458eccfd1c34c8314d666c2a1e3847`.

The earlier repaired full attempts 1/2/3 have unknown terminal outcomes. Raw
running records, partial logs and every earlier actual failure remain historical.
No old PID, tool handle or agent name establishes current liveness. The new
smoke failures are environment results, not a new full attempt or source failure.

## Exact next sequence

1. Use an execution environment with normal own-process executable discovery
   (`/proc/<own PID>/exe` on Linux). Retain the official stock toolchain and pins.
   Nix is optional. If this archive is newly restored, reacquire the regenerable
   binaries/dependency caches; their current-workspace presence is not bundled.
2. Put official release bin first on PATH. Leave LEAN and LEAN_GITHASH unset.
   LEAN_SYSROOT can name its root; explicit release lib/lean and lib paths in
   LD_LIBRARY_PATH resolved loader discovery here. Record actual supporting
   tool versions. Require successful `lean --version`, `lean --githash`,
   `lean --print-prefix`, `lake --version` and a real import/compilation smoke
   check before treating the environment as ready.
3. In a clean isolated checkout of exact candidate 07e480f, acquire/verify all
   nine Git dependency revisions and run `lake exe cache get`. No cache command
   has yet run in this recovered workspace. Keep source and configuration stable.
4. Start one separately recorded full guarded check, conventionally repaired
   attempt 4: `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD` with both lean
   and lake resolving to the verified release. Use new log/metadata paths and
   preserve all earlier outcomes. Cold missing outputs are normal in recovery;
   new concrete integrity incidents retain the existing runbook.
5. Inspect the actual full exit/log/audit and matching verification JSON.
   After full success, resume the existing logical review loop with replacement
   coordinator and independent Standards/Spec axes as needed. Retain the full
   scope, prior finding IDs and both frozen requirement snapshots.
6. Both axes must pass the same immutable candidate. Immediately run unchanged
   `./check.sh --verify-candidate HEAD` before acceptance/integration. Save and
   expose the acceptance checkpoint immediately; only then advance Chapter 2
   under the retained integration workflow.
7. Continue through the entire book. Recovery or environment setup is never
   acceptance and does not reduce the formalization scope.

## Recovery records and artifacts

Checkpoint 0066 is saved as `libfile_83054193060881919d15cb2bdcab1d9b`; its
receipt/content inspection are now retained and enter checkpoint 0067.
The 0066 current handoff is preserved under direct-environment-20261103.

Checkpoint 0067 will preserve this user exception, exact release/dependency
acquisition provenance, failed smoke results and source-confirmed runtime
blocker, alongside all original source/history/control. Regenerable compiler
binaries, dependency caches and copyrighted book text remain excluded.
Its own creation/save receipt postdates the archive in the usual way.


## Checkpoint 0067 saved and inspected

conaled-fdsa-0067-direct-toolchain-recovery.tar.gz is saved as libfile_e4e5f5a888608191a42f300e3ac95d68.
Size 75223020 bytes; SHA-256 3b87c09192605c123a162bf4a9bdfb380936e0be3d1737cbb10c9c53688218f6.
The closed-archive content check passed. Its own receipt and inspection
postdate the archive and are retained for the next checkpoint.
