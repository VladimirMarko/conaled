# Current environment: supplied unified native kit

Updated 4 November 2026. The preferred recipe is the supplied immutable
`tooling/unified-native-kit-4.35.0`, kit version 1.0.0, Lean 4.35.0 and matching
Lake. Its README, pins, source, narrow native adapter, cache relink objects,
licenses, checksums, and recovery documentation are all included.

The original kit archive SHA-256 is
`45edfb844068f93b26ea5469572473f8c07e5a63e2bc294eed6de543cb3d5bf2`.
Historical setup on 3 November verified all 298 manifest entries.
The reset 4 November host independently rechecked those 298 entries and
successfully restored and installed the environment. The fourth recorded setup
attempt exited 0 at 03:53:20 UTC; preceding HTTP429 failures are retained.
Use `python3 fdsa-control/tooling/unified-native-kit-4.35.0/conaled_native.py verify`.

## Restore the exact pending candidate

Updated recovery guidance, 4 November 2026. The 0080/0081 recovery script already
recreates conaled-ch01-review on work/fdsa-foundation-integration at
f17cc6b1a2bf44215b16202ed0fcee2b5c130761. Do not add another worktree at the old
Chapter 1 HEAD or reset the restored foundation candidate. The accepted main
branch remains 07e480f6ec9958d4975bb90151005b84f2907614.

Check actual available storage before source recovery or setup. The official
compiler installer requires at least 5 GiB available at STATE. Plan 12–16 GiB
available for a fresh active checkout, more for separate caches. On the
earlier 4 November host preflight the workspace had 0 available bytes, so no
installation was attempted then. The subsequent reset supplied about 59.54 GiB
available; restoration and native setup succeeded without bypassing any guard.
Setup completed with about 34.9 GiB available. Recheck before extra cache copies.

After supplied-script recovery succeeds, from the restored workspace root:

```sh
set -eu
test "$(git -C conaled rev-parse HEAD)" = 07e480f6ec9958d4975bb90151005b84f2907614
test "$(git -C conaled-ch01-review rev-parse HEAD)" = f17cc6b1a2bf44215b16202ed0fcee2b5c130761
test -z "$(git -C conaled-ch01-review status --porcelain=v1 --untracked-files=all)"
KIT="$PWD/fdsa-control/tooling/unified-native-kit-4.35.0"
STATE="$PWD/conaled-native-state"
PROJECT="$PWD/conaled-ch01-review"
python3 "$KIT/conaled_native.py" verify
python3 "$KIT/conaled_native.py" --state "$STATE" setup --project "$PROJECT"
```

The unchanged kit requires Linux x86-64/glibc >=2.30, Python >=3.11, cc, Git,
curl and zstd. It acquires the exact official archive (594,481,375 bytes,
SHA-256 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d),
restores the nine pinned clean Git dependencies and official Mathlib cache,
and runs the real proof/native smoke checks. Keep STATE outside source/kit.
No project pin, compiler/kernel binary or execution profile is silently changed.

Where qualification requires it, the disclosed narrow adapter uses per-program
glibc --preload. It is not global LD_PRELOAD. Follow the kit's actual probes and
checks; preserve its command records and actual exits. Start at one Lean thread;
CPU count alone is not evidence for safe higher concurrency.

## Applicable full foundation gate

Chapter 1 already supplies the successful full fresh native-kit baseline.
Apply the repository README's actual normal-versus-fresh triggers. Mere loss of
regenerable outputs or restoration on a new workspace does not itself require
another expensive fresh baseline. A relevant changed runtime/toolchain/build or
dependency input still requires the appropriate validation. Do not manufacture
a pass from setup smokes or focused compilation.

After exact setup, with exclusive ownership of stable candidate inputs/outputs,
launch a newly named recorded attempt; never resume/poll historical session7319:

```sh
python3 "$KIT/conaled_native.py" --state "$STATE" run --project "$PROJECT" --threads 1 -- ./check.sh --candidate HEAD
```

Preserve the actual terminal exit, complete closed log, exhaustive proof audit,
native-kit command record and matching .lake/verification.json in a new
candidate-specific provenance directory (not attempt1). Missing terminal
evidence leaves the outcome unknown. The accepted C1 verification file is not
a foundation result. The ordinary checker owns its source-policy, coverage,
input/output integrity, immutable-candidate and exhaustive axiom checks.

Continue reviews/shared-foundations-round1.md and its independent Standards and
Spec axes. Their complete source analyses stand for unchanged f17cc6b; both
overall outcomes remain Blocked until the actual full terminal evidence is
assessed. Source changes require the same full-scope review continuation.
After both axes and all gates pass, immediately before the exact local
fast-forward run:

```sh
python3 "$KIT/conaled_native.py" --state "$STATE" run --project "$PROJECT" -- ./check.sh --verify-candidate HEAD
```

Confirm the verified commit is the fully approved candidate, then integrate,
update local coverage/tickets and save/upload an acceptance checkpoint. No
Github write/push is authorized. Chapter 1 acceptance is not reopened by loss
of the workspace. The old attempt1 remains historical with unknown outcome.

## Retained fallback

The previously tested native adapter and QEMU recipes remain intact in
`provenance/compact-checkpoints-20261103/ENVIRONMENT0069.md` and its referenced
files. They are historical fallback evidence; the unified kit is preferred.
The user's Nix exception, local-only ticketing, all mathematical requirements,
and all acceptance gates remain in force.

## Historical separate focused Chapter 2 development environment

At checkpoint0080, conaled-ch02-top-down (branch work/fdsa-ch02-values) used
the supplied native profile with its own project outputs and an independent
copy of .lake/packages. Root copied only dependency sources/caches with
cp -a --reflink=auto, verified the nine pinned HEADs/statuses and a distinct
artifact inode. Those private outputs isolated development from the then-active
foundation check. Evidence remains in provenance/chapter02-values-private-
environment/private-cache.json. Copies are regenerable and excluded from
checkpoints. None of those historical copies or builders survives as a known
active environment/process in this recovered session. New exact primary setup
has now passed; no secondary writable dependency copy exists at checkpoint0082.

After sufficient storage and source recovery, either apply the unchanged kit's
exact setup recipe to the secondary checkout or make an independent copy from
a completed stable primary dependency setup, then verify exact revisions and
private writable outputs before focused builds. Plan the additional storage.
Focused module success is not a whole-candidate audit or acceptance record.
