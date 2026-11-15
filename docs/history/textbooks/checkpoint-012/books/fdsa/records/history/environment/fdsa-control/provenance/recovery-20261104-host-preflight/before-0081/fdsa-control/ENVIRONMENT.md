# Current environment: supplied unified native kit

Updated 3 November 2026. The preferred recipe is the supplied immutable
`tooling/unified-native-kit-4.35.0`, kit version 1.0.0, Lean 4.35.0 and matching
Lake. Its README, pins, source, narrow native adapter, cache relink objects,
licenses, checksums, and recovery documentation are all included.

The original kit archive SHA-256 is
`45edfb844068f93b26ea5469572473f8c07e5a63e2bc294eed6de543cb3d5bf2`.
The delivered kit verified all 298 manifest entries in this recovered session.
Use `python3 fdsa-control/tooling/unified-native-kit-4.35.0/conaled_native.py verify`.

## Recreate the active candidate

After source recovery, from the workspace root:

```sh
git -C conaled worktree add --detach ../conaled-ch01-review 07e480f6ec9958d4975bb90151005b84f2907614
KIT="$PWD/fdsa-control/tooling/unified-native-kit-4.35.0"
STATE="$PWD/conaled-native-state"
PROJECT="$PWD/conaled-ch01-review"
python3 "$KIT/conaled_native.py" --state "$STATE" setup --project "$PROJECT"
```

The kit requires Linux x86-64/glibc >=2.30, Python >=3.11, cc, Git, curl, zstd,
and about 12–16 GiB free for a fresh active checkout. It downloads the exact
official archive (594,481,375 bytes, SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`),
restores the nine clean pinned Git dependencies and the official Mathlib cache,
and runs real proof and native executable smoke checks. State is regenerable
and must be outside the immutable kit and source. No project pins are changed.

On this constrained host it uses per-program glibc `--preload` only when the
qualified own-executable-path probes require the narrow adapter. This extra
runtime component is disclosed; official compiler/kernel binaries remain
unchanged. It is not a global `LD_PRELOAD` route.

## Formal gate and continuation

Adopting this launcher/profile requires one fresh baseline under the repository
README. After setup succeeds and with no source/dependency/compiler writers:

```sh
python3 "$KIT/conaled_native.py" --state "$STATE" run --project "$PROJECT" --threads 1 -- ./check.sh --candidate HEAD --fresh --jobs 1
```

Preserve the real exit, complete closed log and matching `.lake/verification.json`.
Fresh mode owns private temporary project outputs, reuses external dependencies,
and runs the source/coverage/compiler checks and exhaustive proof audit. It
neither reuses nor warms ordinary project artifacts. A fresh success is a valid
full candidate check; do not add a redundant incremental full run without a
concrete requirement. Both final independent Chapter 1 review axes must then
pass that same candidate. Immediately before acceptance run:

```sh
python3 "$KIT/conaled_native.py" --state "$STATE" run --project "$PROJECT" -- ./check.sh --verify-candidate HEAD
```

Only after all gates pass may the approved candidate be integrated and Chapter 2
activated. Keep all logs/results in `provenance/unified-native-20261103/` and
subsequent candidate-specific provenance directories. Missing results or partial
logs never prove success.

## Retained fallback

The previously tested native adapter and QEMU recipes remain intact in
`provenance/compact-checkpoints-20261103/ENVIRONMENT0069.md` and its referenced
files. They are historical fallback evidence; the unified kit is preferred.
The user's Nix exception, local-only ticketing, all mathematical requirements,
and all acceptance gates remain in force.

## Separate focused Chapter 2 development environment

The current conaled-ch02-top-down worktree (branch work/fdsa-ch02-values) uses
the same supplied native profile with its own project outputs and an independent
copy of .lake/packages. Root copied only dependency sources/caches with
cp -a --reflink=auto, verified all nine pinned HEADs/statuses and that a copied
artifact has a distinct inode. No writable project outputs are shared with the
owned full foundation check. Evidence: provenance/chapter02-values-private-
environment/private-cache.json. The copy is regenerable and excluded from
checkpoints. On recovery, either apply the kit's same exact setup recipe to the
secondary checkout, or make an independent copy from a completed stable primary
dependency setup, then verify its exact revisions before focused builds.
Focused module success is not a whole-candidate audit or acceptance record.
