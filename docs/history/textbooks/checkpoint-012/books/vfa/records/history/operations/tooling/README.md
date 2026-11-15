# VFA: reproduce the pinned Lean/Lake execution environment

This recipe applies to VFA candidate `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`
and fixed review base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Read [STATUS](../STATUS.md), [requirements](../REQUIREMENTS.md), and
[amendments](../AMENDMENTS.md). The user permits the correct tools without Nix
and supplied this QEMU route. All formal gates remain. No GitHub writes are authorized.

The exact adapter is [pinned_toolchain.py](pinned_toolchain.py), SHA-256
`a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47`.
Its complete source is preserved beside this README. The
[supplied guide](../environment-guides/user-supplied-lean-lake-qemu-guide.md)
has SHA-256 `ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1`.
This VFA recipe has no dependency on that guide's other project/checkpoint.

## Layout and prerequisites

Use x86-64 Linux with glibc, Python 3.11+ (`tomllib`), Git, curl, GNU tar,
zstd, `sha256sum`, and `dpkg-deb`. Record actual tool versions. From the recovery
directory containing `conaled/` and `work-state/`, use Bash:

```sh
set -euo pipefail
vfa_root="$(pwd -P)"
```

The helper derives this root from its own `work-state/tooling/` location.
Keep the official distribution at `toolchains/lean-4.35.0-linux`, QEMU at
`toolchains/qemu-user/bin/qemu-x86_64-static`, and the isolated candidate at
`vfa-validation/`. The generated overlay is `toolchains/lean-4.35.0-host`.
Runtime state and dependency downloads stay in root-local directories selected
by the adapter. Reuse verified existing files; do not extract over unknown content.

## Acquire unchanged distributions

The [official release](https://github.com/leanprover/lean4/releases/tag/v4.35.0)
and [retained metadata](../validation/1031-official-lean-release.json) identify
the 594,481,375-byte Lean asset. These commands reacquire it after workspace loss:

```sh
mkdir -p toolchains/downloads
curl --fail --location \
  https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst \
  --output toolchains/downloads/lean-4.35.0-linux.tar.zst
sha256sum --check <<'SHA256'
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  toolchains/downloads/lean-4.35.0-linux.tar.zst
SHA256
tar --no-same-owner --zstd -xf toolchains/downloads/lean-4.35.0-linux.tar.zst -C toolchains
```

Extract only the needed QEMU executable and its copyright from Ubuntu's exact
`qemu-user-static` package, version `1:8.2.2+ds-0ubuntu1.18`; do not install it:

```sh
mkdir -p toolchains/qemu-user/extract toolchains/qemu-user/bin
curl --fail --location \
  https://archive.ubuntu.com/ubuntu/pool/universe/q/qemu/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb \
  --output toolchains/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb
sha256sum --check <<'SHA256'
5bb397f66063efa349f6fd5cb3b68cd96f29edd0994e4ba5115cf0859a716bf0  toolchains/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb
SHA256
dpkg-deb --fsys-tarfile toolchains/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb \
  | tar --no-same-owner -x -C toolchains/qemu-user/extract \
      ./usr/bin/qemu-x86_64-static ./usr/share/doc/qemu-user-static/copyright
cp toolchains/qemu-user/extract/usr/bin/qemu-x86_64-static toolchains/qemu-user/bin/
cp toolchains/qemu-user/extract/usr/share/doc/qemu-user-static/copyright toolchains/qemu-user/
sha256sum --check <<'SHA256'
90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0  toolchains/qemu-user/bin/qemu-x86_64-static
a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47  work-state/tooling/pinned_toolchain.py
SHA256
```

[Current acquisition evidence](../validation/1032-qemu-environment/qemu-acquisition.json)
binds the locally verified Ubuntu signature, index, package and executable.
Its sibling `ubuntu-InRelease`, `ubuntu-Packages.xz`, and
`ubuntu-archive-keyring.gpg` preserve verification inputs. Original trust came
from the host's Ubuntu keyring; the saved copy is evidence, not a new trust root.
Fresh metadata must be authenticated against its own signed release; the live
`noble-updates` index need not retain the recorded hash.

## Preserve the candidate and acquire exact dependency sources

Create the isolated worktree only if absent:

```sh
if [ ! -e vfa-validation ]; then
  git -C conaled worktree add --detach ../vfa-validation 3279bacaec4087cc0d6b7e6b8ae862109cb2dfec
fi
cd "$vfa_root/vfa-validation"
python3 - <<'PY'
import json, subprocess
from pathlib import Path
repo = Path.cwd()
def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()
assert git(repo, 'rev-parse', 'HEAD') == '3279bacaec4087cc0d6b7e6b8ae862109cb2dfec'
assert not git(repo, 'status', '--porcelain=v1', '--untracked-files=all')
assert (repo / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
manifest = json.loads((repo / 'lake-manifest.json').read_text())
assert len(manifest['packages']) == 9
assert next(p for p in manifest['packages'] if p['name'] == 'mathlib')['rev'] == '56a005855ea17e0b0958f73ec801ae140b0a1679'
packages = repo / manifest['packagesDir']
packages.mkdir(parents=True, exist_ok=True)
for item in manifest['packages']:
    assert item['type'] == 'git'
    path = packages / item['name']
    if not path.exists():
        path.mkdir()
        git(path, 'init', '--quiet')
        git(path, 'remote', 'add', 'origin', item['url'])
        git(path, 'fetch', '--depth', '1', 'origin', item['rev'])
        git(path, 'checkout', '--detach', item['rev'])
    assert git(path, 'rev-parse', 'HEAD') == item['rev'], item['name']
    assert not git(path, 'status', '--porcelain=v1', '--untracked-files=all'), item['name']
    print(item['name'], item['rev'], 'clean')
PY
```

Do not reset an existing mismatched/dirty dependency. Assess it and preserve
evidence. Do not regenerate the manifest or change any pin. Current source
acquisition is recorded in
[dependency-source-acquisition.json](../validation/1032-qemu-environment/dependency-source-acquisition.json).

## Verify the route and obtain dependency caches

Run from `vfa-validation/`; preserve actual commands, output and individual exits:

```sh
python3 ../work-state/tooling/pinned_toolchain.py --describe
python3 ../work-state/tooling/pinned_toolchain.py -- lean --version
python3 ../work-state/tooling/pinned_toolchain.py -- lake --version
python3 ../work-state/tooling/pinned_toolchain.py -- lake env lean --version
python3 ../work-state/tooling/pinned_toolchain.py -- lake build cache
python3 ../work-state/tooling/pinned_toolchain.py -- lake env \
  "$vfa_root/toolchains/qemu-user/bin/qemu-x86_64-static" \
  "$vfa_root/vfa-validation/.lake/packages/mathlib/.lake/build/bin/cache" get
```

Require Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and
Lake `5.0.0-src+eb6cafb`. QEMU supplies guest executable-path discovery without
host mounts or binary patches. Native children do not automatically remain
emulated: keep cache execution explicit inside `lake env`, and retain the
bundled `leantar` entry. A cache-fetch exit alone proves no complete project build.
Current runtime evidence is recorded in
[launcher-description.json](../validation/1032-qemu-environment/launcher-description.json)
and [launcher-smoke.json](../validation/1032-qemu-environment/launcher-smoke.json).
Cache commands have separate recorder directories:
[cache build](../validation/1032-cache-build/) and
[cache retrieval](../validation/1032-cache-get/). Inspect their actual outcomes;
this recipe does not claim successful smokes, cache completion or download counts.

## Fresh3 and the unchanged acceptance sequence

Keep one controlled run, stable isolated inputs and independent writable outputs.
Check actual capacity first. The adapter sets `LEAN_NUM_THREADS=1`, clears
inherited Lean selectors, and selects the same overlay for bare and child Lean.
Do not replace executable copies in `overlay/libexec/` with symlinks.

Use the unchanged [recorder](../validation-recorder/README.md) in a short-yield
foreground tool call. Its attempt directory must not already exist:

```sh
python3 -B "$vfa_root/work-state/validation-recorder/recorder.py" \
  --cwd "$vfa_root/vfa-validation" \
  --attempt-dir "$vfa_root/work-state/validation/1002-candidate-3279bac-fresh3" \
  --candidate 3279bacaec4087cc0d6b7e6b8ae862109cb2dfec --mode fresh \
  --env LEAN_NUM_THREADS=1 --env LAKE_ARTIFACT_CACHE=false \
  -- python3 "$vfa_root/work-state/tooling/pinned_toolchain.py" \
     -- ./check.sh --fresh --jobs 1 --candidate HEAD
```

Retain the tool handle and inspect `run.json`, complete heartbeat records and
`child.log` with bounded calls. A stale record is not success or retry authority.
Fresh1/fresh2 terminal outcomes stay unknown. Preserve a successful fresh record
before another candidate check replaces `.lake/verification.json`.

After fresh success, apply the existing incident-preservation plan to actual
suspect artifacts before repair. Then run these dependent commands separately:

```sh
python3 ../work-state/tooling/pinned_toolchain.py -- ./check.sh --candidate HEAD
python3 ../work-state/tooling/pinned_toolchain.py -- \
  env LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit
python3 ../work-state/tooling/pinned_toolchain.py -- lake env python3 scripts/test-proof-audit.py
```

Require guarded incremental build/post-build integrity/exhaustive-audit success
and its separate record. Run regression only after the managed audit prerequisite
succeeds; preserve all four expected outcomes. Unexpected prerequisite dependency
rebuilds require recording and corresponding guarded evidence to be re-established.
Complete both independent review axes against the same candidate/base and retained
findings, with the environment amendment and actual new execution evidence.
Immediately before acceptance, run through the adapter:

```sh
python3 ../work-state/tooling/pinned_toolchain.py -- ./check.sh --verify-candidate HEAD
```

Follow the full [acceptance checklist](../validation/1002-acceptance-evidence-checklist.json).
Only then accept Preface, then Perm; upload an acceptance checkpoint before Sort.
Setup, cache, partial compilation and source-review clearance are not chapter acceptance.

## Recovery and relocation

Preserve this README, exact helper, guide, provenance and actual outcomes in each
new complete checkpoint. Distribution archives, generated overlays and caches are
reproducible prerequisites, not source-checkpoint payloads. After relocation,
reacquire verified distributions and let the helper create a new overlay: generated
wrappers contain absolute paths and must not be copied blindly. It refuses changed
entries. Recreate the isolated worktree and reacquire dependencies as above.
Do not infer process survival, replay old cleanup, or replace unknown outcomes.
