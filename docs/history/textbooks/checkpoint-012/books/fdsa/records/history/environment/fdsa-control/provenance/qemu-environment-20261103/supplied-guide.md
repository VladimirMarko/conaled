# conaled: pinned Lean and Lake when the Nix shell cannot start

Verified on **2026-11-03**, on the restricted **x86-64 Linux** host used for the conaled integration.

**The working project route is the exact official Lean 4.35.0 distribution, including Lake 5.0.0-src+eb6cafb, launched through QEMU user mode.** The compiler binaries and project pins remain unchanged. A small external launcher overlay makes both bare Lean and Lake's child Lean invocations use that same distribution. This route does not need Nix.

A separate per-user Nix route also works to a limited extent: static Nix 2.20.6 from `nix-portable v012`, under QEMU with a workspace-local logical store, passed startup, offline evaluation, and one real local shell derivation. **A complete conaled `nix develop` shell has not been demonstrated.** Appendix B describes that result; the numbered procedure below is the route used for the project.

This is a self-contained guide. **Appendix A contains the complete launcher source**; an agent can recreate it without a prior chat or an installed skill. The linked checkpoint contains the supporting logs and provenance, not a hidden prerequisite for copying that source.

## Authorization and scope

The user explicitly authorized this exception for the current work:

> The Nix shell is defined for consistency and convenience, but is not strictly necessary for continued development. You have my permission to disregard `AGENTS.md` in this respect, if you are able to separately acquire the correct versions of required programs.

Read the checkout's `AGENTS.md` and `README.md`. This exception changes environment setup only. Source policy, full build, exhaustive proof audit, applicable regression checks, independent reviews, and final candidate verification still apply. Tickets and changes remain local, with no GitHub writes. Preserve this authorization when handing the current work to another agent; do not assume a different task automatically waives its environment rules.

## What failed, and why this works

The normal Nix installation expects `/nix/store`; `/nix` is absent and outside this workspace's writable roots. The rooted/chroot store alternative needs namespace support unavailable here. PRoot also failed: even with a writable temporary directory and its documented `PROOT_NO_SECCOMP=1` setting, `ptrace(TRACEME)` was denied.

Separately, native Lean fails with `failed to locate application`. Its Linux startup calls `IO.appPath`, which reads `/proc/<pid>/exe`, before command-line option processing. This path is unavailable on the host. `LEAN_SYSROOT` does not override that internal startup path. Native static Nix similarly failed reading `/proc/self/exe`.

QEMU user mode supplies the guest executable's already-known path for that lookup while running the unchanged executable. It requires no new host mount, namespace, tracing facility, privileged installation, or compiler/kernel patch. QEMU does **not** automatically keep a child launched by `execve` under emulation, so the Lean, Lake and cache executables need explicit launchers.

## What has actually passed

| Check | Actual result |
|---|---|
| Lean through QEMU | Lean 4.35.0; commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake through QEMU | Lake 5.0.0-src+eb6cafb; Lean 4.35.0 |
| Bare `lean` and `lake env lean` | Same overlay launcher and same official compiler bytes |
| Small theorem through Lean and through Lake | Successful `.olean`; both test theorems reported no axioms |
| Bundled native C compiler/linker | All 42 cache-tool build tasks succeeded |
| Cache executable through QEMU | All 9,031 requested dependency files downloaded and decompressed, exit 0 |
| Nix through QEMU | Version, offline `1 + 2 = 3`, and one local `/bin/sh` derivation passed |

These are setup results, not a full formal acceptance claim. The project gate was running separately when this guide was captured; no final build/audit pass is claimed here.

## Workspace and prerequisites

Use a writable workspace containing `conaled/`. Run acquisition commands in sections 1–3 from that workspace root, then use the project commands from `conaled/` as stated.

Required supporting tools are Python **3.11 or later**, Git, curl with HTTPS support, GNU tar with zstd support, `sha256sum`, and `dpkg-deb` for extracting the QEMU package. Observed supporting versions were Python 3.12.14, Git 2.51.1, curl 8.5.0, GNU tar 1.35, zstd 1.5.5 and glibc 2.39. These are observations, not additional project pins. This recipe was tested on x86-64 Linux with glibc; another architecture needs corresponding artifacts and new validation.

| Workspace path | Purpose |
|---|---|
| `conaled/` | Existing source checkout |
| `toolchains/lean-4.35.0-linux/` | Unmodified official distribution |
| `toolchains/qemu-user/bin/qemu-x86_64-static` | Authenticated emulator |
| `toolchains/lean-4.35.0-host/` | Generated launcher overlay |
| `work-state/tooling/pinned_toolchain.py` | Complete adapter in Appendix A |
| `runtime-tmp/`, `runtime-config/`, `runtime-state/` | Workspace-local runtime state |
| `dependency-cache/` | Reproducible dependency cache |

For continuation of the book integration, restore [checkpoint 039](https://chatgpt.com/library?file_id=libfile_ac04b9cdc61881919726beb282ded644&account_id=personal) following its `RESTORE.md`. Its archive SHA-256 is `5ac950843fafcf2e7cd73d87ab6c30a477374100e30d7e8719e66e8bc070af33`. It restores local branch `local/adwh-continue-2026-11-03`, candidate `f62c48c8e5703ed68a5882216a07cb5c66d2eca4`, tree `c81938c7629432111b1dba72983e732e8e979cfb`; that branch has not been uploaded to GitHub. The [recovery receipt](https://chatgpt.com/library?file_id=libfile_b8b30960e3c08191bccc9aa49a3ecbf6&account_id=personal) records the actual successful restoration.

For another existing conaled checkout, preserve its source state and confirm its pins before applying this exact-version recipe:

```sh
python3 - <<'PY'
import json
from pathlib import Path
repo = Path('conaled')
assert (repo / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
manifest = json.loads((repo / 'lake-manifest.json').read_text())
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
assert mathlib['rev'] == '56a005855ea17e0b0958f73ec801ae140b0a1679'
print('Expected Lean/Mathlib generation; preserve every transitive manifest revision.')
PY
```

If either assertion fails, acquire the versions required by that checkout instead. Do not change `lean-toolchain`, `lake-manifest.json` or `flake.lock` merely to boot the host.

## 1. Obtain the exact official Lean distribution

Source: [Lean v4.35.0 release](https://github.com/leanprover/lean4/releases/tag/v4.35.0).
The retained release metadata (`work-state/validation/standalone-environment-2026-11-03/official-lean-release.json` in checkpoint 039) records the
GitHub-published SHA-256 and the 594,481,375-byte Linux asset. The actual download
and extraction are recorded in lean-distribution-download.json (`work-state/validation/standalone-environment-2026-11-03/lean-distribution-download.json` in checkpoint 039).

```sh
mkdir -p toolchains/downloads
curl --fail --location \
  https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst \
  --output toolchains/downloads/lean-4.35.0-linux.tar.zst
sha256sum --check <<'SHA256'
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  toolchains/downloads/lean-4.35.0-linux.tar.zst
SHA256
tar --no-same-owner --zstd \
  -xf toolchains/downloads/lean-4.35.0-linux.tar.zst -C toolchains
```

`--no-same-owner` matters on this host: the original archive's uid/gid metadata
cannot be restored here. It leaves the distributed file contents unchanged.
The extracted directory is `toolchains/lean-4.35.0-linux`.

## 2. Obtain the authenticated QEMU executable

The tested package is Ubuntu `qemu-user-static`, version
`1:8.2.2+ds-0ubuntu1.18`, for amd64. The actual authentication chain is retained
in qemu-acquisition.json (`work-state/validation/standalone-environment-2026-11-03/qemu/qemu-acquisition.json` in checkpoint 039):

1. Ubuntu's trusted archive keyring verified the retained InRelease (`work-state/validation/standalone-environment-2026-11-03/qemu/InRelease` in checkpoint 039).
2. Its SHA-256 stanza authenticated Packages.xz (`work-state/validation/standalone-environment-2026-11-03/qemu/Packages.xz` in checkpoint 039), the
   `universe/binary-amd64/Packages.xz` index.
3. The index authenticated the exact `.deb` through its package SHA-256.
4. The extracted `qemu-x86_64-static` digest is also recorded and checked by
   the environment adapter.

The signed release was obtained from
`https://archive.ubuntu.com/ubuntu/dists/noble-updates/InRelease`; its package
index was obtained from the corresponding `universe/binary-amd64/Packages.xz`.
The retained package metadata (`work-state/validation/standalone-environment-2026-11-03/qemu/official-package-metadata.json` in checkpoint 039) identifies the
exact package entry. To recheck the retained signature on a host with the
trusted Ubuntu archive keyring:

```sh
mkdir -p runtime-config/gpgv
gpgv --homedir runtime-config/gpgv \
  --keyring /usr/share/keyrings/ubuntu-archive-keyring.gpg \
  work-state/validation/standalone-environment-2026-11-03/qemu/InRelease
```

The observed signing-key fingerprint was
`F6ECB3762474EDA9D21B7022871920D1991BC93C`. The authenticated package-index
SHA-256 was `2dd82d93dc7fab28f67d5120aa122d8896b557ce4984995635a7dfff1353386d`.
When fetching fresh repository metadata, authenticate that new index against
its own signed release rather than assuming the moving index retains this hash.

The checkpoint retains the signed release, compressed package index, selected
package metadata, acquisition result, and a byte-identical copy of the observed
host's public Ubuntu archive keyring. Their paths and hashes are recorded in
evidence/authentication-inputs.json (`work-state/validation/standalone-environment-2026-11-03/qemu/evidence/authentication-inputs.json` in checkpoint 039).
For offline reproduction of the recorded signature check, the preserved
public keyring (`work-state/validation/standalone-environment-2026-11-03/qemu/evidence/ubuntu-archive-keyring.gpg` in checkpoint 039) can replace the system
keyring path in the command above. This preserves the original verification
inputs; the original trust attribution remains the host's trusted Ubuntu
installation. No QEMU executable, `.deb`, or Lean distribution archive is part
of this small provenance bundle.

Download and extract the recorded package without installing it:

```sh
mkdir -p toolchains/qemu-user/extract toolchains/qemu-user/bin
curl --fail --location \
  https://archive.ubuntu.com/ubuntu/pool/universe/q/qemu/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb \
  --output toolchains/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb
sha256sum --check <<'SHA256'
5bb397f66063efa349f6fd5cb3b68cd96f29edd0994e4ba5115cf0859a716bf0  toolchains/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb
SHA256
dpkg-deb --fsys-tarfile \
  toolchains/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb \
  | tar --no-same-owner -x -C toolchains/qemu-user/extract \
      ./usr/bin/qemu-x86_64-static ./usr/share/doc/qemu-user-static/copyright
cp toolchains/qemu-user/extract/usr/bin/qemu-x86_64-static \
  toolchains/qemu-user/bin/qemu-x86_64-static
cp toolchains/qemu-user/extract/usr/share/doc/qemu-user-static/copyright \
  toolchains/qemu-user/copyright
sha256sum --check <<'SHA256'
90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0  toolchains/qemu-user/bin/qemu-x86_64-static
SHA256
```

The package is 14,709,858 bytes; the selected executable is 3,751,320 bytes.
The adapter checks this exact executable digest. A different QEMU package needs
its own acquisition evidence and adapter review.

## 3. Restore the exact dependency sources

The authoritative revisions are in `conaled/lake-manifest.json`; no manifest
regeneration is needed. dependency-source-acquisition.json (`work-state/validation/standalone-environment-2026-11-03/dependency-source-acquisition.json` in checkpoint 039)
records the actual commands and clean revisions for all nine dependencies.
The following is a fresh-checkout procedure; it checks an existing checkout
without resetting or overwriting it:

```sh
python3 - <<'PY'
import json, subprocess
from pathlib import Path
repo = Path('conaled').resolve()
manifest = json.loads((repo / 'lake-manifest.json').read_text())
packages = repo / manifest['packagesDir']
packages.mkdir(parents=True, exist_ok=True)
def git(path, *args):
    return subprocess.run(['git', '-C', str(path), *args], check=True,
                          capture_output=True, text=True).stdout.strip()
for item in manifest['packages']:
    path = packages / item['name']
    if not path.exists():
        path.mkdir()
        git(path, 'init', '--quiet')
        git(path, 'remote', 'add', 'origin', item['url'])
        git(path, 'fetch', '--depth', '1', 'origin', item['rev'])
        git(path, 'checkout', '--detach', item['rev'])
    assert git(path, 'rev-parse', 'HEAD') == item['rev'], item['name']
    assert not git(path, 'status', '--porcelain=v1'), item['name']
    print(item['name'], item['rev'], 'clean')
PY
```

Mathlib must remain at `56a005855ea17e0b0958f73ec801ae140b0a1679`; the eight
transitive dependencies must also match the manifest. Supporting tools used in
the observed setup are recorded in
supporting-tools-and-source-pins.json (`work-state/validation/standalone-environment-2026-11-03/supporting-tools-and-source-pins.json` in checkpoint 039).
The project check scripts require Python 3.11 or later.

## 4. Use the checked adapter for parent and child commands

pinned_toolchain.py (`work-state/tooling/pinned_toolchain.py` in checkpoint 039) automatically creates
and verifies `toolchains/lean-4.35.0-host`. Its `libexec/lean` and `libexec/lake`
are byte-identical copies of the official executables. Its `bin/lean` and
`bin/lake` launch those copies through QEMU; its library/source entries and
other tool entries point to the official distribution. Locating both copied
executables inside this overlay makes their own installation discovery agree
with Lake's child environment.

If you did not restore checkpoint 039, first run `mkdir -p work-state/tooling` from the workspace root, save the complete Appendix A source as `work-state/tooling/pinned_toolchain.py`, and run the SHA-256 check at the end of that appendix. Then enter `conaled/`. This creates the helper before any command below uses it.

From `conaled/`, use:

```sh
python3 ../work-state/tooling/pinned_toolchain.py --describe
python3 ../work-state/tooling/pinned_toolchain.py -- lean --version
python3 ../work-state/tooling/pinned_toolchain.py -- lake env lean --version
```

The adapter clears inherited toolchain selectors, supplies the supported Lake
installation override, resolves the unchanged bundled shared libraries, and
keeps temporary files and caches inside the workspace. It does not alter
`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `flake.lock`, source
modules, or proof-audit policy. Use it around the entire project command so
both bare `lean` and Lake's child `lean` follow the same route.

The corrected recorded launcher environment (`work-state/validation/standalone-environment-2026-11-03/qemu/launcher-environment-r1.json` in checkpoint 039) contains hashes
and exact overrides; launcher-smoke.json (`work-state/validation/standalone-environment-2026-11-03/qemu/launcher-smoke.json` in checkpoint 039) records the
actual startup and child-path checks. qemu-kernel-smoke.json (`work-state/validation/standalone-environment-2026-11-03/qemu/qemu-kernel-smoke.json` in checkpoint 039)
records a separate Init-only theorem compilation through the unchanged kernel.
These are environment checks, not a project acceptance claim.

### Obtain the dependency cache through an explicit guest execution

On this host, building the cache tool and launching it are separate steps.
The first `lake exe cache get` attempt completed all 42 build tasks, including
the C compilation/linking and `cache:exe`, then its native cache process failed
with `failed to locate application`. See the preserved
cache-001 result (`work-state/validation/standalone-environment-2026-11-03/cache-001/result.json` in checkpoint 039) and
closed log (`work-state/validation/standalone-environment-2026-11-03/cache-001/full.log` in checkpoint 039). `CacheM.run` calls `getSrcSearchPath`, which
unconditionally reaches `IO.appDir`; it therefore needs the same guest
executable-path discovery supplied to the Lean and Lake launchers.

From the recovered `conaled/` checkout, build the cache executable, then run it
explicitly through QEMU inside Lake's environment:

```sh
conaled_checkout="$(pwd -P)"
conaled_workspace="$(cd .. && pwd -P)"
python3 ../work-state/tooling/pinned_toolchain.py -- lake build cache
python3 ../work-state/tooling/pinned_toolchain.py -- lake env \
  "$conaled_workspace/toolchains/qemu-user/bin/qemu-x86_64-static" \
  "$conaled_checkout/.lake/packages/mathlib/.lake/build/bin/cache" get
```

The second step corresponds to the recorded
cache-002 launch (`work-state/validation/standalone-environment-2026-11-03/cache-002/start.json` in checkpoint 039); its actual outcome is in
cache-002/result.json (`work-state/validation/standalone-environment-2026-11-03/cache-002/result.json` in checkpoint 039) and its
log (`work-state/validation/standalone-environment-2026-11-03/cache-002/full.log` in checkpoint 039). Retaining `lake env` supplies the dependency paths
and inherited child-tool environment. QEMU does not automatically keep a new
host-executed child under emulation, so the ordinary `lake exe cache get`
command alone does not provide this host adaptation. Cache retrieval does not
establish any project build, audit, or acceptance result.

### Cache-specific child tool

Pinned Mathlib `Cache/IO.lean` runs bare `lean --print-prefix`, locates
`<returned prefix>/bin/leantar`, and invokes that tool directly with a JSON
decompression request on stdin (`-x --delete-corrupted -j -`). The overlay must
therefore retain the official `bin/leantar` entry and the inherited PATH/library
settings. No separate leantar download or replacement is required by this
Mathlib revision. Current cache and validation status belongs to the actual
execution records linked above and the current tracker.

## 5. Preserve the normal acceptance sequence

From a stable isolated candidate checkout, use the adapter around the unchanged
commands required by the repository and the existing review loop:

```sh
python3 ../work-state/tooling/pinned_toolchain.py -- env LEAN_NUM_THREADS=4 ./check.sh --candidate HEAD
python3 ../work-state/tooling/pinned_toolchain.py -- lake --no-cache --rehash build +ProofAudit
python3 ../work-state/tooling/pinned_toolchain.py -- lake env python3 scripts/test-proof-audit.py
python3 ../work-state/tooling/pinned_toolchain.py -- ./check.sh --verify-candidate HEAD
```

Each dependent step requires an actual successful preceding result. Retain the
closed build/audit log and matching verification record, complete the same
independent Standards/Spec reviews, and repeat the final candidate-record check
immediately before scoped acceptance. Consult the current tracker for which
of these steps have actually run; this reproduction document does not advance
their status.

## 6. Important details for agents

**Keep both executables in one overlay root.** Running QEMU on the original `bin/lake` while overriding only the Lean root is insufficient: Lake can prepend its original `bin` before the wrapper directory. The adapter uses byte-identical Lean/Lake copies in `overlay/libexec/`, wrappers in `overlay/bin/`, and symlinks for libraries/include/source files. Their installation discovery then agrees. Do not replace these copies with symlinks that canonicalize back to the original executable path.

**Wrap the entire project command.** `check.sh` uses both bare Lean and `lake env lean`. The adapter also clears inherited selectors including `LEAN`, `LEAN_PATH` and `LEAN_GITHASH`, supplies `LEAN_SYSROOT` and `LAKE_OVERRIDE_LEAN`, and sets the official library paths. Those paths resolve a separate `$ORIGIN` lookup problem on this host.

**Keep cache execution explicit.** Building the cache utility succeeded natively; running it natively failed because `Lean.getSrcSearchPath` unconditionally calls `IO.appDir`. The `lake env QEMU CACHE get` command fixes that execution boundary while preserving Lake's paths and the cache's default scope/trust policy. The bundled native `leantar` was usable and remains selected through `lean --print-prefix`.

**Record effective parallelism.** The adapter defaults to `LEAN_NUM_THREADS=1`. The ongoing full gate selects four using `env LEAN_NUM_THREADS=4` after the adapter, as shown in section 5; setting it only before the adapter would be overwritten. Four was selected on the observed nine-CPU, approximately 10 GB host after a slow one-thread run. Choose a memory-appropriate value on another host. Keep one controlled validation run and a stable source/dependency checkout.

**Regenerate after relocation.** The Python adapter derives the workspace from its own location, but generated shell wrappers contain absolute paths. Preserve the source and reacquisition recipe, then regenerate the overlay in the new workspace. Do not copy old-path wrappers blindly. The adapter refuses to overwrite unexpectedly changed payloads or wrappers.

**Handle additional tools only if needed.** The current build does not enable `leanir`/postponed compilation. A future configuration that does so needs its own checked launch path; do not assume every native child is automatically emulated.

**Preserve acceptance boundaries.** Retain the actual terminal result and closed log, exact source/dependency identities, and matching `.lake/verification.json`. Run `+ProofAudit`, the four-case regression, independent final reviews, then repeat `--verify-candidate HEAD` immediately before acceptance. Setup success or a partially completed build is not a full project pass. Archived process/session IDs cannot be resumed after workspace loss.

## Appendix A. Complete reviewed launcher adapter

Create `work-state/tooling/` under the workspace, then save the following block exactly as `work-state/tooling/pinned_toolchain.py`. Checkpoint 039 already contains it. Its SHA-256 is `a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47`.

```python
#!/usr/bin/env python3
"""Launch the pinned, unmodified Lean distribution on this host via QEMU.

This is recovery-environment tooling outside the conaled source tree. The
official distribution stays immutable. Lake's supported installation override
selects an overlay whose Lean entry point explicitly invokes user-mode QEMU.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import sys


WORKSPACE = Path(__file__).resolve().parents[2]
TOOLCHAINS = WORKSPACE / "toolchains"
OFFICIAL = TOOLCHAINS / "lean-4.35.0-linux"
OVERLAY = TOOLCHAINS / "lean-4.35.0-host"
QEMU = TOOLCHAINS / "qemu-user/bin/qemu-x86_64-static"
EXPECTED = {
    QEMU: "90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0",
    OFFICIAL / "bin/lean": "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
    OFFICIAL / "bin/lake": "8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1",
}
UNSET = ("LEAN", "LEAN_PATH", "LEAN_SYSROOT", "LEAN_AR", "LEAN_CC", "LEAN_GITHASH", "LAKE_HOME", "LAKE_OVERRIDE_LEAN")


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def link(target: Path, source: Path) -> None:
    relative = os.path.relpath(source, target.parent)
    if target.is_symlink() and os.readlink(target) == relative:
        return
    if target.exists() or target.is_symlink():
        raise RuntimeError(f"Refusing to replace unexpected overlay entry: {target}")
    target.symlink_to(relative, target_is_directory=source.is_dir())


def prepare_overlay() -> None:
    for path, expected in EXPECTED.items():
        if digest(path) != expected:
            raise RuntimeError(f"Pinned executable digest mismatch: {path}")
    (OVERLAY / "bin").mkdir(parents=True, exist_ok=True)
    (OVERLAY / "libexec").mkdir(parents=True, exist_ok=True)
    for source in sorted(OFFICIAL.iterdir()):
        if source.name != "bin":
            link(OVERLAY / source.name, source)
    for source in sorted((OFFICIAL / "bin").iterdir()):
        target = OVERLAY / "bin" / source.name
        if source.name in ("lean", "lake"):
            # Lake prepends its own bin directory in `lake env`. Keeping both
            # real executables in this root makes its joint-home discovery
            # agree with the compiler overlay. A symlink would canonicalize
            # back to the original root and bypass the child Lean launcher.
            payload = OVERLAY / "libexec" / source.name
            if not payload.exists():
                shutil.copyfile(source, payload)
                payload.chmod(0o755)
            if digest(payload) != EXPECTED[source]:
                raise RuntimeError(f"Relocated executable digest mismatch: {payload}")
            script = "#!/bin/sh\nexec " + shlex.quote(str(QEMU)) + " " + shlex.quote(str(payload)) + ' "$@"\n'
            if target.is_symlink():
                raise RuntimeError(f"Unexpected launcher symlink: {target}")
            if target.exists() and target.read_text() != script:
                raise RuntimeError(f"Refusing to replace changed launcher: {target}")
            if not target.exists():
                target.write_text(script)
                target.chmod(0o755)
        else:
            link(target, source)


def environment() -> tuple[dict[str, str], dict[str, str]]:
    prepare_overlay()
    env = dict(os.environ)
    for name in UNSET:
        env.pop(name, None)
    overrides = {
        "PATH": str(OVERLAY / "bin") + os.pathsep + env.get("PATH", os.defpath),
        "LEAN_SYSROOT": str(OVERLAY),
        "LAKE_OVERRIDE_LEAN": "true",
        "LD_LIBRARY_PATH": os.pathsep.join((str(OFFICIAL / "lib"), str(OFFICIAL / "lib/lean"))),
        "TMPDIR": str(WORKSPACE / "runtime-tmp"),
        "MATHLIB_CACHE_DIR": str(WORKSPACE / "dependency-cache/mathlib"),
        "XDG_CACHE_HOME": str(WORKSPACE / "dependency-cache/xdg"),
        "XDG_CONFIG_HOME": str(WORKSPACE / "runtime-config"),
        "XDG_STATE_HOME": str(WORKSPACE / "runtime-state"),
        "LEAN_NUM_THREADS": "1",
    }
    for name in ("TMPDIR", "MATHLIB_CACHE_DIR", "XDG_CACHE_HOME", "XDG_CONFIG_HOME", "XDG_STATE_HOME"):
        Path(overrides[name]).mkdir(parents=True, exist_ok=True)
    env.update(overrides)
    return env, overrides


def main() -> None:
    env, overrides = environment()
    args = sys.argv[1:]
    if args == ["--describe"]:
        print(json.dumps({
            "workspace": str(WORKSPACE),
            "official_distribution": str(OFFICIAL),
            "overlay": str(OVERLAY),
            "environment_overrides": overrides,
            "cleared_inherited_selectors": UNSET,
            "executables": {str(path): digest(path) for path in EXPECTED},
            "relocated_executables": {name: digest(OVERLAY / "libexec" / name)
                                      for name in ("lean", "lake")},
            "launchers": {name: {"sha256": digest(OVERLAY / "bin" / name),
                                   "content": (OVERLAY / "bin" / name).read_text()}
                          for name in ("lean", "lake")},
        }, indent=2))
        return
    if args[:1] == ["--"]:
        args.pop(0)
    if not args:
        raise SystemExit("Usage: pinned_toolchain.py --describe | -- COMMAND [ARG ...]")
    os.execvpe(args[0], args, env)


if __name__ == "__main__":
    main()
```

Verify the saved adapter from the workspace root:

```sh
sha256sum --check <<'SHA256'
a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47  work-state/tooling/pinned_toolchain.py
SHA256
```

## Appendix B. The limited per-user Nix route

This route is optional and separate from the project recipe. It establishes a working Nix client/evaluator and one local builder, not the full pinned conaled flake shell.

The exact source is [nix-portable v012](https://github.com/DavHau/nix-portable/releases/tag/v012), archive SHA-256 `b409c55904c909ac3aeda3fb1253319f86a89ddd1ba31a5dec33d4a06414c72a`. Its static Nix executable is 10,845,872 bytes, SHA-256 `6aaf87aa8f1e0af28d69a857f33683f9000cb844b510feaf501b41ebd3d56e03`.

The portable distribution is a self-extracting ZIP. Extracting the exact member directly avoids starting its failed PRoot/runtime-selector route. These member bytes were checked against the executable used in the successful tests.

From the workspace root:

```sh
mkdir -p toolchains/nix-static
curl --fail --location \
  https://github.com/DavHau/nix-portable/releases/download/v012/nix-portable-x86_64 \
  --output toolchains/nix-static/nix-portable-x86_64
sha256sum --check <<'SHA256'
b409c55904c909ac3aeda3fb1253319f86a89ddd1ba31a5dec33d4a06414c72a  toolchains/nix-static/nix-portable-x86_64
SHA256
python3 - <<'PY'
from pathlib import Path
import hashlib, zipfile
with zipfile.ZipFile('toolchains/nix-static/nix-portable-x86_64') as packed:
    data = packed.read('nix/store/h9g281pzs2ackcavsaligh09fa0v1ys0-nix/bin/nix')
assert hashlib.sha256(data).hexdigest() == '6aaf87aa8f1e0af28d69a857f33683f9000cb844b510feaf501b41ebd3d56e03'
target = Path('toolchains/nix-static/nix')
if target.exists():
    assert target.read_bytes() == data, 'Existing payload differs; do not overwrite it.'
else:
    target.write_bytes(data)
    target.chmod(0o755)
PY
```

Use a dedicated shell for the optional Nix probe, or let the project adapter set its own runtime environment before returning to Lean work:

```sh
conaled_workspace="$(pwd -P)"
conaled_nix_state="$conaled_workspace/runtime-nix"
mkdir -p "$conaled_nix_state/tmp" "$conaled_nix_state/cache" \
  "$conaled_nix_state/config/nix" "$conaled_nix_state/state" \
  "$conaled_nix_state/log" "$conaled_nix_state/store"
export TMPDIR="$conaled_nix_state/tmp"
export XDG_CACHE_HOME="$conaled_nix_state/cache"
export XDG_CONFIG_HOME="$conaled_nix_state/config"
export XDG_STATE_HOME="$conaled_nix_state/state"
export NIX_CONF_DIR="$conaled_nix_state/config/nix"
export NIX_STATE_DIR="$conaled_nix_state/state"
export NIX_LOG_DIR="$conaled_nix_state/log"
export NIX_STORE_DIR="$conaled_nix_state/store"
export NIX_USER_CONF_FILES="$conaled_nix_state/config/nix/empty.conf"
: > "$NIX_USER_CONF_FILES"
unset NIX_REMOTE NIX_PATH NP_RUN NP_DEBUG NIX_CONFIG
conaled_nix_store="local?store=$conaled_nix_state/store&state=$conaled_nix_state/state&log=$conaled_nix_state/log"
"$conaled_workspace/toolchains/qemu-user/bin/qemu-x86_64-static" \
  "$conaled_workspace/toolchains/nix-static/nix" --version
"$conaled_workspace/toolchains/qemu-user/bin/qemu-x86_64-static" \
  "$conaled_workspace/toolchains/nix-static/nix" \
  --extra-experimental-features nix-command --offline \
  --option build-users-group '' \
  eval --store "$conaled_nix_store" --expr '1 + 2'
```

Expected outputs are `nix (Nix) 2.20.6` and `3`. A nonfatal warning about missing `/proc/stat` was observed.

For the small local-builder check, the tested expression was:

```nix
derivation {
  name = "workspace-builder-smoke";
  system = "x86_64-linux";
  preferLocalBuild = true;
  builder = "/bin/sh";
  args = [ "-c" ''printf '%s\n' 'nix-workspace-builder-smoke' > "$out"'' ];
}
```

Save it as `runtime-nix/builder-smoke.nix`, then use the same shell variables:

```sh
"$conaled_workspace/toolchains/qemu-user/bin/qemu-x86_64-static" \
  "$conaled_workspace/toolchains/nix-static/nix" \
  --extra-experimental-features nix-command --offline \
  --option sandbox false --option build-users-group '' \
  --option builders '' --option substitute false \
  --option max-jobs 1 --option cores 1 \
  build --store "$conaled_nix_store" --no-link --json \
  --file "$conaled_nix_state/builder-smoke.nix"
```

The recorded successful execution supplied that same expression using `--expr`; `--file` above avoids difficult shell quoting. Its output contained exactly `nix-workspace-builder-smoke` and a final newline: 28 bytes, SHA-256 `2942c91f1ac0dffe12e773891ee09297d074efd81e3ef6d68948c9f0c0f69cd3`.

`preferLocalBuild = true` is consequential. Without it, the first attempt spawned a native Nix build-hook helper and failed at `/proc/self/exe`. The local preference selected the direct local path. Empty `build-users-group` makes the build run as the calling user; `sandbox=false` here is a Nix setting within the existing host restrictions, not a host permission change.

A custom **logical** store prefix differs from a chroot store whose logical prefix remains `/nix/store`. Standard `/nix/store` binary substitutes cannot be reused with a different logical prefix, so a full package environment may need local builds. Arbitrary helper/child programs can also need explicit compatibility treatment. Do not infer a successful nixpkgs bootstrap or conaled flake shell from this tiny local derivation.

## Primary references and retained evidence

- [Lean 4.35.0 release](https://github.com/leanprover/lean4/releases/tag/v4.35.0).
- [Pinned Lean runtime path lookup](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/io.cpp) and [Lean path discovery](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Util/Path.lean).
- [Pinned Lake installation discovery](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/Config/InstallPath.lean).
- [QEMU user-mode documentation](https://www.qemu.org/docs/master/user/main.html).
- [Nix local-store documentation](https://nix.dev/manual/nix/2.35/store/types/local-store).
- [nix-portable v012 source](https://github.com/DavHau/nix-portable/blob/v012/default.nix).
- [Nix 2.20.6 local-build scheduling](https://github.com/NixOS/nix/blob/2.20.6/src/libstore/build/derivation-goal.cc).

Inside checkpoint 039, `work-state/validation/standalone-environment-2026-11-03/` contains the release metadata, source/tool identities, dependency acquisition, QEMU signature chain, smoke tests and both cache attempts. Its `nix-user/` subtree retains failed and successful Nix tests. `review-recovery/039-outcomes.json` binds the independent environment/recovery reviews. Historical absolute paths describe those actual executions; use the new workspace path when reproducing them.
