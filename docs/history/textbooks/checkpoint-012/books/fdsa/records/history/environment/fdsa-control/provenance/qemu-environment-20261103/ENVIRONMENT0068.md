# Reproduce the FDSA development environment without Nix

This is the FDSA-specific version of the working setup guide supplied by the
user on 2026-11-03. It is self-contained together with the files in this
checkpoint. No other conversation or checkpoint is required. The original
supplied guide is retained at
`provenance/qemu-environment-20261103/user-supplied-setup-guide.md`; its reference
to a different checkpoint is not part of this task's recovery procedure.

The user explicitly waived mandatory Nix use when the correct program versions
are acquired separately. All source, proof, audit, review and candidate-identity
rules remain in force. Keep tickets and Git commits local; do not push to GitHub.

## Layout and exact versions

Use a writable task directory with this layout. In the commands below, begin
in that directory unless a step says otherwise.

| Path | Content |
| --- | --- |
| `work/conaled/` | Restored integration repository |
| `work/conaled-ch01-review/` | Clean isolated Chapter 1 candidate worktree |
| `work/fdsa-control/` | Restored local tracker and recovery tooling |
| `bootstrap/direct-lean/lean-4.35.0-linux/` | Unmodified official Lean distribution |
| `bootstrap/qemu-user/bin/qemu-x86_64-static` | Authenticated QEMU executable |
| `bootstrap/lean-4.35.0-host/` | Generated launcher overlay |
| `runtime-tmp/`, `runtime-config/`, `runtime-state/` | Local runtime state |
| `dependency-cache/` | Reproducible dependency cache |

The adapter derives this task directory from its own location:
`work/fdsa-control/tooling/pinned_toolchain.py`. Restore using
`restore.py /absolute/path/to/task-directory/work`. Other destination names
also work if the restored repository/control pair stays one level below the
task directory containing `bootstrap/`.

The required compiler is Lean **4.35.0**, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The release includes Lake
**5.0.0-src+eb6cafb**. Mathlib is
`56a005855ea17e0b0958f73ec801ae140b0a1679`; all eight transitive dependency
revisions come from the unchanged `lake-manifest.json`.

Supporting tools are Python 3.11 or later, Git, curl with HTTPS, `sha256sum`,
GNU tar with zstd support, `dpkg-deb`, and `gpgv` for signature verification.
The authenticated QEMU binary is
x86-64 Linux software; use this recipe on the matching architecture. Supporting
versions observed in this workspace are recorded in the provenance, rather
than being extra project pins.

## 1. Restore the source and isolated candidate

Follow `RECOVER.md` and verify `SHA256SUMS` before restoring. Read `CURRENT.md`
for the current accepted state and candidate; a later checkpoint may have
advanced beyond the Chapter 1 identities used here.

For the pending Chapter 1 candidate preserved in checkpoint 0068:

```sh
git -C work/conaled worktree add --detach ../conaled-ch01-review \
  07e480f6ec9958d4975bb90151005b84f2907614
```

If that worktree already exists, inspect its HEAD and clean status instead of
overwriting it. The integration branch is preserved separately. Do not reset
any draft branch or replace its content with a different book's checkpoint.

## 2. Acquire and verify the official distribution

The release asset is 594,481,375 bytes. Its publisher-provided SHA-256 is
retained in `provenance/direct-environment-20261103/lean-release-api.json`.

```sh
mkdir -p bootstrap/direct-lean
curl --fail --location \
  https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst \
  --output bootstrap/direct-lean/lean-4.35.0-linux.tar.zst
sha256sum --check <<'SHA256'
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  bootstrap/direct-lean/lean-4.35.0-linux.tar.zst
SHA256
tar --no-same-owner --zstd \
  -xf bootstrap/direct-lean/lean-4.35.0-linux.tar.zst \
  -C bootstrap/direct-lean
```

For an existing distribution, verify its recorded acquisition evidence and
executable digests before reuse; do not extract over modified files.
`--no-same-owner` avoids unsupported restoration of archived ownership while
preserving the released file contents.

## 3. Acquire and authenticate QEMU without installing packages

The tested package is Ubuntu `qemu-user-static` **1:8.2.2+ds-0ubuntu1.18**,
amd64. It is 14,709,858 bytes. The selected executable is 3,751,320 bytes.

```sh
mkdir -p bootstrap/qemu-user/extract bootstrap/qemu-user/bin
curl --fail --location \
  https://archive.ubuntu.com/ubuntu/pool/universe/q/qemu/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb \
  --output bootstrap/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb
sha256sum --check <<'SHA256'
5bb397f66063efa349f6fd5cb3b68cd96f29edd0994e4ba5115cf0859a716bf0  bootstrap/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb
SHA256
dpkg-deb --fsys-tarfile \
  bootstrap/qemu-user/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb \
  | tar --no-same-owner -x -C bootstrap/qemu-user/extract \
      ./usr/bin/qemu-x86_64-static ./usr/share/doc/qemu-user-static/copyright
cp bootstrap/qemu-user/extract/usr/bin/qemu-x86_64-static \
  bootstrap/qemu-user/bin/qemu-x86_64-static
cp bootstrap/qemu-user/extract/usr/share/doc/qemu-user-static/copyright \
  bootstrap/qemu-user/copyright
sha256sum --check <<'SHA256'
90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0  bootstrap/qemu-user/bin/qemu-x86_64-static
SHA256
```

`provenance/qemu-environment-20261103/` retains the fresh signed Ubuntu
`InRelease`, authenticated `Packages.xz`, selected package entry, exact
acquisition result, and the public Ubuntu archive keyring used for signature
verification. The chain is: trusted host archive keyring → signed release →
package-index SHA-256 → package SHA-256 → extracted executable SHA-256. Inspect
`qemu-acquisition.json` for the actual commands, fingerprints and digests.

To reproduce the retained release-signature check offline:

```sh
mkdir -p runtime-config/gpgv
gpgv --homedir runtime-config/gpgv \
  --keyring "$PWD/work/fdsa-control/provenance/qemu-environment-20261103/evidence/ubuntu-archive-keyring.gpg" \
  work/fdsa-control/provenance/qemu-environment-20261103/InRelease
```

The preserved public keyring records the original host's trust input. If
fetching fresh moving repository metadata, authenticate its new package index
against its own signed release rather than requiring an older index digest.

## 4. Restore every exact dependency source

This procedure preserves existing clean checkouts and rejects a mismatch. It
does not reset, clean or overwrite a dependency and does not regenerate pins.

```sh
python3 - <<'PY'
import json, subprocess
from pathlib import Path
repo = Path('work/conaled-ch01-review').resolve()
assert (repo / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
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

## 5. Launch both Lean and Lake through the included adapter

The complete launcher source is **`tooling/pinned_toolchain.py`**, included in
this checkpoint. Its layout adaptation is recorded in `adapter-layout.diff`;
the original supplied source and both hashes are retained alongside it.
No installed skill or other checkpoint is required to recreate the launchers.

From `work/conaled-ch01-review/`:

```sh
python3 ../fdsa-control/tooling/pinned_toolchain.py --describe
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lean --version
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lean --githash
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lean --print-prefix
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lake --version
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lake env lean --version
```

The adapter checks the exact QEMU/Lean/Lake executable digests on every
invocation. It creates byte-identical Lean/Lake copies in `overlay/libexec`,
QEMU launchers in `overlay/bin`, and relative links to the official libraries,
sources and remaining tools. Copies are intentional: resolving a symlink back
to the official executable root can make Lake bypass the child Lean launcher.
The official distribution is unchanged.

The adapter clears inherited selectors including `LEAN`, `LEAN_PATH` and
`LEAN_GITHASH`; sets `LEAN_SYSROOT`, Lake's supported `LAKE_OVERRIDE_LEAN`, and
paths to the official shared libraries; and keeps temporary/cache files in the
task directory. Wrap the **entire** project command, since the integrity helper
uses bare Lean and the checker also uses `lake env lean`.

Regenerate the overlay after relocation. Its generated shell wrappers contain
absolute paths and the adapter refuses to overwrite unexpected content. On a
new recovery the overlay is absent and is generated from the included source.
Do not carry old-path wrappers into a new workspace.

Before treating a new environment as ready, also compile a small real theorem
with `lean -o ...` through both bare Lean and `lake env lean`, from a scratch
directory outside the candidate. The current smoke files and actual results
are retained in the QEMU provenance directory. A version print alone is
insufficient. Setup success does not establish any chapter acceptance.

## 6. Build and retrieve the dependency cache

From `work/conaled-ch01-review/`:

```sh
conaled_checkout="$(pwd -P)"
conaled_task_directory="$(cd ../.. && pwd -P)"
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lake build cache
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lake env \
  "$conaled_task_directory/bootstrap/qemu-user/bin/qemu-x86_64-static" \
  "$conaled_checkout/.lake/packages/mathlib/.lake/build/bin/cache" get
```

QEMU does not automatically emulate children started by `execve`. The native
cache executable also uses Lean's executable-path discovery, so execute it
explicitly under QEMU while retaining Lake's environment. The ordinary
`lake exe cache get` command alone is insufficient on this host. The bundled
native `leantar` remains selected through `lean --print-prefix`; no separate
leantar download is needed for the pinned Mathlib revision.

## 7. Run the unchanged acceptance gates and preserve actual outcomes

Use a clean, isolated and stable candidate; do not run concurrent writers in
its project build directory. The adapter defaults to one Lean thread. An
explicit `env` **after** the adapter selects another memory-appropriate count:

```sh
python3 ../fdsa-control/tooling/pinned_toolchain.py -- \
  env LEAN_NUM_THREADS=4 ./check.sh --candidate HEAD
```

The full command checks source policy and public coverage, exact compiler and
dependency identities, both Lake output-integrity phases, every integrated
module and the exhaustive transitive-axiom audit. Preserve its actual terminal
result, closed log and matching `.lake/verification.json`. A partial log,
progress counter or historical process ID is not success.

The retained Chapter 1 review loop requires both independent Standards and
Spec axes against the original fixed base and full repaired scope. The
unchanged audit-fixture suite is not an additional per-formal-change gate
under its recorded Standards disposition. Reassess applicable checks if
validator, pins, root selection or integrity behavior changes. Use fresh mode
when required by README; never weaken the guard or audit to obtain success.

Immediately before accepting the approved candidate, run:

```sh
python3 ../fdsa-control/tooling/pinned_toolchain.py -- \
  ./check.sh --verify-candidate HEAD
```

`tooling/record_command.py` is an optional external recorder for long commands.
It runs one named invocation in the retained execution session, records the owned
child's exit before secondary bookkeeping, preserves a closed log and any
verification record, and refuses to overwrite/retry existing evidence. It
changes no project command. A missing `result.json` leaves the terminal
outcome unknown; old progress records never prove current liveness. Keep the
recorder foregrounded and retain the execution-session handle. A detached
launch on this host did not reach its worker; the untouched launch intent is
preserved under `provenance/qemu-cache-build-20261103/`.

The current execution status and actual result paths belong in `CURRENT.md`
and the local tickets. This reproduction guide does not close findings or
advance chapters by itself. After acceptance, save an immediate checkpoint
containing source/history, tickets, validation and both reviews, then continue
with the next chapter.
