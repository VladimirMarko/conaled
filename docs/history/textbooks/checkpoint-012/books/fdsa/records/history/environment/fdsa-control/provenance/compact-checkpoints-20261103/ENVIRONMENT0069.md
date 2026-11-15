# Native pinned Lean and Lake for the FDSA formalization

The preferred route now runs the official Lean 4.35.0 distribution **natively**.
The user requested an alternative to QEMU on 2026-11-03 because emulation was
too slow. The original Nix exception remains authorized; no project pin,
proof requirement, review axis or chapter obligation is waived.

A small, included compatibility library supplies a missing own-executable
pathname from Linux's ELF startup data. It does not emulate instructions or
modify the official Lean/Lake executables or proof kernel. It is an additional
runtime component with its own source, binary digest, boundary tests and
independent review; do not describe this as an unmodified host environment.

The complete earlier QEMU procedure remains in
`provenance/qemu-environment-20261103/ENVIRONMENT0068.md` and checkpoint0068.
It is a tested fallback, with its later cache-build outcome recorded separately.
No external checkpoint or prior conversation is needed by either procedure.

## 1. Restore source and choose the correct layout

From the extracted checkpoint, verify SHA256SUMS and follow RECOVER.md. Restore
into `/absolute/path/to/task-directory/work`. The task directory contains:

| Path | Purpose |
| --- | --- |
| `work/conaled/` | Restored integration branch and all source refs |
| `work/conaled-ch01-review/` | Clean isolated Chapter 1 candidate |
| `work/fdsa-control/` | Complete tracker, review records and environment tooling |
| `bootstrap/direct-lean/lean-4.35.0-linux/` | Official release, reacquired below |
| `work/fdsa-control/tooling/native/` | Included compatibility source and binary |
| `runtime-tmp/`, `runtime-config/`, `runtime-state/` | Local runtime state |
| `dependency-cache/` | Reproducible dependency cache |

The native adapter derives the task directory from its own location. Keep the
restored repository/control pair one level below the directory containing
`bootstrap/`. It does not generate absolute-path launcher scripts, so relocation
requires no QEMU overlay regeneration.

Read CURRENT.md before selecting a candidate: later checkpoints can advance it.
For this checkpoint's pending Chapter 1 candidate, create the worktree if absent:

```sh
git -C work/conaled worktree add --detach ../conaled-ch01-review \
  07e480f6ec9958d4975bb90151005b84f2907614
```

If it exists, verify its HEAD and clean status instead of overwriting it. The
integration branch and all unfinished draft branches remain separately preserved.

Required supporting tools: Python 3.11 or later, Git, curl with HTTPS, sha256sum,
GNU tar with zstd support, and a matching x86-64 Linux/glibc host. Rebuilding the
small compatibility library additionally uses a C compiler; the actual build
used Ubuntu GCC 13.3.0-6ubuntu2~24.04 on glibc 2.39. The native adapter explicitly
checks its x86-64 Linux platform and all recorded executable/source hashes.

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

## 3. Restore every exact dependency source

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

## 4. Use the included native compatibility component

The complete source is `tooling/native/app_path_compat.c`. The checkpoint also
includes the small compiled `tooling/native/libapp_path_compat.so` so recovery
on this host does not need an unrecorded build. The current source SHA-256 is
`80c1d0e92d7c5c258f32ce3709736bf969c6a24148287f99b238324d7bfbcfb6`;
the binary SHA-256 is
`65910335cb5a2a4359e9ebf7dae4de1da7a48cdbf9dee5eabe82c3e4b02d88a9`.
The adapter checks both, plus the exact official Lean/Lake binary digests, before
every command. A mismatch is an error, not permission to rewrite the expected hash.

The reproducible build command, from the task directory, is:

```sh
cc -shared -fPIC -O2 -fvisibility=hidden -fstack-protector-strong \
  -D_FORTIFY_SOURCE=2 -Wall -Wextra -Werror -Wl,-z,relro,-z,now \
  -o work/fdsa-control/tooling/native/libapp_path_compat.so \
  work/fdsa-control/tooling/native/app_path_compat.c
sha256sum --check <<'SHA256'
65910335cb5a2a4359e9ebf7dae4de1da7a48cdbf9dee5eabe82c3e4b02d88a9  work/fdsa-control/tooling/native/libapp_path_compat.so
SHA256
```

The bundled binary is retained precisely. A different compiler or target may
produce different bytes; preserve and review that build's evidence rather than
silently changing the adapter's digest contract.

### What the component does

The library exports only `readlink`. It first performs the actual Linux syscall.
Success and every error other than ENOENT pass through. Only exact
`/proc/self/exe` or `/proc/<this process's PID>/exe` queries can use the fallback.
It obtains AT_EXECFN from this process's own ELF auxiliary vector, requires an
absolute, existing ELF executable path, and returns its canonical pathname with
readlink's bounded-copy/no-added-NUL behavior. Other process IDs, ordinary
symlinks, missing paths, and `/proc/self/cwd` retain their actual syscall results.
No new mount, privilege, tracing facility or access to another process is needed.

Use stable executables and normal absolute ELF launches. Relative AT_EXECFN
paths and interpreted scripts deliberately receive no synthetic result; a
script's startup entry names the script rather than its interpreter. The
adapter resolves its command to an absolute path before exec. Native Lake's
compiler path and the explicit cache command below have been tested. The normal
check.sh shell/Python entrypoint also passes its native startup check.

The official compiler uses its original libraries and original kernel. The
library does not intercept theorem checking, axiom collection, serialization,
exit codes, build results, or source/dependency identity checks. Its extra
runtime role is disclosed and independently reviewed, not hidden in a patched
compiler or a fabricated version string.

Primary references: Linux [getauxval(3)](https://man7.org/linux/man-pages/man3/getauxval.3.html)
and [ld.so(8)](https://man7.org/linux/man-pages/man8/ld.so.8.html), plus the exact
Lean runtime source retained under the earlier direct-environment provenance.
Actual local behavior and boundaries are recorded under
`provenance/native-environment-20261103/`, including the executed test sources.

## 5. Invoke both bare and Lake-child tools natively

From `work/conaled-ch01-review/`:

```sh
python3 ../fdsa-control/tooling/native_toolchain.py --describe
python3 ../fdsa-control/tooling/native_toolchain.py -- lean --version
python3 ../fdsa-control/tooling/native_toolchain.py -- lean --githash
python3 ../fdsa-control/tooling/native_toolchain.py -- lean --print-prefix
python3 ../fdsa-control/tooling/native_toolchain.py -- lake --version
python3 ../fdsa-control/tooling/native_toolchain.py -- lake env lean --version
```

Expected identities are Lean 4.35.0 at commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake 5.0.0-src+eb6cafb, and the
original release root `bootstrap/direct-lean/lean-4.35.0-linux` as prefix.
Mathlib stays at `56a005855ea17e0b0958f73ec801ae140b0a1679`, with all eight
transitive sources fixed by the manifest.

The adapter sets PATH, LEAN_SYSROOT, the shipped library paths, and LD_PRELOAD
for this command and its descendants. It clears inherited Lean selectors and
refuses to replace or mix an unexpected existing LD_PRELOAD/LD_AUDIT setting.
Temporary files, configuration and caches stay in the task directory. The
calling session's environment is not changed globally.

Wrap the entire project command. The checker uses both bare Lean for its Lake
hash helper and `lake env lean` for compiler identity/auditing. No LEAN or
LEAN_GITHASH override is supplied to simulate a tool identity.

The final native smoke compiled real theorems both ways and produced the same
6,824-byte .olean SHA-256 as the earlier QEMU runs:
`fbf279c5128799661a3f3087d27f139d4da4944e9061ae0c522fce3af38bb980`.
The actual results include timings, source/adapter/shim hashes, clean candidate
identity and all nine clean dependency revisions. These checks validate setup;
they do not establish any chapter acceptance or whole-project speed guarantee.

## 6. Obtain the pinned dependency cache natively

From `work/conaled-ch01-review/`:

```sh
conaled_checkout="$(pwd -P)"
python3 ../fdsa-control/tooling/native_toolchain.py -- lake build cache
python3 ../fdsa-control/tooling/native_toolchain.py -- lake env \
  "$conaled_checkout/.lake/packages/mathlib/.lake/build/bin/cache" get
```

The explicit absolute cache pathname satisfies the compatibility contract and
uses native execution. No QEMU command appears in this route. The cache tool's
normal default source/trust scope is retained; do not add unsafe cache flags or
substitute a different Mathlib revision. The release's bundled leantar is used.
A previously successful exact cache-tool build can be reused; do not rerun it
merely because its earlier frontend executed under QEMU.

## 7. Preserve the complete formal acceptance sequence

From the stable isolated candidate:

```sh
python3 ../fdsa-control/tooling/native_toolchain.py -- \
  env LEAN_NUM_THREADS=2 ./check.sh --candidate HEAD
```

This chooses a conservative Lake task-manager setting for the initial native
full check. In this exact release LEAN_NUM_THREADS affects compiled tools such
as Lake; it is not the Lean CLI's thread selector or a hard global child-process
cap. Lean CLI has its own supported `-j` option. The adapter's default is1; an
explicit setting must follow the adapter as shown. Record the actual setting
and only change it for a concrete resource or performance reason.

The unchanged gate checks source policy/public coverage, exact compiler and
dependency identities, both project output-integrity phases, every integrated
module, and the exhaustive transitive-axiom audit. Consult README and the
independent environment/Chapter1 reviews for the applicable ordinary/fresh mode;
never weaken a guard, skip an audit or use progress as a successful result.

Retain the actual exit, closed log and matching verification record. The
included `tooling/record_command.py` records long commands in a retained
foreground execution session. Optional progress-write failures do not abandon
its owned child. A missing result.json still means an unknown terminal outcome.
Use one unique name per invocation and preserve interruptions separately.

After both independent Chapter 1 axes approve the same exact candidate and full
requirements, immediately run:

```sh
python3 ../fdsa-control/tooling/native_toolchain.py -- \
  ./check.sh --verify-candidate HEAD
```

Only then integrate the reviewed tree, update its ticket and save an immediate
acceptance checkpoint before activating Chapter2. Continue all27 chapters and
Appendices A–C. Native setup, cache retrieval and draft checkpoints do not reduce
that scope or accept any mathematical obligation by themselves.
