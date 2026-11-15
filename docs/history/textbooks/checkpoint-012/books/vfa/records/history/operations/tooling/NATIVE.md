# Native Lean/Lake 4.35.0 in this restricted Linux environment

This is an alternative to the retained [QEMU recipe](README.md). It executes
the unchanged official compiler natively. A small external shared library
supplies the current executable's already-known path for Lean's startup lookup.
It does not mount procfs, read denied process data, change permissions, or patch
the compiler. The user explicitly requested alternatives to slow emulation;
the exact request and scope are in `../specs/1033-native-app-path.md`.

All formal source, dependency and acceptance requirements remain. This file
describes the execution environment, not chapter acceptance or a complete
proof of the runtime. Full validation results belong to the recorded attempts.

## Prerequisites and preserved inputs

Restore the source checkpoint into a new directory, run its `restore.py`, and
keep `work-state/` beside `conaled/`. Let `recovery_root` name this directory.
Follow README.md to acquire and verify the **complete unchanged official Lean
4.35.0 Linux distribution**, using the recorded release archive digest and
all nine manifest revisions. QEMU is optional for this native route, but the
exact supplied QEMU launcher and its acquisition recipe remain available.

The official release archive SHA-256 is
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Extract it as `toolchains/lean-4.35.0-linux/`. Lean must report commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; the matching Lake reports
`5.0.0-src+eb6cafb`. The native helper checks these official executable hashes:

| File | SHA-256 |
| --- | --- |
| `bin/lean` | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |
| `bin/lake` | `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1` |
| `work-state/tooling/native_app_path.c` | `0798e7e0d6b71510dd3f68778af1e487aaa9093af5f7cb1666c22b8605f5fd76` |
| `toolchains/native-compat/libconaled_app_path.so` | `8bb82334a2888e37a18b657a16f498cba239aaf3935bf24cc5b59728f6df5a18` |

The helper also uses the adjacent, unchanged `pinned_toolchain.py` for constants,
hashing and safe symlink creation. Its SHA-256 remains
`a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47`.
No QEMU process is started by importing that module.

## Build the compatibility library

The observed compiler was `/usr/bin/cc`, Ubuntu GCC
`13.3.0-6ubuntu2~24.04`, on x86-64 Linux/glibc. The build command and actual
compiler output are preserved under `../validation/1033-native-environment/`.
From the restored recovery root:

```sh
recovery_root="$PWD"
mkdir -p "$recovery_root/toolchains/native-compat"
/usr/bin/cc -shared -fPIC -O2 -Wall -Wextra -Werror \
  -o "$recovery_root/toolchains/native-compat/libconaled_app_path.so" \
  "$recovery_root/work-state/tooling/native_app_path.c"
sha256sum "$recovery_root/work-state/tooling/native_app_path.c" \
  "$recovery_root/toolchains/native-compat/libconaled_app_path.so"
```

Check both hashes against the table. A different compiler/platform may produce
different bytes; record and review that environment change before using it.
Do not remove the helper's integrity checks to make an unknown build pass.
The shim is a local generated runtime artifact and is reconstructed from its
complete saved source; downloaded toolchains and build caches stay excluded
from ordinary source checkpoints.

## Test and select the native overlay

```sh
mkdir -p "$recovery_root/runtime-tmp"
python3 -B "$recovery_root/work-state/tooling/test_native_app_path.py" \
  "$recovery_root/toolchains/native-compat/libconaled_app_path.so" \
  "$recovery_root/runtime-tmp"
python3 -B "$recovery_root/work-state/tooling/pinned_native_toolchain.py" --describe
python3 -B "$recovery_root/work-state/tooling/pinned_native_toolchain.py" -- lean --version
python3 -B "$recovery_root/work-state/tooling/pinned_native_toolchain.py" -- lake --version
```

The helper creates a separate `toolchains/lean-4.35.0-native/` overlay. Its
`libexec/lean` and `libexec/lake` are byte-identical copies of the official
executables. Its `bin/` launchers set the exact per-program `CONALED_SELF_EXE`
and this shim's `LD_PRELOAD`; all remaining distribution entries refer to the
verified original. It selects the supported Lake installation override,
explicit official library paths, workspace-local temporary/cache locations,
and `LEAN_NUM_THREADS=1` for Lake's runtime worker pool. For this project's
ordinary Lake targets, that pool setting serializes external compiler jobs.
The Lean command-line compiler has a separate internal worker setting: the
current launcher passes no `-j`/`--threads` argument, so Lean retains its hardware
concurrency default. The helper clears inherited Lean selectors and preload
selection before starting the requested command.

From the isolated candidate checkout, additionally verify:

```sh
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- lake env lean --version
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- lake env python3 -c \
  'import shutil; print(shutil.which("lean"))'
```

The discovered child must be the native overlay's `bin/lean`. After relocation,
generate a new overlay: wrapper scripts contain absolute paths. The helper
refuses unexpected entries instead of overwriting them. Preserve old runtime
artifacts while an owned process could still use them; choose a new distinct
overlay when necessary. Do not change compiler/shim inputs during validation.

The tests exercise the actual dynamically linked readlink function in separate
processes: both current-process spellings, truncated output without a NUL,
zero size, null buffer, successful errno preservation, ordinary symlinks,
nonmatching paths, nonexistent PID, and absent/mismatched executable identity.
They do not rely on real procfs being mounted. Actual native proof smokes and
the complete Squares module also passed; the observed Squares output was
byte-identical to the QEMU result. Timing evidence is scoped to its recorded
run and resource conditions; it is not a universal speedup claim.

## Dependencies and the native cache executable

Use the unchanged manifest acquisition instructions in README.md. All nine
source revisions must match and be clean. Existing completed dependency caches
may be reused under the project's normal trust policy. For a cold cache:

```sh
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- lake build cache
cache_executable="$PWD/.lake/packages/mathlib/.lake/build/bin/cache"
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- lake env env \
  LD_PRELOAD="$recovery_root/toolchains/native-compat/libconaled_app_path.so" \
  CONALED_SELF_EXE="$cache_executable" "$cache_executable" get
```

Setting the cache executable's identity explicitly is essential: an inherited
Lake identity deliberately cannot substitute for a different executable.
The bundled native `leantar` remains selected through the official prefix.
The QEMU cache recipe remains a verified fallback. A newly selected cache route
must have its own actual result; the earlier completed 9,031-file QEMU retrieval
is not evidence that this specific native cache command has run.

## Formal validation commands

Wrap the **whole project command directly**; do not put `check.sh` inside
`lake env`, which injects a `LEAN` selector rejected by incremental checking.
The per-program shell launcher preserves the fresh checker's private LEAN_PATH.
Use a clean isolated candidate with stable inputs and separately owned outputs.
Retain the accepted command recorder, exact argv, actual outcome and complete
logs. Partial attempts never combine into a successful full check.

```sh
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- ./check.sh --fresh --jobs 1 --candidate HEAD
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- ./check.sh --candidate HEAD
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- env LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- lake env python3 scripts/test-proof-audit.py
python3 -B ../work-state/tooling/pinned_native_toolchain.py -- ./check.sh --verify-candidate HEAD
```

These are sequential gates, not an unconditional script: preserve the fresh
record before replacing it; perform the already-required non-repairing artifact
assessment before a repairing guard; run regression only after its prerequisite;
obtain both independent formal review outcomes; and perform final verification
immediately before acceptance. README.md and the acceptance checklist contain
the complete conditions, incident boundaries, and chapter-order requirement.

There are three separate concurrency controls:

- `check.sh --fresh --jobs 1` starts one external compiler process at a time.
- The helper's `LEAN_NUM_THREADS=1` bounds Lake's ordinary build-worker pool;
  the standard compiler job waits for its child before releasing that worker.
  It does not bound every Lake OS thread or arbitrary custom target.
- A real `lean -j1 ...` or `lean --threads=1 ...` argument selects one internal
  Lean CLI worker. `LEAN_NUM_THREADS` does not select that CLI setting.

To change the Lake pool setting deliberately, place `env LEAN_NUM_THREADS=N`
**after** the helper's `--`; a value set only before the helper is overwritten.
For an explicit standalone Lean invocation, pass `-j1` after `lean`. Propagating
such a choice through every checker/Lake compiler invocation would require a
separately selected launcher or command configuration. The current launcher
and running fresh4 inputs have not been changed to do that.

Earlier notes describing this environment value as "one Lean thread" overstated
the internal CLI bound. Preserve their actual recorded commands and results,
and interpret the setting as above. The pinned source assessment and a bounded
successful `FirstOrder` compilation with explicit `-j1` are recorded in
`../validation/1033-native-environment/concurrency-and-mmap-assessment.md` and
`explicit-j1-firstorder-probe.json` in that same evidence directory. The probe
produced the same `.olean` bytes as its foundation check. Its timing under
uncontrolled concurrent conditions does not establish a causal speedup.
No concurrency increase or working RSS limit follows merely from startup.

## Exact scope and limitations

The shim handles only `readlink` for `/proc/self/exe` or
`/proc/<actual getpid()>/exe`, only when an explicit absolute expected path
equals the kernel-provided in-memory `AT_EXECFN`. Launchers execute a real
payload by an absolute pathname; arbitrary symlink/relative/deleted-executable
semantics are outside this adapter's intended contract. Unrelated children
with an inherited parent identity fall through to the real syscall.

Lean's actual startup passes a valid writable buffer. Null-buffer and zero-size
errors are retained; arbitrary invalid non-null pointers are not made safe by
this userspace library. No other readlink path, other process lookup, procfs
interface, RSS report or permission is replaced. In particular, the pinned
runtime tolerates unavailable `/proc/self/statm` by reporting zero; the adapter
does not repair or fabricate RSS accounting. Do not claim that RSS-based limits
are accurately enforced in this environment.

The shim and loader are explicit runtime inputs to the ordinary trusted local
toolchain. This is not a proof of the C runtime, operating system, compiler or
emulator. The official compiler/kernel code and formal axiom policy remain
unchanged. The helper verifies specified executable/source/shim hashes and its
wrappers, not every library byte; preserve the verified distribution and stable
inputs. The current project does not enable `leanir`/postponed compilation;
additional native tools need an explicitly checked launch route if later used.
