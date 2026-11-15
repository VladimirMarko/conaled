# Native Lean with an explicit CLI worker setting

This is the separate native configuration prepared under local #1035. It runs
the unchanged pinned Lean and Lake executables with the already accepted
executable-path shim. Its Lean wrapper prepends `-j1`. Its Lake wrapper does
not receive that option. The original native and QEMU helpers and overlays
remain available.

The operational review, completed validation and checkpoint records determine
whether this configuration has been accepted. This guide alone is not an
acceptance record. No environment check establishes a VFA chapter's acceptance.

## Reconstruct the pinned installation

Restore a checkpoint into a new directory, run its `restore.py`, and retain
`work-state/` beside `conaled/`. Follow [NATIVE.md](NATIVE.md) for the exact
official-distribution recovery, authenticated identities, scoped readlink-shim
construction, host restrictions and dependency setup. The user authorized this
non-Nix route; Lean and dependency versions must still match the repository.

Required existing inputs under the recovery root are:

| Input | Required identity |
| --- | --- |
| `toolchains/lean-4.35.0-linux/bin/lean` | SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |
| `toolchains/lean-4.35.0-linux/bin/lake` | SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1` |
| `work-state/tooling/native_app_path.c` | SHA-256 `0798e7e0d6b71510dd3f68778af1e487aaa9093af5f7cb1666c22b8605f5fd76` |
| `toolchains/native-compat/libconaled_app_path.so` | SHA-256 `8bb82334a2888e37a18b657a16f498cba239aaf3935bf24cc5b59728f6df5a18` |

The complete official distribution is required, including its libraries; the
two executable files alone are insufficient. The expected versions are Lean
4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
5.0.0-src+eb6cafb. Dependencies remain those in the captured `lake-manifest.json`,
including Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

From the recovery root, generate and inspect the new overlay:

```sh
python3 -B work-state/tooling/pinned_native_j1_toolchain.py --describe
python3 -B work-state/tooling/pinned_native_j1_toolchain.py -- lean --version
python3 -B work-state/tooling/pinned_native_j1_toolchain.py -- lake --version
```

The helper creates `toolchains/lean-4.35.0-native-j1/`, copies the unchanged
official Lean/Lake payloads into its `libexec/`, and constructs its own `bin/`
launchers. It verifies the four listed inputs and the copied executables. It
refuses unexpected existing launcher contents or symlinks. On relocation,
reconstruct this generated overlay from the retained source and official
installation; do not edit or reuse wrappers containing old absolute paths.

Only the accepted readlink shim appears in the generated `LD_PRELOAD` setting.
The mmap/MADV_RANDOM experiment is not part of this configuration. Each wrapper
supplies the exact current payload path to the shim. Its narrow executable-path
behavior and limitations remain those documented in NATIVE.md; it does not
provide unavailable procfs RSS enforcement or expose denied procfs contents.

## Concurrency and command behavior

There are three separate controls:

| Control | Scope |
| --- | --- |
| `./check.sh --fresh --jobs 1` | At most one external project compiler job in the fresh checker. |
| `LEAN_NUM_THREADS=1`, set by the helper | Lake's ordinary task pool, including its standard synchronous compiler jobs. |
| Initial `-j1` in the new Lean wrapper | Lean CLI internal worker setting for supported invocations. |

These controls do not constrain every OS thread or every custom Lake target.
The wrapper places `-j1` before the caller's arguments, preserving `--run`
script argument boundaries. Later explicit compiler options can override the
initial setting; the supported acceptance commands supply no later thread
override. Lake itself receives only its caller's original arguments.

The outer helper clears inherited Lean selectors, `LD_PRELOAD` and
`CONALED_SELF_EXE`, and sets this overlay's sysroot, PATH and library paths.
Wrap the whole checker directly. Its later private `LEAN_PATH` is retained by
the generated compiler wrapper. Do not wrap the checker inside `lake env`:
that can introduce a `LEAN` override rejected by incremental mode.

## Project validation

Use a clean isolated checkout at the exact formal candidate, with dependency
sources at the manifest revisions and no scheduled writers to its inputs.
Project output directories must belong only to that checkout. Recreate the
pinned dependency cache through the installation guide if it is absent; source
checkpoints intentionally exclude caches and installed toolchains. The earlier
successful cache retrieval used the retained QEMU route; this guide does not
claim a cold native-j1 download has been tested.

With `work-state/` beside that checkout, run:

```sh
python3 -B ../work-state/tooling/pinned_native_j1_toolchain.py -- ./check.sh --fresh --jobs 1 --candidate HEAD
```

Retain the actual completed result, full log and matching fresh verification
record. Follow the existing incident handoff to assess and preserve suspect
incremental artifacts before any repairing guard invocation. Then run the
separate guarded incremental check and retain its distinct evidence:

```sh
python3 -B ../work-state/tooling/pinned_native_j1_toolchain.py -- ./check.sh --candidate HEAD
```

The outstanding recovery acceptance sequence also requires the managed
`+ProofAudit` prerequisite, the audit regressions, both independent formal
review axes, and the final candidate-record verification immediately before
acceptance:

```sh
python3 -B ../work-state/tooling/pinned_native_j1_toolchain.py -- env LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit
python3 -B ../work-state/tooling/pinned_native_j1_toolchain.py -- lake env python3 scripts/test-proof-audit.py
python3 -B ../work-state/tooling/pinned_native_j1_toolchain.py -- ./check.sh --verify-candidate HEAD
```

Run the regression only after its managed prerequisite succeeds. Investigate
unexpected rebuilds or integrity invalidations through the existing local
incident workflow, reestablishing affected guarded evidence where required.
Full validation through this configuration needs a complete new attempt;
partial old and new logs cannot be combined into success. Operational acceptance
and its complete uploaded checkpoint must precede a new formal attempt. Chapter
order and all source/proof policies remain unchanged.

## Measurements and their limits

The exact original Squares source, including `import Lean`, compiled with
explicit `-j1` and the accepted readlink-only route in 2.4449 seconds. A preceding
experiment with `-j1` plus MADV_RANDOM took 6.9525 seconds. Both produced the
same `.olean` SHA-256 as the earlier native and QEMU runs:
`133589a2adff7fcb278b1bc79fd1fd8f2bcf9315cfae28d6d801a5efa099ac4c`.
The earlier native sample without an explicit CLI worker setting took
136.8226 seconds.

These were sequential observations under uncontrolled cache and concurrent
load conditions. They do not establish that thread selection or memory advice
caused the timing differences, nor a whole-project speed guarantee. Peak RSS
was higher in the fast samples: 1,625,588 KiB for the readlink-only control,
1,477,064 KiB with advice, versus 844,264 KiB in the older native sample. No
reduced memory requirement or safe increase in process concurrency follows.
The simpler configuration was selected because the useful observed result did
not require adding the mmap interposer.

Raw identities, command lines, resource counters, normal child exits and output
comparisons are retained under `../validation/1035-mmap-random-prototype/`.
The prototype and its passing boundary fixtures remain historical experiment
evidence, not production runtime inputs or formal chapter credit.

For fallback, retain [README.md](README.md), `pinned_toolchain.py`, and the
user-supplied guide at
`../environment-guides/user-supplied-lean-lake-qemu-guide.md`. The original native
route remains `pinned_native_toolchain.py`; it does not supply the explicit
Lean CLI worker argument described here.
