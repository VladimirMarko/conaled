# Direct pinned toolchain: acquisition and runtime diagnosis

Recorded 2026-11-03. User exception: `user-exception.md`.
This is environment work, not formal acceptance or an independent final review.

## Acquired exact inputs

The official Lean v4.35.0 x86_64 Linux archive was downloaded and extracted
inside the workspace. Its 594481375 bytes match the publisher's release API
size; SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`
matches the publisher-provided digest. The release includes matching Lake.
See `lean-release.json`, `lean-release-api.json` and `extracted-binaries.json`.

All nine dependencies are distinct clean Git checkouts at the exact revisions
in the unchanged candidate `lake-manifest.json`. The acquisition log records
each init/remote/fetch/checkout and the subsequent SHA/cleanliness checks.
See `dependency-acquisition.json` and `dependency-acquisition.log`.

The host's Python 3.12.14 satisfies the unchanged checker's Python >=3.11
requirement (`tomllib`). Git 2.51.1 and curl 8.5.0 are recorded. The repository
pins for Lean/Lake, Nixpkgs and all dependencies remain untouched; no program
version or Git identity was fabricated. The user permits the direct environment
without Nix. Mathematical scope and every acceptance gate remain unchanged.

## Actual smoke results

The release bin directory was first on PATH; LEAN_SYSROOT named the actual
release root; LEAN and LEAN_GITHASH were unset. The first smoke attempt failed
at dynamic-library discovery. A second attempt set LD_LIBRARY_PATH to the
actual release's lib/lean and lib directories, with no binary modification.

| Operation | Second attempt result |
| --- | --- |
| `lake --version` | exit 0: Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0) |
| `lean --version` | exit 1: error: failed to locate application |
| `lean --githash` | exit 1: same startup error |
| `lean --print-prefix` | exit 1: same startup error |
| Compile a scratch `import Lean` theorem using `Nat.add_zero` | exit 1: same startup error, before elaboration |

Complete command/output records are `toolchain-smoke.json` and
`toolchain-smoke-explicit-libraries.json`. The latter records only a successful
Lake version command, not successful Lake project execution or a Lean compiler
identity check. No dependency cache command, project build or proof audit was
started. No repaired attempt 4 was launched; the old full attempts remain
historical with their original unknown outcomes.

## Exact source explanation

The independently inspected official source at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` explains the observed failure:

1. `src/util/shell.cpp`, `lean_main`, calls `init_search_path()` before parsing
   CLI options. On an initialization exception it prints the error and exits 1.
2. That calls exported `lean_init_search_path`; release `Lean/Util/Path.lean`
   computes `getBuildDir` using `IO.appDir`, which obtains `IO.appPath`.
3. `src/runtime/io.cpp`, `lean_io_app_path`, unconditionally uses Linux
   `readlink("/proc/<getpid()>/exe", ...)`. On failure it returns the exact
   message `failed to locate application`. This branch has no environment,
   argv or configured-path fallback.
4. `LEAN_SYSROOT` is supported by the separate `Lean.findSysroot` and Lake
   discovery path; it does not replace this compiler-startup call.
   `--root` selects module/package naming, not executable discovery.

The same-process numeric-PID readlink probe returns ENOENT in this execution
environment; see `proc-executable-probe.json`. This is more precise than
inferring behavior solely from an absent `/proc/self/exe` alias. Source URLs
and byte identities are retained in `runtime-source-identities.json`.
The full compiler source snapshots and binaries are regenerable bootstrap
inputs outside the ordinary source checkpoint.

Independent investigation by `/root/recovery_environment` confirmed this
startup order and lack of a supported flag/config fallback. Root read the same
runtime implementation, shell initialization and shipped Lean path functions.
No compiler patch, interception, substitute identity, security-control change
or proof-policy change was made or selected.

## Next prerequisite and continuation

Use the exact stock release in an execution environment exposing the normal
kernel-provided `/proc/<own PID>/exe` to the compiler process. Nix is optional
under the explicit user instruction. Re-run the smoke checks before retrieving
Mathlib caches or starting the full guarded candidate check. This names the
currently established prerequisite, not a promise that all later steps pass.

Keep candidate `07e480f6ec9958d4975bb90151005b84f2907614`, original review base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, all fourteen paths, both frozen
requirement snapshots and SPEC-001/002/003/V001. After a full successful check,
both independent final review axes and immediate candidate verification are
still required. No chapter, appendix or shared unit is accepted.
