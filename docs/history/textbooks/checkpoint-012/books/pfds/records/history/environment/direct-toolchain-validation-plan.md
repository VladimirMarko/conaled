# Direct toolchain: validation and dependency restoration plan

Recorded 2026-11-03. Read-only investigation for the root coordinator, governed
by `session/requirements/REQUEST-direct-toolchain-041.md`. This report does not
record a successful compiler invocation, build, proof audit, candidate
verification, independent review, or acceptance. Its author ran no compiler or
build and changed no project source, check script, resource limit, or tracker.

## Authorization and immediate conclusion

The user's current instruction is:

> The Nix shell is defined for consistency and convenience, but is not strictly
> necessary for continued development. Can you get the required Lean and Lake
> versions without it?

This supersedes the launch-through-Nix requirement in `conaled/AGENTS.md` and
the corresponding README instructions. Compiler and dependency pins, isolated
clean candidates, unchanged build and audit gates, independent reviews, final
candidate verification, local tracking, and durability obligations remain.

The stock check scripts contain **no Nix or direnv enforcement**. A correctly
functioning official Lean 4.35.0 distribution on `PATH` can supply their Lean
and Lake commands without changing those scripts. Elan and direnv are not
required to invoke an already extracted official distribution.

There is, however, a separate **observed native-runtime blocker** in this
workspace. The coordinator's genuine probes, preserved in
`session/environment/direct-toolchain-smoke-041-r2.json`, give:

| Command | Exit | Actual result |
| --- | ---: | --- |
| `lake --version` | 0 | `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)` |
| `lean --version` | 1 | `error: failed to locate application` |
| `lean --print-prefix` | 1 | `error: failed to locate application` |

These probes used the verified distribution's `lib/lean` and `lib` in a scoped
`LD_LIBRARY_PATH`, its `bin` on `PATH`, and `LEAN_SYSROOT` pointing to its root.
The earlier shared-library loader failures are separate diagnostics in
`session/environment/direct-toolchain-041.json`. The later result must not be
described as a Nix failure or as an operational Lean compiler. Installation and
Lake version discovery succeeded; source compilation has not been established.

## Why the observed Lean startup fails

Exact upstream v4.35.0 source establishes this sequence:

1. `src/shell/lean.cpp` forwards directly to `lean_main`.
2. `src/util/shell.cpp` invokes `init_search_path()` at lines 315–321, catches
   any exception, and returns 1. CLI option parsing starts only afterward.
3. Exported `lean_init_search_path`, defined by
   `Lean.Util.Path.initSearchPathInternal`, calls
   `initSearchPath (← getBuildDir)`.
4. `getBuildDir` obtains `(← IO.appDir).parent`.
5. The Linux implementation of `IO.appPath` in `src/runtime/io.cpp` forms
   `/proc/<getpid()>/exe` and calls `readlink`. Failure returns precisely
   `failed to locate application`. That implementation has no environment
   fallback.

`LEAN_SYSROOT` is supported by the separate `Lean.findSysroot` API and Lake's
installation discovery. It does **not** override `getBuildDir` or Lean's native
startup. `LEAN_PATH` is incorporated only after the failing `getBuildDir` call.
`--root` sets the package root used to calculate an input module name; it is
parsed too late and is not an installation-root option. `--print-prefix`
also calls `getBuildDir` directly. Consequently none of these settings repairs
the observed failure in the official Linux compiler.

The supporting agent is separately checking alternative official entrypoints.
This investigation found no supported native CLI or environment option that
avoids the startup dependency on a functioning process executable path. Do not
patch the compiler, synthesize process paths, substitute fake version output,
or change checks to make this condition appear successful. The conditional
commands below are for a runtime in which actual Lean startup works.

## Required tools and supported environment configuration

The checked-in compiler pin is `leanprover/lean4:v4.35.0`. The official matching
release contains Lake; the observed Lake version above matches the expected
release commit prefix `eb6cafb`. Do not replace it with a current/nightly Lake
or derive acceptance solely from its version string.

The coordinator reports the official Linux archive as 594,481,375 bytes with
SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The installed distribution root is:

`/workspace/scratch/b566cace4ed6/pfds/toolchains/lean-4.35.0-linux`

| Requirement | Evidence and use |
| --- | --- |
| POSIX `sh` | `check.sh` changes to its directory and execs `python3 scripts/check.py`. |
| Python 3.11 or newer | `lake_integrity.py` imports stdlib `tomllib`; installed Python is 3.12.14. No third-party Python package is imported by these gates. |
| Git | Candidate and all dependency clean-HEAD checks use Git; installed Git is 2.51.1. |
| curl | Pinned Mathlib cache code recommends at least 7.84; installed curl is 8.5.0. |
| Lean and Lake from the same distribution | The checker invokes both `lake env lean` and bare `lean --run` for output hashing. |
| Bundled `leantar` | Pinned Mathlib finds it through `lean --print-prefix` plus `bin/leantar`; this also requires real Lean startup. |
| Native link tools | Lake prefers the distribution's `clang` and `llvm-ar` when present. System `cc`/`gcc` exist. No tool replacement is required based on inspection alone. |
| tar and zstd | Present for archive preparation, not proof-acceptance criteria. |

The flake additionally declares elan, direnv, and ripgrep. Elan selects and
installs toolchains; direct extraction removes that need. Direnv supplies the
now-optional launch environment. Ripgrep assists source work but is not called
by the stock acceptance scripts.

Use narrowly scoped supported settings, with all new writable locations under
the allowed workspace:

| Setting | Supported meaning and proposed value |
| --- | --- |
| `PATH` | Prepend the exact distribution's `bin`; retain ordinary system tools. |
| `LD_LIBRARY_PATH` | Coordinator's observed working library discovery uses `<distribution>/lib/lean:<distribution>/lib`. Record this separately from Lean startup success. |
| `LEAN_SYSROOT` | `<distribution>`; supported by `Lean.findSysroot` and Lake, but cannot fix native Lean's `IO.appPath` failure. |
| `MATHLIB_CACHE_DIR` | `/workspace/scratch/b566cace4ed6/pfds/runtime-cache/mathlib`; explicitly supported by the pinned Mathlib `Cache/IO.lean`. |
| `LAKE_CACHE_DIR` | `/workspace/scratch/b566cace4ed6/pfds/runtime-cache/lake`; explicitly supported by the pinned Lake. An empty value disables its system cache. |
| `TMPDIR` | If the normal temporary directory is not writable, use a created workspace temporary directory. The stock integrity helper uses Python `TemporaryDirectory` without an explicit parent; fresh mode instead uses the checkout's `.lake`. |
| `LEAN_NUM_THREADS` | Preserve `1`, as in the interrupted full/focused runs, while retaining one full plus one focused job maximum. |

Neither `HOME` nor `CODEX_HOME` should be reassigned. Both cache implementations
also support XDG-based defaults, but their dedicated variables avoid moving
unrelated application state. `LAKE_CONFIG` is a supported path override if
configuration placement becomes necessary; no configuration change is needed
from this inspection.

Do not set caller `LEAN` for the incremental gate: `check.py` explicitly rejects
that override. It also discards caller `LEAN_PATH`. It is normal for `lake env`
to configure its own child-process Lean variables; that does not authorize
setting `LEAN` in the outer check environment. Do not set `LEAN_GITHASH` to
influence identification.

Do not blindly set `LAKE_HOME` to the release root. In the fallback discovery
path that variable describes Lake's source-build layout, whose executable and
libraries lie under `.lake/build`. A normal joint release installation is
recognized separately through the running executable path. A passing
`lake --version` alone does not establish that all installation/configuration
discovery needed by `lake env` and build commands will work.

## Stock checks that remain unchanged

`check.sh`, `scripts/check.py`, `scripts/lake_integrity.py`,
`scripts/lake-output-hashes.lean`, `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json` are byte-identical at restored main `76d77a1`, prerequisite
candidate `901f734`, and signed-potential candidate `d24c443`.

The incremental candidate gate performs all of the following:

- Requires the candidate to equal checked-out HEAD and the checkout to be clean,
  including untracked nonignored files. Integrated Lean sources must be tracked.
- Requires every manifest dependency to be a Git checkout, clean, and at its
  exact manifest revision.
- Rejects forbidden source constructs, missing local imports, import cycles,
  and public-entrypoint omissions.
- Requires the Mathlib cache directory
  `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib`.
- Runs `lake env lean --version` and compares the version to `lean-toolchain`.
- Guards existing project outputs, disables Lake artifact cache restoration
  and writes, and calls `lake --no-cache --rehash build +<module>...` for the
  complete module inventory.
- Guards the resulting outputs again, without repair, then executes the real
  `ProofAudit.lean` on every invocation, including an otherwise cached build.
- Rechecks candidate, dependencies, and compiler before atomically writing
  `.lake/verification.json` on success.

The hash guard runs the real pinned `Lake.computeBinFileHash` through
`lean --run scripts/lake-output-hashes.lean`; it does not trust replaceable hash
sidecars. It requires the standard project source and output layouts and
`enableArtifactCache` unset or false. Its existing limitation is unchanged:
it does not authenticate dependency caches or make shared writable build
outputs concurrency-safe.

`./check.sh --verify-candidate HEAD` compares the saved successful record to
the current identity and compiler. It neither recompiles nor reruns the audit;
run it immediately before actual acceptance after the required reviews.
`--jobs` is supported only with `--fresh`; do not invent a Lake build `-j`
option. Installing the same pinned distribution does not itself require a
new source/checker change or waive any candidate gate.

## Pinned dependency and cache restoration

Use the existing manifest, not `lake update`. The exact required revisions are:

| Package | Git revision |
| --- | --- |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
| Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

The ordinary preparation command, once runtime startup works, is
`lake exe cache get` in a checkout with the unchanged manifest. It retrieves
pinned sources and Mathlib's ordinary compiled dependency cache. The pinned
Mathlib cache implementation checks the Lean toolchain and shared manifest
entries. Its native decompressor is the distribution's `leantar`, discovered
through actual Lean prefix output. Network access must reach the normal source
and cache endpoints through the permitted connector/network route.

The coordinator's planned dependency staging location is
`/workspace/scratch/b566cace4ed6/pfds/dependency-store-041`. Preserve the manifest's
`.lake/packages` layout as seen from each project checkout. Confirm all nine
Git heads and clean status after restoration; retain manifest/source identities
with the preparation record.

The shared download-cache directory is supported by Mathlib's process-tagged
download names. This does not make simultaneous mutation of dependency build
outputs safe. Finish dependency preparation before starting consuming builds,
then keep a shared prepared dependency tree stable. Alternatively, give each
checkout its own pinned dependency checkouts while sharing only the supported
download cache. Keep each candidate's project `.lake/build` private. If a
consumer would rebuild shared dependencies, serialize it rather than let two
consumers write the same outputs.

No unselected Library archive is needed or authorized for this plan. The
historically mentioned build-cache archive is not an attached input. Restore
from official pinned dependency sources and their ordinary cache instead.
Restored dependency outputs remain external trusted inputs under the existing
project policy; they are not proof-acceptance evidence for either local
candidate. Never copy a prior candidate's verification record into place.

## Resuming the two recorded jobs when the runtime is usable

The old wrappers have the obsolete absolute root
`/workspace/scratch/ca9a61d0bf30` and an obsolete Nix executable. The coordinator
may adapt session-owned runners under the current workspace for the user-
authorized direct environment; no repository check script needs modification.

The full candidate is the clean isolated checkout `import-correction-r3` at
`901f734161920a76f3b399a575805b9a1d31e971`. Its command core remains:

```sh
env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD
```

The focused development candidate is `signed-potential` at
`d24c443ba22019613b1ce646d6eed7279c791ad6`. Its eleven-target command core is:

```sh
env LEAN_NUM_THREADS=1 lake build \
  Applications.Resources.Potential \
  Applications.Resources.SignedPotential \
  Applications.Resources.BinaryCounter \
  Applications.Resources.SymmetricCosts \
  Applications.Resources.RandomAccess.End \
  Applications.Resources.FIFOContracts \
  Examples.PotentialAccounting \
  Examples.FIFOContracts \
  Examples.RandomAccessEndCosts \
  Examples.SignedPotential \
  Examples.PotentialTransport
```

The focus remains development evidence only. Its passing result cannot replace
the prerequisite's full check or the eventual full gate and reviews for the
signed-potential work.

Preserve these recording properties from the old wrappers:

1. Acquire `active-validation/full-build.lock` for a full job and
   `active-validation/focused-build.lock` for a focus. Allow at most one of
   each, and no concurrent source/dependency mutations affecting either.
2. Use new run/record/log filenames. Retain the interrupted full-r2 and
   focused-r2 records exactly as historical terminal-unknown evidence.
3. Record actual command argv, selected environment, checkout and exact HEAD,
   start/end timestamps, owner, terminal exit, post-run clean state, and raw
   log digest. If interrupted with no terminal result, record that uncertainty.
4. For a focus, preserve queued/start/end hashes of the targets and recursive
   local imports plus `lean-toolchain`, Lake files, and flake files. Reject
   mixed-input results. The old focus wrapper exits 2 if inputs changed.
5. Save a copy and digest of `.lake/verification.json` only if the stock full
   gate actually created it. Its existence alone is insufficient: require
   terminal success, exact identity, and unchanged recorded inputs.
6. Adapt `run-import-verify-candidate-r3.py` to reference the new successful
   full-run record. It currently names `import-footprint-901f734-full-r2.json`;
   that historical interrupted record cannot support verification. Preserve
   its checks that the retained verification record equals the live record,
   the actual full command was the stock gate, and the candidate is clean.
7. Run the stock verification immediately before the coordinator's acceptance
   decision, after applicable independent Standards and Spec review. A runner
   must continue to record `acceptance: false`; it does not make the decision.

No new full or focused build was launched by this investigation.

## Primary evidence

Local evidence: `conaled/AGENTS.md`, README development/build/audit sections,
the four stock check files, flake and Lake files, old full/focused/verification
runners, `session/research/validation-concurrency.md`, the current user request
record, and the coordinator's direct-toolchain smoke record.

Exact versioned upstream source read directly during this investigation:

- [Lean native runtime](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/runtime/io.cpp)
- [Lean executable entrypoint](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/shell/lean.cpp)
- [Lean startup](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/util/shell.cpp),
  SHA-256 `502eaa752396cdff5bb448833a63be54cbbcbb3d36881eb10e235c04c64c0832`
- [Lean path initialization](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Util/Path.lean),
  SHA-256 `52cf9aa41a82db18d0d3c93bf6257d064f773af9e62b8b43be89ce1b0e00055f`
- [Lean shell options](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Shell.lean),
  SHA-256 `bbfcf01a93bcb9ca3f4d1264d3ad9890f3a6384dbbc949f5bf3cc286c0ec2225`
- [Lake installation discovery](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/Config/InstallPath.lean),
  SHA-256 `fc5bc3094122fb0384c01cb4d70bf0bd0e84744ec340affadf04b09c88088277`
- [Lake environment](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/Config/Env.lean),
  SHA-256 `bc976a2f9ae4806676adb3a29c83828161767f5eeae496f8ebbc0af5c6304739`
- [Pinned Mathlib cache I/O](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/IO.lean),
  SHA-256 `3f7ee518fef40145242bb0415d21e11a3cb5f25720fe7e87321cf741692217a5`
- [Pinned Mathlib cache requests](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/Requests.lean),
  SHA-256 `e10ab3332fbe21f8295fe7bec8dded3ab3aba7cced1cea41d60e16c2c3162381`

The extracted distribution also supplies the exact Lean/Lake source, which
was inspected for the environment-variable definitions. No research source
was compiled, installed as a replacement, or used to alter the checker.
