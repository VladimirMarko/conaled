# External environment

Use the exact repository commit in `STATE.json`. Read its `README.md` and
`docs/development.md` for the current compiler/dependency pins and check modes.
Use Nix/direnv when available. The user's existing native-route exception also
permits the source adapter in `native/` with the same pinned inputs.

## Native route

This adapter requires Linux x86-64, a glibc loader with per-program `--preload`,
Python 3.11+, and `cc` or `gcc`. Git, HTTPS download support and zstd are needed
for external acquisition. It downloads nothing. The adapter prefers the host compiler's glibc loader over a system compatibility
trampoline. Its `PINS.json` records the exact
official Lean distribution, selected binary hashes and project pin-file hashes;
its `prerequisite` is historical adapter provenance, not this seed's source base.
`NOTICE.md` preserves attribution and the adapter's verification boundary.

Reuse a matching complete official distribution. For a new installation, download
the `official_archive.url` from `native/PINS.json`, verify its exact byte length
and SHA-256, and extract it into a new external directory. Check the project pin
files against `project_files`. A mismatch needs investigation or an adapter
update; changing expected hashes does not establish compatibility. A locally
Nix-patched Elan installation may legitimately differ from the official archive.

Set these variables to actual absolute paths. Profile state must be new, outside
the project and seed, with an existing parent and no symlink components,
whitespace or colon.

```sh
CONALED_SEED="/absolute/path/to/seed"
CONALED_PROJECT="/absolute/path/to/conaled"
CONALED_TOOLCHAIN="/absolute/path/to/official-lean"
CONALED_PROFILE_STATE="/absolute/new/native-state"
CONALED_NATIVE="$CONALED_SEED/operations/native/native_profile.py"
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" prepare \
  --toolchain "$CONALED_TOOLCHAIN" --project "$CONALED_PROJECT"
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" verify \
  --project "$CONALED_PROJECT" --full
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" run \
  --project "$CONALED_PROJECT" -- lean --version
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" run \
  --project "$CONALED_PROJECT" -- lake exe cache get
```

Run focused `lake build ACTUAL_MODULE` through the same outer `run` boundary.
Do not set caller `LEAN`, `LEAN_PATH` or `LEAN_SRC_PATH`; Lake and the checker own
those paths. Keep installed tools, dependencies, profiles and build outputs out
of checkpoint payloads. The adapter supplies no command timeout or resource cap.

For native whole-library acceptance, create an independently owned clean detached
worktree at the actual candidate, retain its private project outputs and use only
a stable matching dependency cache. Set `CONALED_ACCEPTANCE_PROJECT` to that
checkout and `CONALED_CANDIDATE` to the exact commit. Run the whole checker directly:

```sh
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" run \
  --project "$CONALED_ACCEPTANCE_PROJECT" -- \
  ./check.sh --candidate "$CONALED_CANDIDATE"
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" run \
  --project "$CONALED_ACCEPTANCE_PROJECT" -- \
  ./check.sh --verify-candidate "$CONALED_CANDIDATE"
```

This direct route does not inherit the managed check-candidate wrapper's locks or
process cleanup. Keep one writer and inspect surviving processes after an
interruption. Never switch the acceptance checkout while a check is running.

The adapter's regression command is
`python3 -B operations/native/test_native_profile.py -v`. Set
`CONALED_NATIVE_TEST_TOOLCHAIN` and `CONALED_NATIVE_TEST_PROJECT` to the matching
existing installation and checkout to run its real-compiler tests. Without those
variables most tests are skipped; a short passing result is not full validation.
The tests do not establish whole-library mathematical acceptance.

Keep the existing ten-minute setup/troubleshooting budget and at most one targeted
retry for a concrete failure. Report the actual blocker when exhausted and
continue only work supported by the available evidence. This budget does not cap
mathematical compilation or authorize CPU, thread, memory or build-time limits.
