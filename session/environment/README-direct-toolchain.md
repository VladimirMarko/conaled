# Recreate the direct Lean/Lake environment

The user made Nix optional in `../requirements/REQUEST-direct-toolchain-041.md`.
The Lean and dependency pins and all formal acceptance gates still apply.
This directory contains authored recovery helpers; downloaded binaries and
ordinary build/cache outputs are deliberately outside the durable source payload.

## Exact distributions

Use the original official Lean release, which includes the matching Lake:

- URL: https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst
- Size: 594481375 bytes
- SHA256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`
- Extract into `pfds/toolchains/`, producing `lean-4.35.0-linux/`.

For this workspace's absent process filesystem, use the standard QEMU Linux
user-mode executable from the official Debian package:

- URL: https://deb.debian.org/debian/pool/main/q/qemu/qemu-user-static_7.2+dfsg-7+deb12u18+b3_amd64.deb
- Size: 62603724 bytes
- SHA256: `c3e3ba2bd87f8c5b9a5da5ef21b5a3b82d7c63b89dd448d9ddaa4eabc5b6e402`
- Extract only `./usr/bin/qemu-x86_64-static`, using `dpkg-deb --fsys-tarfile`
  and `tar -xOf` or an equivalent safe archive reader.
- Place it at `pfds/toolchains/qemu-7.2-deb12u18/qemu-x86_64-static`, executable.
- Extracted executable SHA256:
  `8f2e8d5017b23a877fdf52e4021e6348bb5ad92306dd0d0615159ab6276da442`.

Check the exact byte sizes and SHA256 digests before extraction. These are
workspace extractions, not system package installations. The original Lean
distribution remains unchanged. No mount, global binary-format registration,
compiler patch, preload hook, or change to access permissions is involved.
See `direct-toolchain-041.json`, `qemu-lean-smoke-041.json`, and
`qemu-lean-feasibility-041.md` for the actual provenance and runtime investigation.

## Profile and ordinary commands

From the restored `pfds` directory:

```sh
python3 session/environment/make-direct-toolchain-profile.py
python3 session/environment/run-direct-toolchain.py --describe
python3 session/environment/run-direct-toolchain.py -- lean --version
python3 session/environment/run-direct-toolchain.py -- lake --version
```

The profile copies the genuine small `lean`, `lake`, and `leanir` executables
byte for byte to regular `*.real` files and launches them through QEMU. All
other release contents are referenced unchanged. Regular files preserve the
profile root when the guest queries its own executable path. Each entrypoint
is wrapped because a child `execve` does not automatically remain in emulation.

The environment launcher scopes `PATH`, `LD_LIBRARY_PATH`, `LEAN_SYSROOT`, the
two cache paths, `TMPDIR`, and `LEAN_NUM_THREADS=1` to the invoked command.
It does not change the caller's home, project sources, dependency pins, Lean
options, or stock verification script. `--describe` is read-only and returns
the environment and actual launcher/executable identity hashes. `--workspace`
can explicitly select the recovered `pfds` directory when testing a snapshot.

The recorded CLI tests accept a valid theorem with no axioms and reject a
false theorem with Lean's type mismatch. The Lake test compiles, links, and
runs a native executable whose output is `42`. These checks establish the
toolchain path, not formal project acceptance. Their test sources and complete
red/green outputs are adjacent to this file.

## Pinned dependencies and cache

Restore every dependency at its exact `lake-manifest.json` revision. The
record in `direct-dependencies-041.json` identifies all nine clean repositories.
Use `pfds/dependency-store-041/<package>/` and give each candidate a private
`.lake` directory whose `packages` symlink points to that store. Keep each
project's `.lake/build` and verification records private. Do not run `lake update`.

From `pfds/import-correction-r3`, with `PFDS_ROOT` set to the absolute restored
`pfds` directory, initialize the shared dependency cache once:

```sh
python3 "$PFDS_ROOT/session/environment/run-direct-toolchain.py" -- lake build @mathlib/cache
python3 "$PFDS_ROOT/session/environment/run-direct-toolchain.py" -- lake env \
  "$PFDS_ROOT/toolchains/qemu-7.2-deb12u18/qemu-x86_64-static" \
  "$PFDS_ROOT/dependency-store-041/mathlib/.lake/build/bin/cache" get
```

The cache executable also queries its own path, so it is explicitly launched
through QEMU. Lake supplies its normal source search environment. Native cache
downloads and decompression retain the pinned implementation and normal flags.
Inspect the cache command's actual exit status and dependency cleanliness;
an incomplete cache operation is not a successful formal check.

Run the stock candidate check and immediate final verification through the same
environment launcher in the appropriate clean isolated checkout. README requires
a fresh check after tooling changes; the first full check in this recovered
environment therefore uses the recorded runner's `full RUN_ID --fresh` route,
which invokes stock `./check.sh --candidate HEAD --fresh --jobs 1`. This does
not reuse or populate project outputs; the pinned dependency caches are reused.
The recorded validation runner preserves full/focused lock discipline and
terminal evidence for either stock mode. Its `verify` route reads the mode from
the named full record and passes no fresh/jobs flag to the stock verifier.
Both independent review axes must still pass on the same candidate before it
can be accepted. Historical interrupted validations remain inconclusive.
