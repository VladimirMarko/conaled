# Pinned Lean environment through QEMU: setup result

The QEMU route passed all 12 environment checks on 2026-11-03. Bare Lean and
Lake's child Lean used the same unchanged official Lean 4.35.0 executable and
successfully compiled the same Init-only proof file. Both theorems reported
no axiom dependencies. This result enables project validation; it does not
establish a project build, exhaustive audit, independent review, or chapter
acceptance result.

## Authority and preserved source

This setup applies the numbered project route from the user-supplied
`conaled-nix-workaround-lean-lake-4.35.0(2).md`, retained byte-for-byte as
`supplied-guide.md`. Its SHA-256 is
`ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1`.
The user authorized the Nix-shell exception. All other source, build, audit,
review, and local durability requirements remain in force.

The actual source is the FDSA checkpoint 0065 recovery, with the isolated
Chapter 1 candidate at `work/conaled-ch01-review`:

- Candidate: `07e480f6ec9958d4975bb90151005b84f2907614`.
- Tree: `2b089ee7b3e0dea370001df6e78deedc0eb398d8`.
- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- All nine dependency checkouts match the existing manifest and are clean.

The unrelated checkpoint 039 referenced in the supplied guide was not restored
or used as this task's source. `supporting-tools-and-source-pins.json` and
`post-smoke-source-verification.json` retain before/after source identities,
configuration digests, dependency checks, and actual supporting-tool versions.
The candidate and its tracked configuration remained unchanged and clean.

## Authentication and acquired artifacts

The existing official Lean distribution remains at
`bootstrap/direct-lean/lean-4.35.0-linux`. Its previous download and release
authentication records remain in `../direct-environment-20261103/`.

QEMU was obtained from Ubuntu's official HTTPS archive without installing the
package. Fresh `noble-updates/InRelease`, dated 2026-11-03 12:40:01 UTC, was
verified by `gpgv` using the host's trusted
`/usr/share/keyrings/ubuntu-archive-keyring.gpg`. The valid signing fingerprint
was `F6ECB3762474EDA9D21B7022871920D1991BC93C`. Its SHA-256 stanza authenticated
the downloaded `universe/binary-amd64/Packages.xz`, whose exact package stanza
authenticated `qemu-user-static` version `1:8.2.2+ds-0ubuntu1.18` for amd64.

| Input | SHA-256 |
|---|---|
| Packages.xz | `2dd82d93dc7fab28f67d5120aa122d8896b557ce4984995635a7dfff1353386d` |
| qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb | `5bb397f66063efa349f6fd5cb3b68cd96f29edd0994e4ba5115cf0859a716bf0` |
| qemu-x86_64-static | `90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0` |
| Official bin/lean | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |
| Official bin/lake | `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1` |

The package and extracted emulator are under `bootstrap/qemu-user`. Extraction
copied only the regular `qemu-x86_64-static` and copyright members from the
package payload; no installer or maintainer script ran. The signed release,
compressed index, selected package stanza, and a byte-identical copy of the
observed public host keyring are retained here. `qemu-acquisition.json` contains
the complete commands, exit codes, signature output, input identities, and
timestamps; `acquire_qemu.py` records the acquisition procedure.

No host permissions, tracing settings, mounts, namespaces, or system
installation paths were changed. The earlier native Lean and Nix failures
remain historical evidence. The successful route executes the unchanged
compiler through QEMU user mode, which supplies the guest executable path.

## Adapter and layout

The durable adapter is `../../tooling/pinned_toolchain.py`, SHA-256
`8bc54deea672a0ff7928d1de8f839ee97963349c4d97cae13e4ac2257b06ec3f`.
The original Appendix A adapter is retained as `adapter-guide-original.py` and
matches the supplied hash
`a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47`.
`adapter-layout.diff` shows the entire adaptation: workspace derivation uses
`parents[3]` because this adapter is under `work/fdsa-control/tooling`, the
toolchain directory is `bootstrap`, and the existing official distribution is
under `bootstrap/direct-lean`. Executable pins and launcher behavior are
unchanged from the supplied source.

The generated overlay is `bootstrap/lean-4.35.0-host`. Its Lean and Lake
payloads are byte-identical copies of the official executables. Both launchers
explicitly invoke the authenticated QEMU executable; libraries, sources,
headers, and other bundled tools point to the original distribution.

The adapter clears inherited toolchain selectors, uses Lake's supported
installation override, supplies the official shared-library paths, and keeps
runtime files and caches within the workspace. It defaults to
`LEAN_NUM_THREADS=1`. An explicit different value must be placed after the
adapter, for example `-- env LEAN_NUM_THREADS=4 COMMAND ...`.

## Actual checks

`run_smoke.py` completed at 2026-11-03 15:47:50 UTC. All 12 commands exited 0;
their complete outputs and timestamps are in `launcher-smoke.json`.

- `--describe` created and verified the overlay; its result is separately
  retained in `launcher-environment.json`.
- QEMU reported `8.2.2 (Debian 1:8.2.2+ds-0ubuntu1.18)`.
- Bare Lean and `lake env lean` reported the identical full version string,
  Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
- Both routes' `--githash` output matched that exact commit; both
  `--print-prefix` outputs identified the generated overlay.
- Lake reported `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
- Lake's child environment selected the overlay's `bin/lean` and `bin/lake`.
  Stock Lake populated its child `LEAN_GITHASH` with the actual compiler hash;
  the adapter did not inject or fabricate that identity.
- Both routes compiled `smoke/QemuKernelSmoke.lean`, including an induction
  proof, and printed no axiom dependencies for either theorem. Both generated
  `.olean` files are 6,824 bytes with SHA-256
  `fbf279c5128799661a3f3087d27f139d4da4944e9061ae0c522fce3af38bb980`.

This assignment did not invoke a dependency cache download, a project build,
the project audit, or final candidate verification. Those executions belong
to the coordinating agent and require their own terminal evidence.

## Invocation and recovery

From `work/conaled-ch01-review`, wrap the entire intended command:

```sh
python3 ../fdsa-control/tooling/pinned_toolchain.py --describe
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lean --version
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lake env lean --version
```

The coordinator's cache route, not run by this setup assignment, is:

```sh
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lake build cache
python3 ../fdsa-control/tooling/pinned_toolchain.py -- lake env \
  /workspace/scratch/6bb268f9336f/bootstrap/qemu-user/bin/qemu-x86_64-static \
  /workspace/scratch/6bb268f9336f/work/conaled-ch01-review/.lake/packages/mathlib/.lake/build/bin/cache get
```

Use the actual new workspace paths after relocation. Preserve the adapter,
guide, authentication inputs, and acquisition records in durability checkpoints;
the large official distribution and extracted emulator can be reacquired from
their authenticated sources. Regenerate the overlay in the new workspace:
its generated shell launchers contain absolute paths, and the adapter
intentionally refuses to overwrite unexpected existing launcher contents.
Keep old acquisition and validation records as historical evidence; record a
new acquisition attempt separately instead of overwriting these records.
