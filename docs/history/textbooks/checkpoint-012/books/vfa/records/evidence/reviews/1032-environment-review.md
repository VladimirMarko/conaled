# #1032: scoped QEMU environment review

Reviewer: `/root/environment_options`, 2026-11-03.

**Disposition: clear within the setup and recovery-instructions scope; no
unresolved findings. This is not formal Standards/Spec approval of the VFA
candidate, a completed project validation result, or chapter acceptance.**

## Scope and inspected identities

The VFA candidate remains `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, with fixed
review base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. This review covers the
external launcher, its setup evidence, and the VFA-specific recovery recipe.
The supplied guide's ADWH candidate and checkpoint confer no VFA acceptance.

| Inspected file | SHA-256 |
| --- | --- |
| `tooling/pinned_toolchain.py` | `a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47` |
| `tooling/README.md` | `968a1c6d0df5be47ec2bd1d93256854d8031526828fd526f296d6612e7a9ac27` |
| `validation/1032-qemu-environment/setup-summary.json` | `55c574a8a9760f87f14dbe316e41236572d38721e0a30e9091849220dc6a1a2a` |
| `validation/1032-qemu-environment/launcher-smoke.json` | `953682c1c23ba6d2a6acc35d610788210f9e77751ddfbd343f8fbaa957de680c` |
| `validation/1032-qemu-environment/qemu-acquisition.json` | `d4375dbe48d721856e544b6d21dbfbbbe930bdf50ade8355651be359b0dc2945` |

Paths above are relative to `work-state/`. The retained guide hash is
`ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1`.
The adapter is exactly the 5,436-byte Appendix A Python block from the user
attachment; its syntax and declared digest match. The summary's guide,
adapter, and instruction hashes match the inspected files.

## Findings

- The copied executable layout, supported Lake installation override, library
  paths, and child launchers agree with the pinned Lake installation-discovery
  source. Both official executable copies remain under one overlay root.
- The recipe wraps the checker directly. It does not inject `lake env` around
  the whole checker, which would conflict with its incremental `LEAN` guard.
  Shell launchers preserve the fresh checker's generated private `LEAN_PATH`.
- All eight recorded smoke commands have individual exit status zero. They
  include exact Lean/Lake version output, the overlay prefix and Lake child
  path, and actual theorem compilation through both bare and Lake-child Lean.
  Both test theorems report no axioms. The embedded smoke-source hash matches.
- The nine dependency identities reported in the summary match every manifest
  pin. This is a comparison of retained evidence, not a new dependency-cleanliness
  observation during an active build.
- The acquisition record distinguishes the host keyring trust basis, signature
  result, signed-index binding, package digest, and extracted executable digest.
  The README preserves that distinction and does not claim a package installation.
- The summary explicitly records cache build as running at its observation time,
  with a null return, fresh3 not launched, and no chapter acceptance. Its status
  is a dated observation, not a current process guarantee.

## Formal gates and recovery

The README preserves fresh validation, separate guarded incremental validation,
the managed `ProofAudit` prerequisite, all four audit regression outcomes, both
independent formal review axes, immediate final candidate verification, and an
acceptance checkpoint before Sort. It preserves the fresh record before a later
check replaces it and retains the historical unknown fresh1/fresh2 outcomes.
Cache execution is explicitly emulated inside Lake's environment. The current
one-job/one-thread setting is accurately recorded; no additional gate is imposed.

The recovery recipe retains exact acquisition identities, complete adapter source,
and relocation instructions. Generated absolute-path launchers are regenerated;
no prior conversation or other checkpoint is required. Suspect-artifact
preservation and existing incident limits remain applicable.

## Limits

QEMU is part of the execution environment; no emulator-correctness proof is
claimed. The adapter checks three executable digests and wrapper contents, not
every runtime/library byte. The verified original distribution and stable-input
discipline remain relevant. I inspected records and source and compared hashes;
I did not rerun the smokes, signature verification, dependency acquisition, or
formal builds, and did not independently rehash the full distribution. The only
file written by this assignment is this review record.
