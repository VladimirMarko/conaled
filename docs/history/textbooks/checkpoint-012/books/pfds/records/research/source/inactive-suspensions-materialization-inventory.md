# Inactive suspension candidate: source-retirement inventory

Assessor: `/root/inactive_materialization_inventory`.
Observed on 2026-11-03, with the complete byte inventory taken at
04:32:44.493462–04:32:46.594754 UTC and a final clean-HEAD observation at
04:33:57.180680 UTC. This is a bounded read-only operational investigation,
not an independent formal review or implementation loop.

## Finding and scope

The source materialization at
`/workspace/scratch/ca9a61d0bf30/validation-suspensions-r3` is recoverable from
its exact saved Git reference. Subject to root's fresh process/lock and identity
checks, its source files could be retired while retaining all its ordinary
outputs separately and restoring them to this same path later. The inventory
does not establish that such an operation has occurred, that current processes
are absent, or that a future stock guard will reuse every artifact.

This read-only assignment performs no retirement; root decides after actual
process/lock and identity checks. The user already authorized local work and
recoverable operational housekeeping. This report introduces no request for
additional user permission and no acceptance approval.

Only the named inactive checkout, its saved refs/checkpoint metadata, the
requested current status, and the earlier reappearance report were inspected.
Neither running compiler closure nor any process was inspected or changed.
The historical review-ch01 copies and archive001 were not opened or modified.
Their earlier unexplained reappearances remain recorded, without attributing
an actor or mechanism or repeating their removal.

## Exact source identity

| Property | Observed value |
| --- | --- |
| HEAD | `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` |
| Branch and matching ref | `refs/heads/pfds/suspensions-review-r3` |
| Git status, including nonignored untracked files | Empty |
| Tracked files | 1,648 |
| Tracked modes | 1,645 at `100644`; 3 at `100755` |
| Source bytes | 88,154,576 |
| Allocated bytes in source files | 91,783,168 |
| Source link counts | All 1,648 equal 1 |
| Git blob and executable-mode comparisons | Every tracked file matched HEAD |
| Aggregate source SHA256 | `d9884169d69d90ec67b6177cebab96679915d508b223da2b5a0de14262086038` |

The aggregate is SHA256 of lexicographically path-sorted records, each encoded
as `path`, NUL, mode, NUL, decimal byte length, NUL, file SHA256, newline.
Source modes use the literal Git modes above. Every file's device, inode, mode,
link count, size, nanosecond mtime and ctime were stable before/after its read;
all captured identities were checked again at the end of the inventory. These
checks establish the observed snapshot, not a promise about later mutation.

Git administration is in
`conaled/.git/worktrees/validation-suspensions-r3`, with common directory
`conaled/.git`. The checkout's 89-byte Git pointer has SHA256
`8fa05842c82ade4fc2a132f85abd083838f3304825ce4931034c7162041f2c54`.
It is Git administration, not an ordinary output to transplant into a new
worktree. Git should create the correct pointer during recovery.

Retiring these source files could reclaim approximately 91.8 million allocated
bytes, plus some directory/administration overhead. This is not a guarantee of
free space at the time of a later operation and is not a replacement for the
reviewed output-migration reserve preflight.

## Private ordinary outputs

`validation-suspensions-r3/.lake/build` is a real private directory, with no
symlink or multiply linked file inside it. All 452 files are regular, mode
`0644`, link count 1.

| Property | Observed value |
| --- | --- |
| Build files | 452 |
| Logical bytes | 53,857,483 |
| Allocated file bytes | 55,132,160 |
| Aggregate SHA256 | `dbb475ab91363ba77f3afd414c203c2a593f96b42dcc92f3baba31f99070dcc4` |
| `ir` files | 132 |
| `lib` files | 320 |
| Suffix counts | 64 `.c`, 192 `.hash`, 4 `.json`, 64 `.ilean`, 64 `.olean`, 64 `.trace` |

The build aggregate uses the same record encoding as the source aggregate,
with checkout-relative `.lake/build/...` paths and literal mode `0o644`.
Each of the 64 trace paths has all six corresponding siblings: `.olean`,
`.olean.hash`, `.ilean`, `.ilean.hash`, `.c`, `.c.hash`. This is structural
completeness only. I did not execute the stock guard or recompute Lake's hashes,
and I make no artifact-validity or future cache-hit claim.

The four setup JSONs are part of the 452-file inventory and must not be dropped:

| Path below `.lake/build/ir/` | Bytes | SHA256 |
| --- | ---: | --- |
| `Applications/Probability/HeavyTail.setup.json` | 1,847,913 | `a3f13a5b79b378b4ece1a37490c9ec842c3770e9de6a5be4f1014c1164835ee3` |
| `Applications/Progress/Examples.setup.json` | 467,741 | `80d96ed892b02dbfc6f73a6478a2e228e676f641d21a9345886d75740d34c795` |
| `Applications/Progress/Processors.setup.json` | 467,578 | `954c350c6530badad01936deac8089017cd97db196754d97d81ea0e314fcca2a` |
| `Applications/Progress/Streams.setup.json` | 467,416 | `34ae0f64d8af99bdc39338f63aa3d0fc073cfa8df5efc535cdfafce24acf9801` |

Their project import paths name this exact `validation-suspensions-r3` checkout;
their external dependency paths name `conaled/.lake/packages`. No alternate
candidate checkout path occurs among their absolute import paths. Recreate the
same checkout path before returning these bytes. Do not rewrite paths or traces
to make a different checkout consume them.

The observed build root identity is device 27, inode 3546098, mode 16877,
link count 4, size 4096, mtime_ns and ctime_ns 1793659150546665420. The `.lake`
root is device 27, inode 3543676, mode 16877, link count 4, size 4096,
mtime_ns and ctime_ns 1793666841584152612. A same-filesystem rename would permit
root to check preservation of directory identity as well as every member hash;
no rename has been performed by this assignment.

## Other local material that must be accounted for

The `.lake` directory also contains four config files, totaling 1,491,189
logical bytes and 1,503,232 allocated file bytes. Each is regular, mode `0644`,
link count 1. Preserve them with the build instead of treating build alone as
the complete local Lake material:

| Path | Bytes | SHA256 |
| --- | ---: | --- |
| `.lake/config/1/lakefile.olean` | 727,328 | `53b3efe9eab9dfd3e764797b57e3f09e86659001b53b859f4b1e37a2f7e26b28` |
| `.lake/config/1/lakefile.olean.trace` | 180 | `ec72a5f1a424ed022f79142aa6b592cbd6f363a659d2a457aa6c44a113772b2c` |
| `.lake/config/5/lakefile.olean` | 763,384 | `e35486da0ecf6b1ca6fc62cd3cd7f64186471e039791162586aea7da61960547` |
| `.lake/config/5/lakefile.olean.trace` | 297 | `a0293d2d61ce2abced65d5595e61028dc9b279ddf2bd4885300351e40529b3ea` |

The config traces name `mathlib` at index 1 and `proofwidgets` at index 5.
Both record leanHash `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and platform
`x86_64-unknown-linux-gnu`. No inference of validation follows from those strings.

`.lake/packages` is the sole symlink observed in this checkout. Its literal
target is `/workspace/scratch/ca9a61d0bf30/conaled/.lake/packages`, 54 bytes,
target-text SHA256
`b5f7fa6d3308837f81c41071c9ad99d8b14d6fac22e3c4f1c198fa67661956fe`.
Preserve or recreate the link itself without following it into the protected
shared dependency tree. I did not inspect or modify that target tree.

The only other ignored file outside `.lake` and the Git pointer is
`scripts/__pycache__/lake_integrity.cpython-313.pyc`, 9,337 bytes, mode `0644`,
link count 1, SHA256
`64530244ee42f6bdafb58eda2e48d93c819181dc671b748f09c50da03795ef2b`.
It is reproducible Python bytecode rather than a Lean build artifact, but a
literal preservation operation can retain it too; do not silently overlook it.

No `.lake/verification.json` exists in the inspected checkout. Thus there is
no success record to preserve or reuse. The candidate remains unaccepted.

## Pins and durable source references

| Tracked file | SHA256 |
| --- | --- |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `76966dfb4ea744d75d4bbe20ed3a6c576a17145d23f36ba44c4422673c51b04f` |
| `lake-manifest.json` | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |
| `flake.nix` | `0dc6835949ecc2a9e28e9fff16aeb4fa46eca74d1a92132d9a3a236974409f37` |
| `flake.lock` | `8489579a33350261a210f64e54d9442fece9c04fedf7ce8e6c5543010471238f` |

Both checkpoint037 and checkpoint038 manifests retain
`refs/heads/pfds/suspensions-review-r3` at exact HEAD a3feaff above, with no
symbolic target. The inspected manifest identities are:

* `validation/checkpoint037-manifest.json`: SHA256
  `956ba3a7ef2c462c320e2f319be8d70a534e62db05e2c72457e0a60234a02b3b`.
* `validation/checkpoint038-manifest.json`: SHA256
  `e1e95d82cddb170410c27c7959e05cb3475d29f0c0998da1e89a5458ef32a35a`.

The inspected checkpoint038 creation record reports actual restore success,
exit 0, 76,229,695 bytes and archive SHA256
`900c983bee0498f113bcc9ac73a5730f061044c434066422e070b535bbc0aa01`.
Its successful upload receipt identifies
`libfile_6e5dfd7dcc908191b0d7a51d89e3801b`. These are retained source/ref recovery
evidence, not a new restoration test by this assessor. The source checkpoint
excludes ordinary build outputs; a local output stash alone would not survive
loss of the whole workspace. Any separate durable output archive should retain
that distinction and confer no candidate approval.

## Concrete preservation and recovery prerequisites

1. Root must freshly verify exact clean a3 HEAD/ref, all source identities and
   modes, every output/config identity, symlink target, complete extra-file
   inventory and absence of a new verification record. Check actual host
   process users and relevant locks before any mutation. A read-only snapshot
   several minutes earlier cannot establish current inactivity.
2. Use a new dedicated inactive location for this exact candidate's material.
   Retain the complete `.lake` directory, including build, config and the
   dependency symlink itself, without traversing the link. Retain the small
   ignored Python bytecode if the action promises literal preservation of all
   non-source material. Record exact source/destination paths and per-file
   hashes before and after, and durably record the move before source retirement.
3. Remove only the now-recoverable inactive source worktree through ordinary
   Git worktree handling. Retain `pfds/suspensions-review-r3` unchanged and
   verify its exact object after the operation. Do not touch the active 901 or
   10023 checkouts, shared dependencies, historic reappeared copies, or any
   acceptance/review result.
4. To recover locally, recreate
   `/workspace/scratch/ca9a61d0bf30/validation-suspensions-r3` from the retained
   `pfds/suspensions-review-r3` reference and verify exact a3 HEAD and clean
   source/modes/pins before restoring the retained material. Refuse to overwrite
   a new or divergent path/output. Return the whole original private `.lake`
   material to its original location and compare all member hashes and link
   targets. Do not rewrite setup paths, traces or sidecars, and do not fabricate
   a verification file.
5. Resume the existing gate sequence only when its accepted predecessor and
   normal resource preflight permit. This candidate still requires its own
   stock full build, exhaustive audit, matching verification record, retained
   independent Standards/Spec continuations, and immediate final verification.

This proposal is preservation and later reattachment of one inactive candidate's
own outputs. It transfers no outputs to a different candidate, asserts no
accepted donor, and does not invoke or replace the separately reviewed
accepted-output migration procedure. No new cache policy, resource setting,
hash exception, proof assumption or gate exception is proposed.

Root must stop and reconcile rather than apply this plan if the named checkout
is active, its identity changes, the source destination already exists, an
unaccounted file appears, a package link resolves differently, any output/config
hash changes, or the exact recovery reference is unavailable. This assignment
ran no compiler, guard, candidate verifier, test, archive extraction, remote
tool or cleanup; its sole written artifact is this report.
