# Current environment after Monitor correction

Use tooling/ACTIVE-NATIVE.md and tooling/UNIFIED-NATIVE.md. Main conaled and
isolated vfa-summation-validation are clean at eae9e110adc7ba1cc28386448a6deef23e406c13.
The old isolated/provisioning project roots remain frozen at4adc; old-descendant
quiescence remains unknown. Shared compiler/profile and dependency inputs are
unchanged. No setup/cache/profile writer is running.

The cf0 full fresh failed at937 after936 successes; all records are preserved.
The new candidate adds only Mathlib.Order.Lattice to Monitor. Its complete source
passed, and all116 actual diagnostic modules completed with actualAPI/kit exit0.
The complete record is1040-focused-summary.json. Candidate-specific scope is
675selectors and the same3932installed families;
all954localsources, dependency-header comparisons and ninecleanpins were checked.
No new acquisition was required. See validation/1040-candidate.json,
1040-cache-scope.json,1040-environment-ready.json and1040-focused-remaining2.
A new eae9 full fresh is running, session30015, records in
validation/1002-candidate-eae9e11-monitor-fresh1. No new formal gate or chapter
acceptance is claimed.
Compressed offline compiler/cache download seeds were reclaimed after this
completed run;1040-compressed-download-reclamation.json preserves their exact
inventory/hashes. Installed compiler/profile, dependency source/artifact trees
and private outputs remain untouched. Reacquire seeds if later reinstall needs
them; this does not change the empty-restore recipe.
Historical paths, setup results and permission statements below describe earlier
hosts only and do not authorize operations in the current host.

# Development environment and recovery

Recorded 2026-11-02 for the local Verified Functional Algorithms formalization.

## Repository and toolchain

- Initial conaled commit: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Main checkout: `/workspace/scratch/0c54f2db1fdf/conaled`.
- Follow `AGENTS.md` and the development/build sections of `README.md`.
- Use the checked-in Nix flake shell. Repository tooling and dependency pins
  were not modified by environment setup.
- Verified Nix: 2.35.4.
- Verified Lean: 4.35.0, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Verified Lake: `5.0.0-src+eb6cafb`.
- Verified direnv: 2.37.1.
- mathlib manifest revision: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Commands in this workspace

Run from the desired checkout. The execution sandbox cannot see the installed
Nix profile; use the approved escalated execution mode for these commands.
The newline inside `NIX_CONFIG` is intentional.

```bash
export PATH=/root/.nix-profile/bin:$PATH
export NIX_CONFIG='build-users-group =
experimental-features = nix-command flakes'
export LEAN_NUM_THREADS=1
nix develop --command lake build Examples.ComparisonPermutations
```

`direnv allow .` was run in the main checkout. Noninteractive commands can
continue using `nix develop --command ...` directly.

For committed acceptance in an isolated checkout:

```bash
export LEAN_NUM_THREADS=1
nix develop --command ./check.sh --candidate HEAD
LAKE_ARTIFACT_CACHE=false nix develop --command lake --no-cache --rehash build +ProofAudit
nix develop --command lake env python3 scripts/test-proof-audit.py
nix develop --command ./check.sh --verify-candidate HEAD
```

The managed `+ProofAudit` step is needed because the guarded command executes
`ProofAudit.lean` without producing the importable artifact used by the regression
fixtures. See `validation/1002-audit-regression-prerequisite.md`. Run the sequence
only after each preceding command succeeds, and complete both independent review
axes before the final candidate verification and acceptance.

Use one Lean worker in this 8 GiB environment. Four concurrent full-project
workers caused severe paging even without an OOM failure; reducing concurrency
improved observed progress in that attempt while preserving the same guarded
validation procedure. Later large imports still incurred substantial paging;
this is not a controlled speed comparison or a promise of normal performance.
See `validation/1002-build-restart.md`. Reassess concurrency from actual resource
evidence on a different machine, without changing proof/audit requirements.

Use `--fresh` when required by the repository's README. Preserve the resulting
`.lake/verification.json` and validation output with the review evidence.
Focused `lake build` is useful during development but does not replace the
guarded integrated build, exhaustive proof audit, or independent reviews.

Staging compiler output files such as `.olean` are reproducible intermediates.
Their hashes may be recorded as historical validation evidence, but these output
files are removed before checkpoint capture. Restore source checks using the
recorded commands; checkpoints preserve source and evidence, not build caches.

## Completed setup validation

- `nix develop --command lean --version`: passed.
- `nix develop --command bash -c 'lean --version && lake --version && direnv version'`:
  passed with the versions above.
- `nix develop --command bash -c 'direnv allow . && lake exe cache get'`: passed;
  8,687 cache files decompressed.
- All nine dependency checkouts were checked against `lake-manifest.json`;
  every revision matched and every dependency working tree was clean.
- No integrated project build or proof audit was run as part of environment setup.

## Historical initial dependency copy

The dependency tree is `conaled/.lake/packages`, approximately 7.1 GiB after
setup. It can be copied into a candidate's own `.lake` directory to avoid
re-downloading caches while keeping writable files independent:

```bash
mkdir -p /absolute/candidate/.lake
cp -a /workspace/scratch/0c54f2db1fdf/conaled/.lake/packages \
  /absolute/candidate/.lake/
```

Do not copy the main project's mutable `.lake/build` outputs into a candidate.
Do not use hardlinks or writable directory symlinks to share build outputs.
Reflink support was tested and is unavailable on this filesystem, so each
dependency copy uses about 7.1 GiB. There were about 25 GiB free immediately
after setup; check current capacity before creating more copies.

## Recreating setup after workspace loss

The repository's `flake.lock`, `lean-toolchain`, and `lake-manifest.json` own
the reproducible project pins. Restore the checkpoint's repository and local
ticket/review state, install Nix as appropriate for the replacement host, and
run the documented Nix-shell/cache commands. The machine-specific paths above
must be adjusted to the restored workspace.

For a fresh recovery, prefer creating the isolated candidate **before** fetching
its dependencies, so a second full generated cache is not deliberately created
in the main source checkout. From the clean restored main repository, after
installing the pinned development environment:

```bash
nix develop --command git worktree add --detach ../vfa-validation HEAD
cd ../vfa-validation
nix develop --command lake exe cache get
```

Then run the acceptance sequence above in that isolated checkout. Keep the main
checkout for source work; its own generated cache is not required merely to edit
files. Read dependency source and use actual completed dependency artifacts from
the isolated checkout when preparing protected staging checks. Do not share
writable project outputs, assume a historical main-cache path exists, or treat
a successful cache-download exit as proof that every artifact is present. The
ordinary full build remains required. The earlier copy recipe records the
initial setup and is an alternative only when the actual source cache is complete
and capacity permits; it is not a mandatory recovery step.

On this ephemeral root container, the official Nix 2.35.4 binary distribution
was downloaded from:

`https://releases.nixos.org/nix/nix-2.35.4/nix-2.35.4-x86_64-linux.tar.xz`

Its SHA-256 matched the official installer:

`ff66236d2f7e2a21f3350e73668e021ac6a8881ef277a38e16e952bfb22718c3`

The inspected installer was run with `--no-daemon --no-channel-add
--no-modify-profile --yes` and the same `NIX_CONFIG` above, after creating
`/nix`. It did not modify shell startup files. On a different host, choose the
installation mode supported by that host; the project still uses its pinned
flake shell.

The setup downloads under `toolchain-setup/` are reproducible intermediates.
They are not needed to restore source work, tickets, or review evidence.

## Cache coverage clarification during candidate validation

A bounded read-only follow-up on 2026-11-02 confirmed that the recorded 8,687
decompressed entries do not certify a complete Mathlib cache. The pinned
no-argument cache tool targets Mathlib.lean's import closure, but ordinary
missing cache entries can warn and still allow successful exit. No separate
raw download log was preserved, so the initial missing-entry count/cause is
not reconstructed from the setup note. The candidate subsequently compiled
Mathlib.Algebra.Homology.ShortComplex.Basic (job4309, 5.4s), whose artifacts
were absent from the inactive main dependency copy.

Main and candidate manifests were byte-identical, and all nine dependency
HEADs in both matched their pins during this follow-up. No dependency, cache,
compiler, or configuration change was made. This is consistent with the
existing requirement to complete the whole candidate build and audit; it does
not justify a restart or a fresh cache fetch while validation is active. The
pinned implementation evidence is in Cache/Main.lean (default root),
Cache/Requests.lean (ordinary misses versus failures), and Cache/Warning.lean
(missing-cache warning), under the mathlib checkout.


## 2026-11-02 08:50 UTC storage reclamation

Checkpoint 014's first restore smoke failed during severe disk pressure. Root
reclaimed uploaded local checkpoint copies 000–011 and the inactive main
Mathlib generated build directory only. Main package source and Git pins remain;
its compiled Mathlib outputs were absent immediately afterward but later partly
reappeared. Local ticket #1025 retains that unexplained inactive-path recreation;
it does not establish an active-cache inconsistency. The deliberately selected
cleanup did not touch the isolated cache or active gate. Future focused checks
must inspect actual available artifacts instead of assuming main is empty or
complete. The detailed independent path/ownership checks and actual free-space
observations are in validation/20261102-storage-cleanup.json. This is planned
reclamation of derived data, not a toolchain or source change.

## Later operational records

After checkpoint 016 was uploaded and verified, root retired only redundant local
copies 012–014, checking each full SHA256, size and Library binding first. Their
durable copies and all receipts remain available; local copies 015/016 were kept.
The returned checkpoint 000 and unexplained cache paths were not deleted again.
See `validation/20261102-checkpoint-local-retention.json`.

One bounded advisory pass requested `POSIX_FADV_DONTNEED` on 74,135 singly linked
regular files in the inactive main Mathlib build tree. It opened no active-cache
files and changed no file contents. The report records successful requests,
not reclaimed-page counts or a timing improvement:
`validation/20261102-inactive-cache-advisory.json`. Neither this advice nor the
inactive-path investigation substitutes for any build, audit, regression or
review gate. #1025 remains open and nonblocking under its recorded proportional
disposition unless concrete active-input or integrity evidence changes that.

## 2026-11-03 checkpoint035 recovery

The original host setup and its approval above are historical. In the restored
workspace `/workspace/scratch/83865511e965`, no Nix/Lean/Lake/direnv installation
is visible. The official Nix archive hash was verified; no installer was run.
Ordinary installation needs `/nix`, outside the writable roots. The documented
local-store namespace probe failed because `/proc/self/uid_map` is unavailable.
See `validation/1030-environment.json` for exact observations and limits.

Use the current `STATUS.md` as the resume entry point. No new formal validation
was launched, and no cached output or old process was restored. Establish a
permitted working Nix environment before the candidate gates; do not reinterpret
the historical escalated-command instruction as present access or approval.

## 2026-11-03 direct toolchain under the user exception

The user explicitly waived the Nix/direnv wrapper requirement when the correct
required tools are separately acquired. Read AMENDMENTS.md and
specs/1031-direct-toolchain-amendment.md. The official Lean4.35.0 Linux archive
was acquired, matched its official SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`,
and was extracted unchanged under `toolchains/lean-4.35.0-linux` in this workspace.
The distribution includes its matching Lake.

Direct startup needs explicit LD_LIBRARY_PATH to the distribution's lib and
lib/lean in this sandbox. With those paths, Lake reports5.0.0-src+eb6cafb, but
Lean exits1 with `failed to locate application`. Exact pinned source explains
that Linux startup reads /proc/<pid>/exe before processing options; /proc is not
visible here. LEAN_SYSROOT does not override that internal lookup. A read-only
version check outside the sandbox was rejected by the execution policy because
sandbox escalation is disabled. No binary modification or bypass was attempted.

Python3.12.14 satisfies the integrity helper's Python3.11+ requirement; Git2.51.1
and curl8.5.0 are available. This is a documented direct environment, not a claim
of reproducing every historical Nix package byte. No dependency fetch or formal
validation has run. See validation/1031-direct-toolchain.json for exact provenance,
individual smoke results, startup-source evidence, and the policy rejection.
The downloaded distribution is a reproducible setup intermediate and is excluded
from source checkpoints; the acquisition URL and digest are preserved.

## 2026-11-03 user-supplied QEMU route verified

The native process-path limitation is resolved for project execution by the exact
user-supplied QEMU adapter, without host permission or compiler-byte changes.
Use tooling/README.md and the adjacent complete pinned_toolchain.py. Actual bare
Lean, Lake, and Lake-child Lean version checks passed; two small theorems compiled
through both routes with no axioms. All9 dependency source revisions are clean and
match the manifest. Cache preparation and formal gates retain separate outcomes.
See validation/1032-qemu-environment/setup-summary.json and current STATUS.md.

The official distribution now lives under the recovery root's toolchains/ rather
than the scratch root. The earlier paths and failures remain historical. The new
Ubuntu signature/index/package/binary authentication chain and public verification
inputs are preserved. Regenerate overlay wrappers after a future relocation.


## Native alternative accepted under local#1033

The user explicitly requested alternatives to slow QEMU. Use the complete
`tooling/NATIVE.md` recipe, C source, native launcher and boundary tests. Native
operational candidate e41336d46dffd7bddd42b242a7ea7484a6055e43 passed both independent
axes and isolated reconstruction/runtime tests; root comparison and limits are
in validation/1033-native-environment/acceptance.json. The exact original QEMU
recipe remains unchanged as fallback. Current formal inputs/next action are in
STATUS.md. Runtime setup does not accept any chapter or waive a validation gate.
