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
LEAN_ARTIFACT_CACHE=false nix develop --command lake --no-cache --rehash build +ProofAudit
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
