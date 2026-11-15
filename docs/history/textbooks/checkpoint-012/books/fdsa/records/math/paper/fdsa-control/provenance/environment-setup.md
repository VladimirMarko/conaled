# conaled environment setup

Date: 2026-11-02. Checkout baseline: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

The starting environment had no Nix, direnv, elan, Lean, or Lake on PATH.
The official Nix installer was downloaded from `https://nixos.org/nix/install`
and retained as `install-nix.sh` in this directory. It selects Nix 2.35.4
for x86_64 Linux and checks the release archive SHA-256
`ff66236d2f7e2a21f3350e73668e021ac6a8881ef277a38e16e952bfb22718c3`.

Nix was installed using its single-user installer, without adding a channel
or modifying shell startup files. This disposable environment runs as root;
the installer warned that root installation is not supported but completed
successfully. The explicitly empty build-users group permits the local
single-user store. No conaled flake, toolchain, or dependency pins were changed.

## Commands

From the repository root, use the repository's required flake shell:

```sh
/root/.nix-profile/bin/nix \
  --extra-experimental-features 'nix-command flakes' \
  --option build-users-group '' \
  develop --command lean --version

/root/.nix-profile/bin/nix \
  --extra-experimental-features 'nix-command flakes' \
  --option build-users-group '' \
  develop --command lake exe cache get
```

In this task's execution sandbox the download/setup calls require escalated
execution; un-escalated public network requests fail at the supplied proxy.
No permission or source-policy check was disabled.

The shell smoke check passed and reported:

```
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

The pinned Nixpkgs revision is
`26f4107e47e3ad0ffd0db220469ba83b6f6d96e8`. The pinned Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Validation status

Toolchain smoke check: passed. Dependency and cache retrieval: passed (exit 0),
with 9,031 cache files downloaded and decompressed. Lake reports
`Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.

Every dependency checkout was checked against `lake-manifest.json`: all nine
Git revisions match and all nine checkouts are clean. A Git diff check found
no changes in `flake.nix`, `flake.lock`, `lean-toolchain`, `lakefile.toml`, or
`lake-manifest.json`.

This record does not claim that conaled itself has passed a build or proof
audit. Use the repository's `check.sh` acceptance commands after implementation.

The untracked file
`docs/history/algorithm-design-haskell/.checkpoint-233.zip.n7UlkJ` was present
at the initial checkout inspection; it has not been edited or removed by
the environment setup task.
