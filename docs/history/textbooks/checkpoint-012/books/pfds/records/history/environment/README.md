# Development environment bootstrap

Repository: `conaled`, initial commit `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

The container initially had no Nix, direnv, elan, Lean, or Lake on PATH.
The official installer was downloaded from `https://nixos.org/nix/install`.
It verified and installed the Nix 2.35.4 binary closure into `/nix/store`.
The final single-user profile activation failed because the container runs as
root and has no `nixbld` group. No shell profiles were modified.

The installed **real Nix binary** is usable directly:

```sh
/nix/store/8lza1b8nnci8lmm4q68p0l33pg975s0q-nix-2.35.4/bin/nix \
  --extra-experimental-features 'nix-command flakes' \
  --option build-users-group '' --option sandbox false \
  develop --command lean --version
```

Run from the repository root. The two options accommodate this root container,
which has neither Nix build users nor usable sandbox namespaces. They do not
change the checked-in flake, dependency versions, or repository verification.
Use the same invocation followed by `lake exe cache get`, `lake build MODULE`,
or the required `./check.sh` acceptance command. Network and Nix store writes
required the execution tool's approved elevated mode in this environment.

Smoke check passed with:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

On a normal machine with Nix configured, the repository's documented
`nix develop --command ...` or `direnv exec . ...` is sufficient. The container
bootstrap options are not requirements for such a machine.

`nix-install.log`, `lean-version.log`, and `lake-cache.log` record the bootstrap.
This note does not establish that the project build or proof audit passed.

`lake exe cache get` subsequently exited successfully. It downloaded and
decompressed 6,559 missing cached files and decompressed 2,383 already-cached
files. All nine dependency checkouts are clean and their HEADs exactly match
`lake-manifest.json`, as recorded in `summary.json`.

Additional verified tool versions: Lake 5.0.0-src+eb6cafb, elan 4.2.1,
Git 2.54.0, and direnv 2.37.1. No repository source, configuration, index,
or commits were changed by environment bootstrap.

