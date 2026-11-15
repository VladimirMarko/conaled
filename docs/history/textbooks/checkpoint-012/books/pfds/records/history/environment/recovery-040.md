# Environment recovery investigation for checkpoint 040

The restored repository remains clean at `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
No compiler, Lake build, candidate gate, proof audit, installer, or remote write was run by this investigation.

## Observed environment

`nix`, `nix-store`, `direnv`, `lean`, `lake`, and `elan` are absent from PATH.
`/nix`, `/proc`, `/proc/self/uid_map`, and `/dev/fuse` are absent.
The benign namespace capability probe `unshare --user --map-root-user true`
exited 1 with `unshare: cannot open /proc/self/uid_map: No such file or directory`.
This records the observed failure; it does not infer a particular host implementation or cause.

The previous environment record used a genuine Nix 2.35.4 binary under `/nix/store`
and required approved elevated execution. Current writable roots do not include
`/nix`; no out-of-root creation or escalation was attempted here.

## Official restoration routes

The [Nix 2.35.4 binary installation manual](https://nix.dev/manual/nix/2.35/installation/installing-binary.html)
describes single-user installation into `/nix`, using privilege to create that directory
when needed. It does not supply a direct arbitrary-prefix binary installer.

The [local store manual](https://nix.dev/manual/nix/2.35/store/types/local-store.html)
supports a physical store beneath a chosen root, while preserving logical `/nix/store`
paths. Building and executing from such a chroot store requires Linux mount and user
namespaces. The observed namespace probe failure prevents establishing that supported
route in this environment. No mount, namespace, sandbox, or host configuration was changed.

The manual also permits changing the logical store path, but doing so loses the default
Nix binary substitutes and can require rebuilding the entire tool closure. That is not
an established cache-preserving restoration route. No alternate-store build was begun.
The [source installation page](https://nix.dev/manual/nix/2.35/installation/installing-source.html)
points to building Nix from its repository; no source bootstrap was attempted.

All three official manual pages were fetched successfully with curl, so this record does
not claim general network failure. A GitHub release-tag API query returned 404; no binary
identity was inferred from it. The accompanying JSON retains source hashes, tool/path
observations, the exact namespace diagnostic, and the untouched repository identity.
Downloaded documentation is reproducible temporary input under `session/tools/` and is
excluded from recovery archives by the existing checkpoint policy.

## Consequence

No supported workspace-only restoration of the required Nix development environment
was established. Required formal validation needs a conventional permitted Nix installation
or an environment with the documented namespace facilities. This is a tooling blocker,
not a failed theorem, successful build, or candidate acceptance. The project instructions,
version pins, proof obligations and full-gate requirements remain unchanged.
