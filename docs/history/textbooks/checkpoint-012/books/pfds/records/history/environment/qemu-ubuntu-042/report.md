# Ubuntu QEMU authentication — checkpoint 042 evidence

**Result: the guide's exact Ubuntu QEMU package and selected executable were independently authenticated on 2026-11-03.** This acquisition is complete and frozen. No emulator, Lean, Lake, or project gate was executed in this task; the active runtime was not changed.

## What was established

The trusted input was the host's installed **public** Ubuntu archive keyring, `/usr/share/keyrings/ubuntu-archive-keyring.gpg`. `gpgv` 2.4.4 verified the newly downloaded official `noble-updates/InRelease` with exit status 0 and a `VALIDSIG` record for fingerprint:

`F6ECB3762474EDA9D21B7022871920D1991BC93C`

The signature was dated **2026-11-03 12:40:55 UTC**. The authenticated release fields identify Ubuntu 24.04, suite `noble-updates`, codename `noble`, with release date **2026-11-03 12:40:01 UTC**. It advertises `Acquire-By-Hash: yes`; no `Valid-Until` field is present. The public keyring copy retains the observed trust input, rather than independently certifying that trust root.

The release's SHA256 section authenticated exactly one `universe/binary-amd64/Packages.xz` entry. The compressed index was downloaded using its signed by-hash URL, then checked for both digest and byte count. It contained one `qemu-user-static` stanza, for `1:8.2.2+ds-0ubuntu1.18`, architecture `amd64`. The package's signed SHA256 and size matched the guide before download, and the downloaded bytes matched those values. `dpkg-deb --fsys-tarfile` exited 0; a streaming tar reader copied only the exact regular member `./usr/bin/qemu-x86_64-static` into the task's excluded tools directory. Its hash and size also matched the guide. A header read identified a 64-bit little-endian x86-64 ELF; it was not executed.

| Object | Bytes | SHA-256 |
| --- | ---: | --- |
| Installed public Ubuntu archive keyring | 3,607 | `80a36b0a6de2f69f49d2df75ef473ccde121e9e190b9ea01d20a4f63778d5c31` |
| Downloaded signed InRelease | 126,125 | `5f4cbfd1daf09c5c6af3eeb67fe923b15010f28d9189b64995e2c0f68eec7b77` |
| Authenticated Packages.xz | 1,707,340 | `2dd82d93dc7fab28f67d5120aa122d8896b557ce4984995635a7dfff1353386d` |
| Authenticated qemu-user-static .deb | 14,709,858 | `5bb397f66063efa349f6fd5cb3b68cd96f29edd0994e4ba5115cf0859a716bf0` |
| Selected qemu-x86_64-static | 3,751,320 | `90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0` |

The observed signer, index digest, package version/digest/size, and executable digest/size all match the supplied guide. The current canonical index happened to match the guide's recorded digest; that is an observation about this snapshot, not a promise that a moving index will keep the same bytes.

## Official acquisition sources

- Signed release: <https://archive.ubuntu.com/ubuntu/dists/noble-updates/InRelease>
- Canonical index: <https://archive.ubuntu.com/ubuntu/dists/noble-updates/universe/binary-amd64/Packages.xz>
- Actual authenticated by-hash index download: <https://archive.ubuntu.com/ubuntu/dists/noble-updates/universe/binary-amd64/by-hash/SHA256/2dd82d93dc7fab28f67d5120aa122d8896b557ce4984995635a7dfff1353386d>
- Package URL taken from the authenticated stanza: <https://archive.ubuntu.com/ubuntu/pool/universe/q/qemu/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb>

`acquisition.json` retains the actual absolute command arguments, statuses, and textual outputs for each curl/gpgv/dpkg-deb invocation, as well as expected and observed hashes, sizes, release fields, selected archive member, and timestamps. The exact retained `Packages.xz` preserves the release-to-index-to-stanza chain; the selected stanza alone would not prove its membership in the signed index. All curl invocations completed with status 0. The signature verification and authenticated-cleartext extraction both completed with status 0 and the expected `VALIDSIG` fingerprint.

## Reproduction from retained public inputs

Run these commands from the recovered PFDS workspace. The output home and authenticated cleartext remain task-local in the excluded tools directory:

```sh
mkdir -p session/tools/qemu-ubuntu-042/recheck-gpgv-home
gpgv --homedir session/tools/qemu-ubuntu-042/recheck-gpgv-home \
  --keyring "$PWD/session/environment/qemu-ubuntu-042/ubuntu-archive-keyring.gpg" \
  --status-fd 1 \
  --output session/tools/qemu-ubuntu-042/rechecked-Release \
  session/environment/qemu-ubuntu-042/InRelease
```

Require exit status 0 and the fingerprint above. From the authenticated cleartext, select the SHA256 entry for `universe/binary-amd64/Packages.xz` and compare its digest and size with the retained compressed index. Decompress that verified index and select the exact `Package`, `Version`, and `Architecture`; `package-stanza.txt` and `package-metadata.json` are retained derived views. Authenticate a new release if using newly downloaded moving metadata. Download the signed stanza's `.deb` filename, verify its signed SHA256 and size, then extract and hash only the selected executable. The compact acquisition record describes the actual checks performed in this task. These recovery instructions are a reproduction recipe, not a claim that an additional recovery run occurred.

## Proven versus reported in the guide

The package authentication chain above was performed here. The guide's separate historical acquisition execution, Lean/Lake smoke tests, cache build and retrieval, Nix experiments, and project validation outcomes were not repeated or imported. This task supplies no performance comparison between QEMU versions and no finding about the best thread count. The guide's suggested four-thread gate is a separate runtime choice requiring evaluation in the active project environment.

The guide names a different workstream's checkpoint 039 (`local/adwh-continue-2026-11-03`, archive digest starting `5ac95084`). Its Library references were not accessed. Those restoration details and formal-status claims do not establish anything about this PFDS workstream. The attachment used here has SHA-256 `ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1` (34,828 bytes).

## Retention and scope

`session/checkpoint.py` explicitly omits session path components named `tools`, while retaining the present `session/environment/qemu-ubuntu-042/` evidence. Accordingly, the `.deb`, extracted QEMU binary, extracted release cleartext, and temporary GPG home are under `session/tools/qemu-ubuntu-042/` and excluded from durability checkpoints. This evidence directory retains the small signed InRelease and public keyring, the exact 1.7 MB compressed index, selected package metadata, this report, the acquisition record, and an input manifest with their hashes. The index is deliberately retained so the authenticated chain can be checked offline after the repository moves.

No system package was installed. No active toolchain/profile, launcher, project source/ref, or running validation job was modified. No native compatibility adapter was authored, selected, or integrated in this task. The authenticated Ubuntu executable is an available candidate; its acquisition does not select it as the active runtime or establish runtime equivalence with the existing QEMU configuration.
