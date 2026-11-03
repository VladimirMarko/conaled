# Real Elan for the stock checker regression suite

This supplements `RECOVER-ENVIRONMENT.md`. Recreate its approved native Lean
profile and pinned dependencies first. Nix remains optional. This appendix is
needed because the unchanged `scripts/test-check.py` obtains a real selected
compiler path with `elan which lean` in its version-mismatch test.

The compiler and Lake still come from the exact official Lean 4.35.0 release.
Elan is only the genuine version-manager interface required by that stock test.
No project pin, test, timeout, compiler, active native profile or validation
controller is changed by the setup below.

## Provenance and observed result

The official release is Elan 4.2.4, commit
`227caca133724d5516bee25c2aeb3e609478f2d8`. The public release API is
<https://api.github.com/repos/leanprover/elan/releases/tags/v4.2.4>.
Its exact response and the tagged upstream README are retained under
`elan-4.2.4-provenance/`, together with their retrieval hashes.

| Artifact | Identity |
| --- | --- |
| Official archive | `https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz` |
| Archive size | 4,996,571 bytes |
| Archive SHA256, matched to official API digest | `42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63` |
| Extracted `elan-init` size | 13,452,832 bytes |
| Extracted `elan-init` SHA256 | `e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5` |
| Actual version output | `elan 4.2.4 (227caca13 2026-08-25)` |

The upstream README documents that `elan-init` is also the real Elan CLI,
selected by its invocation name, and demonstrates an `elan` symlink. We use
that supported entrypoint directly. This avoids the installer's self-copy
step, which uses Rust's own-executable lookup. It does not replace Elan with a
script or manufacture its output. The release's Linux executable is built for
musl despite the compatibility filename; no claim is made that the glibc
metadata adapter could repair its installer.

Actual local setup, link, selection and selected-compiler checks all returned
zero; see `elan-4.2.4-provenance/setup.json`. The selected wrapper resolved to
the already verified native profile and reported the exact Lean 4.35.0 commit.
These are setup results. They do not claim that any regression suite passed.

## Recover in a new workspace

Use a clean Bash shell with the normal prerequisites from the main runbook.
Set `PFDS_ROOT` to the newly restored workspace, not to a historical path.
Keep `elan-init` outside `ELAN_HOME/bin`: ordinary Elan startup cleans an
installer file at that location. These commands modify only task-owned paths.

```bash
set -euo pipefail
PFDS_ROOT=/absolute/path/to/restored-pfds
PFDS_ELAN_PACKAGE="$PFDS_ROOT/toolchains/elan-4.2.4"
PFDS_ELAN_STATE="$PFDS_ROOT/runtime-cache/elan-native-check-tests"
PFDS_ELAN_ARCHIVE="$PFDS_ROOT/session/downloads/elan-v4.2.4-x86_64.tar.gz"
test -d "$PFDS_ROOT/toolchains/lean-4.35.0-native"
test ! -e "$PFDS_ELAN_PACKAGE"
test ! -L "$PFDS_ELAN_PACKAGE"
test ! -e "$PFDS_ELAN_STATE"
test ! -L "$PFDS_ELAN_STATE"
test ! -e "$PFDS_ELAN_ARCHIVE"
test ! -L "$PFDS_ELAN_ARCHIVE"
mkdir -p "$PFDS_ROOT/session/downloads"
curl --fail --location --output "$PFDS_ELAN_ARCHIVE" \
  https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz
python3 - "$PFDS_ELAN_ARCHIVE" "$PFDS_ELAN_PACKAGE" <<'PY'
from pathlib import Path
import hashlib, sys, tarfile
archive, package = map(Path, sys.argv[1:])
assert archive.stat().st_size == 4996571, 'Unexpected archive size'
assert hashlib.sha256(archive.read_bytes()).hexdigest() == \
    '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63'
assert not package.exists() and not package.is_symlink(), \
    'Refuse to replace an existing package'
with tarfile.open(archive) as source:
    members = source.getmembers()
    assert len(members) == 1 and members[0].isfile()
    assert members[0].name in ('elan-init', './elan-init')
    data = source.extractfile(members[0]).read()
assert len(data) == 13452832
assert hashlib.sha256(data).hexdigest() == \
    'e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5'
package.mkdir()
(package / 'elan-init').write_bytes(data)
(package / 'elan-init').chmod(0o755)
(package / 'elan').symlink_to('elan-init')
PY
env ELAN_HOME="$PFDS_ELAN_STATE" "$PFDS_ELAN_PACKAGE/elan" --version
env ELAN_HOME="$PFDS_ELAN_STATE" "$PFDS_ELAN_PACKAGE/elan" toolchain link \
  pfds-native-4.35.0 "$PFDS_ROOT/toolchains/lean-4.35.0-native"
env ELAN_HOME="$PFDS_ELAN_STATE" ELAN_TOOLCHAIN=pfds-native-4.35.0 \
  "$PFDS_ELAN_PACKAGE/elan" which lean
```

The last command should print the real linked compiler wrapper path:
`$PFDS_ELAN_STATE/toolchains/pfds-native-4.35.0/bin/lean`. Confirm that its
resolved path is the native profile's `bin/lean`; do not substitute a hardcoded
answer for this check. Its ordinary `--version` invocation through the native
launcher must report the exact compiler identity in the main runbook.

Existing installations are deliberately refused by the creation recipe. On
reuse, inspect the retained binary hashes, Elan state/link and native profile
receipt instead of overwriting unknown contents. Regenerate the native profile
and custom Elan link after relocation; its generated launchers bind absolute
paths. Do not change `HOME`, shell startup files, or a global default toolchain.

## Run the unchanged suites with separate evidence

For the checker suite, from the intended clean candidate checkout:

```bash
cd "$PFDS_ROOT/import-correction-r3"
env ELAN_HOME="$PFDS_ELAN_STATE" ELAN_TOOLCHAIN=pfds-native-4.35.0 \
  PATH="$PFDS_ELAN_PACKAGE:$PATH" \
  python3 "$PFDS_ROOT/session/environment/run-native-toolchain.py" -- \
  python3 scripts/test-check.py
```

Prepending the package directory makes bare `elan` select this verified release
even when another Elan is already on the inherited PATH. The package contains
no Lean or Lake proxies to replace the native profile's launchers. Elan's
custom selection is local to this child environment. The version-mismatch
fixture still compares the actual selected compiler with its deliberately
incorrect fixture pin. Keep the stock script and its limits unchanged.

The other documented suites are:

```bash
python3 "$PFDS_ROOT/session/environment/run-native-toolchain.py" -- \
  python3 scripts/test-proof-audit-roots.py
python3 "$PFDS_ROOT/session/environment/run-native-toolchain.py" -- \
  lake env python3 scripts/test-proof-audit.py
```

The roots suite needs only the toolchain and pinned cached dependencies. The
negative-audit suite additionally needs real ordinary project import outputs,
including `ProofAudit.olean` and the `Applications` output directory. A stock
fresh full check deletes its private output directory and does not populate
that ordinary build tree. Prepare the required outputs with the documented
build route or separately reviewed, exact-identity output reuse; a successful
fresh record alone is not fixture setup. Do not share writable build directories
between active checkouts or copy another run's verification record.

Record each suite's actual command, relevant environment/input identities,
stdout/stderr, terminal status and any limitation separately. Preserve failures
or timeouts and investigate them. Setup success and a focused proof build do
not stand in for these suites, the candidate's full build/audit, both independent
reviews, or immediate final stock verification. Consult `session/STATUS.md`
and the retained review records for the current actual outcomes and scheduling.
