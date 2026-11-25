# Native restart after compact recovery

Packet route: `current/operations/native-restart.md`. Checkpoint147 preserves the
portable recorder actually used after fresh environment preparation. Its actual
setup observations are separate evidence; every future host must be prepared
and verified again with the unchanged pins.

## Retained source required

Keep these exact packet members. The adapter reads its pins and library sources
relative to `native_profile.py`, so this layout needs no old136 directory:

| Packet member | Purpose |
| --- | --- |
| `operations/native/native_profile.py` | Profile creation, verification and command interface |
| `operations/native/PINS.json` | Official distribution and project pin-file identities |
| `operations/native/lib/runtime.py` | Per-tool launcher and outer/child environments |
| `operations/native/lib/app_path.c` | Source for the locally compiled application-path adapter |
| `operations/native/NOTICE.md` | Attribution and verification limits |
| `operations/SETUP.md` | Original native setup, acquisition and acceptance guidance |
| `operations/run_recorded.py` | Current recorder with immediate durable child-exit receipt |

The original setup README is `operations/SETUP.md`; the supplied native directory
has `NOTICE.md`, not a separate `README.md`. Its optional regression command uses
`test_native_profile.py`, which is not part of this minimum selection. That test
file is not required to prepare or run the adapter; do not claim its tests ran.

The recovered repository supplies `lean-toolchain`, `lake-manifest.json`,
`lakefile.toml`, the pinned Nix files, `README.md`, `AGENTS.md` and
`docs/development.md` through the unchanged complete-source recovery mechanism.
No generated native profile, host config, toolchain inventory, installed binary,
dependency checkout, download, cache or build output is required in the packet.

## Restore first, then create fresh external state

Complete the packet's ordinary independent repository restoration and strict
inspection before using the recovered source. Preserve the exact public
prerequisite, full source delta, tracked bodies/modes, index/tree and style gates.
`PINS.json`'s historical `prerequisite` is adapter provenance, not the current
source prerequisite. A historical private candidate hash is not a promise that
that Git object exists in the restored ordinary clone.

Use the repository's pinned Nix/direnv route when available. The already
authorized native route requires Linux x86-64, Python 3.11+, `cc` or `gcc`, a
glibc loader supporting per-program `--preload`, Git, HTTPS acquisition and zstd.
The adapter selects the host compiler's loader before system fallback paths.
Permission errors or mixed `/proc/.../exe` behavior are errors, not permission to
force its compatibility mode.

Reuse a matching complete official Lean distribution or obtain the archive
specified by `operations/native/PINS.json` into new external storage. Before
extracting it, check both its exact length and SHA-256:

- Lean **4.35.0**, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Archive: `https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`.
- Length: **594481375 bytes**.
- SHA-256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

The complete extracted distribution retains its licenses. Profile preparation
checks 55 selected official inputs plus required directories; this is not a
whole-tree attestation of an arbitrary existing installation. A patched local
Elan distribution can legitimately differ and must not be accepted by changing
expected hashes.

Set the following to actual absolute paths. The state and run directories must
be new, with existing parents, outside both the recovered project and the entire
packet. The state path must have no symlink components, whitespace or colon.
Keep the packet immutable.

```sh
export CONALED_PACKET="/absolute/path/to/extracted-checkpoint"
export CONALED_PROJECT="/absolute/path/to/recovered-conaled"
export CONALED_TOOLCHAIN="/absolute/path/to/official-lean-4.35.0-linux"
export CONALED_PROFILE_STATE="/absolute/new/native-state"
export CONALED_RUN_DIR="/absolute/new/native-runs"
export CONALED_NATIVE="$CONALED_PACKET/operations/native/native_profile.py"

python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" prepare \
  --toolchain "$CONALED_TOOLCHAIN" --project "$CONALED_PROJECT"
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" verify \
  --project "$CONALED_PROJECT" --full
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" run \
  --project "$CONALED_PROJECT" -- lean --version
python3 -B "$CONALED_NATIVE" --state "$CONALED_PROFILE_STATE" run \
  --project "$CONALED_PROJECT" -- lake exe cache get
```

Observe each actual result and stop dependent commands on failure. The last
command obtains dependencies/cache using the unchanged `lake-manifest.json`;
its nine exact Git revisions remain authoritative, including mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Check the obtained dependency identities
and source cleanliness before compiling. `prepare` and `verify` explicitly
report `dependencies_checked: false`; they do not perform that dependency check.
Do not run `lake update`, use moving branch heads, or alter pins to repair setup.

Preparation regenerates the host loader path/hash, compiled adapter hash,
relative toolchain links, wrappers and watched-file metadata. The former
`work/native-state/profile/config.json` describes the previous host and layout;
copying it into a new workspace is not bootstrap. No hand-authored replacement
config is needed.

Preserve the existing ten-minute setup/troubleshooting budget and at most one
targeted retry for a concrete failure. Record the actual blocker when exhausted.
This budget does not cap mathematical compilation. Add no thread, memory,
heartbeat, recursion or compilation-time overrides. Let the adapter and Lake
own the Lean search paths and per-program loader environment.

## Copy the portable recorder into a new run directory

The retained recorder now reads `CONALED_NATIVE` and `CONALED_PROFILE_STATE`
from the environment. Prepare and verify the new external profile first. Export
those two variables with the actual absolute native-adapter and state paths.
Copy the exact recorder into a new external run directory; do not run it in the
immutable packet. No source adaptation is necessary.

```sh
python3 -B - <<'PY_COPY_RECORDER'
from pathlib import Path
import hashlib
import json
import os

source = Path(os.environ["CONALED_PACKET"]) / "operations/run_recorded.py"
raw = source.read_bytes()
expected = "a606ef4743c42fe85d47037e768f2b8b5e2ece5557eadbe13e471eb047e73ce0"
if hashlib.sha256(raw).hexdigest() != expected:
    raise SystemExit("Recorder differs: review its source before using it")
work = Path(os.environ["CONALED_RUN_DIR"])
if not work.is_absolute() or work != work.resolve():
    raise SystemExit("Run directory must be a canonical absolute path")
work.mkdir(exist_ok=False)
destination = work / "run_recorded.py"
with destination.open("xb") as stream:
    stream.write(raw)
print(json.dumps({"source_sha256": expected, "working_path": str(destination),
                  "working_sha256": hashlib.sha256(raw).hexdigest()}))
PY_COPY_RECORDER
```

Retain the working recorder's hash and exact source as a current operational
input. Always pass `--project` explicitly. Rebuild each input-list JSON from the
current packet's source map and actual new workspace paths. Before launching,
check that every listed path exists as the expected regular file and that all
required source/config/tool inputs are listed. The recorder's unchanged
`describe` function returns null for a missing path; equal missing bindings must
never count as an acceptable source-invariance observation.

Options must precede the positional run name because the recorder uses
`argparse.REMAINDER` for the command:

```sh
python3 -B "$CONALED_RUN_DIR/run_recorded.py" \
  --project "$CONALED_PROJECT" --inputs "/absolute/path/to/new-inputs.json" \
  native-smoke -- lean --version
```

Use unique run names. The recorder writes its start, log, child-exit and final
result beside the working copy, so these remain outside the immutable packet.
Use the same route for a focused command only after its exact current inputs
have been assembled. Interrupted work without a terminal receipt stays UNKNOWN.

For whole-candidate validation, follow the recovered source's current capture
and checker contract, using an actual independently owned candidate checkout,
one output writer and stable dependency inputs. Never substitute the archived
private candidate name for a missing object or reuse old project outputs by
copying them into the new checkout. Environment readiness, focused compilation,
whole-check completion, independent review and checkpoint recovery retain their
separate gates.

## Source review binding

This proposal read the complete supplied `SETUP.md`, `NOTICE.md`,
`native_profile.py`, `lib/runtime.py`, `lib/app_path.c`, current recorder,
the pin/config fields relevant to relocation, the current complete Lake manifest
and the repository's development setup/build instructions. No old host profile
or toolchain inventory needs selection.

The adapter-source identities are:

| File under `operations/native/` | SHA-256 |
| --- | --- |
| `native_profile.py` | `a3891ea20145d0cd9fed82c07b95276d79fe611eb141c27e8a9a600b62355ea4` |
| `PINS.json` | `854746c88e7ab68f1f81ff6749842b9549dea7d51591952d5987c68a81c668f6` |
| `lib/runtime.py` | `cafe22ddc9a0de09a7dad5ef70fbd1c0b752217281cafed6bd71b7601d9413ad` |
| `lib/app_path.c` | `fefc39d8645e4a938d6cc27574257d1a1e8e8f0790b75cc15bcf074272066fe0` |
| `NOTICE.md` | `0622bfa90322c467122bcb2bd9b6f361a69dd9c9e274722fbce9ee699c321510` |

Current `lean-toolchain` SHA-256 is
`ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
current `lake-manifest.json` SHA-256 is
`dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b`.
Both match the adapter's `project_files` pins. Packet inventory and curated
selection descriptors bind the retained source bodies; this note grants no
runtime or compiler validation credit.
