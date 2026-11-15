# Unified native environment recovery — checkpoint 045

Recorded 2026-11-03. The supplied native kit completed setup successfully at
23:26:09 UTC in the recovered workspace. This is environment evidence only;
no formal candidate build, exhaustive audit, chapter acceptance, or integration
acceptance is asserted here.

The exact command was:

```sh
python3 /workspace/scratch/09cf0de22282/conaled-native-kit-4.35.0/conaled_native.py \
  --state /workspace/scratch/09cf0de22282/pfds/native-state \
  setup --project /workspace/scratch/09cf0de22282/pfds/conaled
```

Its actual execution session terminated with exit 0. The complete outer log is
`unified-native-setup-045.log`. The authoritative summary, source identities,
retained-file hashes, commands, and limitations are in
`unified-native-setup-045.json`. Original kit-produced receipts and command logs
are copied byte for byte under `unified-native-evidence-045/`, including the
small source fixtures used for smoke tests. The original mutable runtime state
is reproducible and is not part of the recovery payload.

## Inputs and observed results

| Item | Result |
| --- | --- |
| Supplied kit | Version 1.0.0; all 298 manifest files verified after setup. |
| Kit archive | 1,154,144 bytes; SHA-256 `45edfb844068f93b26ea5469572473f8c07e5a63e2bc294eed6de543cb3d5bf2`. |
| Official Lean archive | 594,481,375 bytes; complete archive SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` verified before extraction. |
| Release extraction | 18,571 members and 3,137,937,793 regular-file bytes. The complete release was preserved. |
| Compiler | `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`. |
| Lake | `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`. |
| Host mode | `compat`: the kit's bounded own-executable metadata adapter, with unchanged official executables. |
| Dependency sources | All nine checkouts installed at the exact manifest revisions; all remained clean in the post-setup check. |
| Cache utility | The 19-object relink exited 0 and reproduced the kit's fixed SHA-256 `a8b0bf258ad991ba40561bffcbcadc88ad429eef6e4ac2cd8ae99b229590d624`. |
| Cache retrieval | Actual exit 0; 9,031 requested files downloaded and decompressed; 65.955 seconds for the cache command. |
| Smoke suite | All ten cases met their expected outcomes. |
| Final runtime doctor | Passed: profile identity, 47 official release/link inputs, and eight additional runtime files. |
| Project source | Main stayed clean at `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`. Project checker, proof policy, toolchain pin, and dependency manifest were not edited. |

The smoke cases checked both versions, bare and Lake-child compiler prefixes,
a true proof, rejection of a false proof, Lake-child proof checking, a native
executable build, execution printing `42`, and a real
`Mathlib.Tactic.TypeStar` import. The false-proof case exited 1 with a Lean
error, as required. The Mathlib fixture emitted an unused-variable warning and
exited 0; no linter setting or source policy was changed.

The full archive hash authenticates the initially extracted release. The
doctor's 47+8 checks are bounded subsequent file checks, not a fresh complete
distribution attestation. Cache download success likewise does not prove the
project's formal statements or replace its checker.

## Recovery layout and commands

The small supplied archive is retained intact at:

```text
session/environment/conaled-unified-native-kit-lean-4.35.0-2026-11-03.tar.gz
```

After restoring the PFDS checkpoint into a new directory, set `PFDS_ROOT` to
that directory's absolute path. Extract the kit beside it, outside both project
source and runtime state. Use a fresh destination if the sibling kit already
exists with different contents; do not overlay an active or mismatched kit.

```sh
PFDS_ROOT=/absolute/path/to/restored/pfds
PFDS_KIT_PARENT="$(dirname "$PFDS_ROOT")"
tar --no-same-owner -xzf \
  "$PFDS_ROOT/session/environment/conaled-unified-native-kit-lean-4.35.0-2026-11-03.tar.gz" \
  -C "$PFDS_KIT_PARENT"
PFDS_KIT="$PFDS_KIT_PARENT/conaled-native-kit-4.35.0"
PFDS_NATIVE_STATE="$PFDS_ROOT/native-state"

python3 "$PFDS_KIT/conaled_native.py" verify
python3 "$PFDS_KIT/conaled_native.py" --state "$PFDS_NATIVE_STATE" \
  setup --project "$PFDS_ROOT/conaled"
python3 "$PFDS_KIT/conaled_native.py" --state "$PFDS_NATIVE_STATE" \
  doctor --full
```

The state path must contain no whitespace or colon. Setup needs the official
release, exact dependency repositories, and their cache endpoints to be
reachable, unless the kit's documented offline inputs are already present.
Setup can resume its own partial official download and reuses verified inputs.
Read the intact kit's `README.md` and `docs/RECOVERY.md` before handling a
mismatch; do not change expected hashes, source pins, or the compatibility
adapter to force setup to succeed.

This session prepared private real dependencies at
`conaled/.lake/packages`. The root coordinator owns any later PFDS-specific
candidate sharing under the existing serial-writer discipline. The universal
kit's `setup`, `deps`, and project-scoped `doctor` intentionally reject shared
or symlinked package layouts. For such a deliberately shared PFDS candidate,
use runtime-only `doctor --full` and the reviewed validation controller's
separate exact-source/dependency checks; do not reinterpret a kit refusal as
permission to remove its guard.

The kit's ordinary command wrapper remains:

```sh
python3 "$PFDS_KIT/conaled_native.py" --state "$PFDS_NATIVE_STATE" \
  run --project "$PFDS_ROOT/conaled" -- lake build Applications.Resources.Potential
```

Formal acceptance must use the current, reviewed candidate route and its own
stock check, audit, review, and immediate verification obligations. In
particular, this setup does not authorize using an old controller's fixed
`901f734...` identity to validate the prospective integration candidate
`3cf3de4...`.

## Stable identity and controller adoption

The runtime profile is `native-state/profile`. Its `config.json` records
wrapper, payload, adapter, loader, runtime-source, link, and watched official
file identities. The current configuration SHA-256 is
`ef95106ffdf6b594235bfd88284b1ef5450e392d04bbcc3f62a4a7b685dc7573`.
This is a fact about this constructed profile; a legitimate recovery creates
a new profile and new evidence rather than blindly adopting an old host's
runtime configuration.

`doctor --full` emits a JSON object with a volatile `free_bytes` observation.
Preserve that observation separately; exclude it from frozen-input identity
equality. The summary JSON does so, retaining the remaining doctor fields under
`runtime_identity` and the free-space observation under `observed_free_bytes`.

For the pending controller adoption, the kit's `run` wrapper creates its own
child process group. Nesting that wrapper under a controller which only kills
its immediate launcher's process group can leave the checker running. The
root coordinator was advised to load the fixed kit's `environment(state, 1)`
API, call its project/profile checks, and directly launch the unchanged stock
command in the controller-owned group. That uses the same kit environment
while retaining ownership of checker cleanup. The controller must accurately
record that API-based environment selection and actual command; it must not
claim a `kit run` invocation that did not occur. This paragraph is design advice,
not an implemented or independently approved controller outcome.

All ten smoke command logs and all original setup/acquisition records remain
available. Earlier interrupted project gate records were not rewritten. The
next formal gate still needs the reviewed exact candidate scope, stable inputs,
real terminal full-build/audit success, required regressions, both independent
review axes, and immediate stock verification.
