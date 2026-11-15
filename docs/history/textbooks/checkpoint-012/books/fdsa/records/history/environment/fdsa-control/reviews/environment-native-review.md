# Native environment review — continuation of environment 0068 loop

## Scope and immutable identities

This continues the same environment/recovery implementation review after the
user rejected slow emulation and requested alternatives. The completed and
conditional history in `environment0068-review.md` and its two independent
reports remains intact. The checkpoint 0068 archive is unchanged.

- Snapshot repository: `/workspace/scratch/6bb268f9336f/environment-review-0068`.
- Unchanged fixed base and confirmed merge base:
  `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`.
- Native candidate: `9f673480206912d7df4a1dcc2b09ca7527bb0275`.
- Previous environment candidate:
  `5fe6d4f7cdac2761c7c3622d26479282cfb7fa1b`.
- Full eleven-path scope and byte identities: `environment-native-snapshot.json`.
  This includes every previous implementation artifact, the native adapter,
  compatibility-library source and binary, and all three native validation
  harness source files. Nothing within this declared implementation is excluded.
- The coordinator verified the clean snapshot, nonempty complete diff, merge
  base, and all eleven snapshot/live artifact hashes before review dispatch.

Formal source remains candidate `07e480f6ec9958d4975bb90151005b84f2907614`
with original project base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
No formal source, pin, checker, guard or proof-audit change belongs to this
environment correction. Chapter 1 and SPEC-001/002/003/V001 remain open.

## Requirements and evidence

The original governing FDSA request, retained limited Nix exception and latest
user steering in `provenance/native-environment-20261103/user-request.json`
define the scope. The user seeks a faster alternative to QEMU, with the exact
official compiler/dependency versions and all formal acceptance rules intact.
The recovery recipe must be self-contained and truthful about runtime changes
and execution-domain limitations.

The proposed native route keeps the official Lean/Lake executables unchanged
and adds a separately recorded compatibility library for missing own-executable
path discovery. Both axes must assess the narrow fallback semantics, explicit
stable absolute ELF launch contract, extra runtime dependency, source-to-binary
provenance and recovery instructions. The prior ENV68-SPEC-001 recorder fix
and its independent closure remain part of the complete scope.

Supplied native evidence is listed in `environment-native-snapshot.json`:
boundary tests, launch-domain tests, source/binary build record, ten actual
native startup/path/proof/cache-help checks, and the actual native dependency
cache retrieval. Both real proof artifacts have the same 6824 bytes and
SHA-256 `fbf279c5128799661a3f3087d27f139d4da4944e9061ae0c522fce3af38bb980`
as the earlier QEMU smoke artifacts. The new adapter and compatibility bytes
are bound to these records. Native cache retrieval records exit 0 in 70.79
seconds and a clean unchanged candidate; it is not a project build or audit.

The earlier QEMU cache-build attempt r2 also has an actual terminal result:
exit 0 in 161.54 seconds, clean source, corrected recorder and a closed
588-byte log, SHA-256
`ebaf6dc29a83d012474cc6c70c9f9e9f97c6d5be1bc11049d619499d8ce73dac`.
The coordinator read that result and complete log. This resolves the missing
terminal evidence factually without making QEMU the user's preferred route.
The first cache attempt's interruption and unknown child outcome remain
separate history; no old outcome is replaced with r2's success.

## Independent axes

The retained independent Spec and Standards axes assess the full eleven-path
delta from the same fixed base, reusing earlier unchanged analysis/evidence.
The coordinator reconciles them and performs no third source-review axis.
Standards must also determine the appropriate next Chapter 1 verification mode
given the additional native runtime library, unchanged official compiler/pins/
checker and cold project outputs. No mode ruling may waive all-module build,
both integrity phases, exhaustive audit, final independent formal review or
immediate candidate-record verification.

At initial dispatch the review was in progress; no approval was inferred from
implementation or validation alone. The completed outcomes follow.

## Reconciled final outcome

Both independent axes pass the same complete native candidate
`9f673480206912d7df4a1dcc2b09ca7527bb0275` against the same fixed base
`900614e27f7d3dfffd9a29139884a8f1a4fce8d3`:

| Axis | Outcome | Unresolved findings | Worst unresolved issue |
| --- | --- | --- | --- |
| Standards | Passed for environment/recovery implementation | 0 | None |
| Spec | Passed for environment/recovery implementation | 0 | None |

The coordinator read the entire final native Standards report and the entire
new native Spec assessment, retaining its earlier complete round readbacks.
The reports remain separate and their scopes and qualifications are unchanged:

- `environment-native-standards.md`, 10813 bytes, SHA-256
  `05695c42dec7a60a93df032818eb779fc52f4997ec08667d5c781a1b7934f4a4`.
- `environment0068-spec.md`, with all three rounds, 18475 bytes, SHA-256
  `23da57348583157670faad7729a273cc88ff24370ddeba9afcfaab6501ec5a4a`.

ENV68-SPEC-001 remains fixed with independent source and execution evidence.
There is no newly unresolved native finding. Immediately after reading both
reports, the coordinator rechecked all eleven delivered control artifacts
against their immutable candidate blobs and the snapshot hash record: all
match, and the snapshot checkout is clean. That identity check binds this
environment-only approval to the delivered implementation; it is not a formal
project verification command or an approval of later edits.

### Next formal gate and limits

The independent Standards report explicitly permits the complete ordinary
guarded `./check.sh --candidate HEAD` route through the native adapter for
this specific cold recovered checkout. The official compiler release, all
dependencies, project compilation configuration, checker, integrity algorithm
and proof audit are unchanged; the observed project `.lake/build` was absent.
Every integrated module must therefore compile in the selected environment.
Both integrity phases, source/public-coverage checks, exact identities and the
exhaustive transitive-axiom audit remain mandatory. The external compatibility
library is a disclosed trusted runtime dependency within its documented stable
absolute-ELF launch contract, not a general proc-filesystem implementation.

This ruling introduces no additional full fresh pass or unrelated fixture
suite. New stale-output evidence, a changed compiler/pin/project tool or
changed compatibility implementation must still be reassessed under the
unchanged README and incident rules. Root separately owns current disk-capacity
checks and the actual controlled validation run; this review does not predict
its success or adequate future storage.

The next checkpoint may preserve the approved environment implementation and
all historical evidence. Native execution is the current selected route; QEMU
remains preserved fallback history. No chapter, appendix or shared unit is
accepted here. Chapter 1's complete original fourteen-path scope, frozen
requirements, original base, candidate and SPEC-001/002/003/V001 remain in force.
Full candidate success, both independent final Chapter 1 reviews and immediate
`--verify-candidate HEAD` are still necessary before Chapter 1 acceptance.

The two independent reports and this coordinator record are now stopped for
root's checkpoint capture. No implementation file, project source, dependency,
cache output or acceptance policy was edited by this coordinator or its axes.
