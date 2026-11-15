# Local #1026: make remaining proof imports explicit

Recorded: 2026-11-02T10:15:16.915057+00:00
Implementation baseline: `39c3e2fd0c3a7b39e56373d453a1a17382bc3749`.
Enclosing review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

## Scope and decision

Apply exactly the ten ordered single-line replacements in
`../validation/1026-import-plan.json`. The independently prepared source proposal
is `../validation/remaining-import-survey-round2.md`, SHA256
`29a90c4156c9c3aadb20c2f78ff90fed093af4efb8bc51714c8694f23fb14ee3`. Its exact original/proposed
hashes, provider findings and explicit residual uncertainties are part of this
specification. Preserve every other source byte, including all remaining imports,
comments, statements, assumptions, definitions, proof bodies and existing cases.
Do not alter tooling, pins, dependencies, compiler flags, proof policy, mathematical
interfaces, or chapter order. The existing ProjectiveMotion deferral is superseded
only by this explicit combined decision. No later VFA chapter is implemented.

The current baseline has severe observed import-loading cost: DiagnosticGraph
and DiagnosticProjection took 288 and 424 seconds, and DiagnosticStorage finally
passed after 1,387 seconds. Bounded process observations are saved separately in
`../validation/20261102-baseline-import-pressure.json`; they establish continued
I/O activity, not a unique cause. The joint source graph removes Mathlib.Tactic
from 62 affected modules. At the proposal snapshot 14 were complete and 48
unfinished; those counts can change as the old build continues. The joint
aggregate external closure changes from 4179 to 3807 modules. These are topology
counts, not a measured timing or memory benefit.

## Actual remaining obligations

The proposal retains concrete downstream requirements, including Diagnostic
Linarith/Ring, BoundedSummary Ring, and FiniteMH finite-sum theorem providers.
Retained named providers do not establish identical implicit simp registrations,
tactic extensions, instances or public visibility. In particular Structured's
integer-matrix NormNum extensions and Monitor's small header need elaboration.
The full candidate build decides those questions; no source-only clearance
accepts the change. If a named dependency is missing, retain the actual diagnostic
and correct the narrow import through this same implementation/review loop.
Do not change a proof body or weaken a claim to conceal an import failure.

## Integration and validation

Root owns the integration. Stop only the recorded task-owned primary process
group after verifying its command, start identity and workspace membership.
Preserve the old log and actual raw return code, confirm the complete group is
inactive before changing the isolated checkout, and retain ordinary completed
outputs under the existing guard. An intentional interrupted partial artifact
is not an unexplained integrity incident.

There are no separate focused compiler experiments in this round: normal full
candidate validation will compile the actual project and every integrated client
using the existing pinned Nix environment, LEAN_NUM_THREADS=1, unchanged check.sh
and no imports/setup overrides. This avoids duplicating prerequisites while the
initial baseline is incomplete. Capture the new clean candidate and immediately
create, restore-check, expose and upload a recovery checkpoint. Then run the
unchanged `./check.sh --candidate HEAD` in the isolated checkout, retaining actual
failures and success evidence. Reuse normal project outputs through Lake's guard;
do not install hand-produced staging artifacts.

After genuine full-gate success, preserve the matching verification record,
run the documented managed +ProofAudit prerequisite and required proof-audit
regression, complete both original independent Standards/Spec axes on the full
enclosing diff and this exact candidate, and run `./check.sh --verify-candidate
HEAD` immediately before acceptance. No fresh-mode trigger arises solely from
import changes; actual stale-artifact evidence or configuration changes would
be assessed under the existing README/runbook. Local #1025 remains an open
nonblocking storage investigation under its recorded proportional disposition.

Existing cases and byte-identical declarations are the appropriate statement
review boundary for this import-only refactor. Full elaboration/audit and the
independent reviews remain required. No chapter or cross-cutting ticket is
accepted by preparing this specification or by committing the import changes.
