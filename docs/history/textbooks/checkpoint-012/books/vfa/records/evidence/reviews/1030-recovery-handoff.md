# Checkpoint035 recovery handoff: independent read-only assessments

Date: 2026-11-03. Formal candidate remains
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`; enclosing formal review base remains
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

These are operational recovery assessments. They do not replace the original
Standards and Spec axes or approve a formal candidate. Both formal outcomes remain
Blocked; ST-002 and SP-VAL-001 remain open. No formal source changed.

## Recovery integrity assessment — /root/recovery_audit

Scoped recovery-handoff assessment: clear, with no material defects found.
This is a review of recovery records and resume instructions, not formal
candidate approval.

Reviewed STATUS.md, specs/1030-recovery.md, both 1030 validation records, the
appended environment section, and the ticket/checkpoint changes, against the
original checkpoint manifest and retained source inventory.

- All 1,574 recorded source paths match original metadata, including content
  hashes and executable bits. Index/working-tree patches match captured hashes;
  the formal checkout remains clean at the same candidate.
- Saved original STATUS and tickets exactly match the original manifest entries.
- REQUIREMENTS.md, AMENDMENTS.md, the complete Preface/Perm review record and
  acceptance checklist remain byte-identical.
- No original manifest file is missing. Only the four expected existing files
  changed: STATUS.md, tickets.json, checkpoints.json and environment.md.
- The previous environment document is an exact prefix of the updated file.
  All previous checkpoint records are retained unchanged; the new checkpoint035
  record distinguishes current attachment identity from an unavailable original
  upload receipt.
- The input archive hash, downloaded VFA archive hash and all 17 chapter hashes,
  sizes and order match the recovery record and pinned inventory.
- Downloaded upstream AGENTS.md is byte-identical to the restored copy; the Nix
  archive matches its recorded official hash.
- The namespace probe was not repeated. Its provenance is attributed to the
  environment agent, with conclusions limited to the exposed sandbox.

The handoff preserves full chapter order and scope, local tracking/publication
exceptions, fresh plus separate guarded validation, exhaustive audits, managed
ProofAudit prerequisite and regression, both independent axes, immediate final
verification, and the acceptance checkpoint before Sort implementation.

Ticket edits clear current run pointers while preserving historical ones.
Original run/review files were not altered. Unknown fresh1/fresh2 outcomes remain
unknown. Missing restored caches do not resolve the historical integrity cause
or establish the old host's process state. No approval rejection, installation,
formal build, chapter acceptance or successor implementation is invented.

Checkpoint036 creation, restore verification and upload were prospective during
this assessment; this assessment does not certify those later actions or their
final hash. Their actual results must be recorded separately.

## Environment evidence assessment — /root/environment_options

The ordinary installer's requirement for /nix is correctly distinguished from
the separately observed local namespace failure. The handoff does not assert
host-wide namespace disablement, host-wide absence of Nix, or an approval
rejection. The downloaded archive was not installed; historical approvals and
process identities are not treated as current access or active resources.

The resume commands preserve the pinned shell, unchanged candidate, separate
isolated checkout, fresh and guarded validation, audit regression, independent
reviews and immediate final verification. Recovery remains subordinate to the
whole-book objective. The source/hash checks were outside this assessor's scope.

One precision finding was raised: the original field
`writes_outside_allowed_roots_attempted: false` was too broad because the approved
namespace probe attempts to open /proc/self/uid_map. Root replaced it with
`system_installation_writes_attempted: false` and added the exact process-interface
failure limitation. The assessor read the corrected record and confirmed the
finding resolved.

Final scoped disposition: clear, with no unresolved operational evidence
findings. This is not formal Standards/Spec approval, a proof-validation result,
or chapter acceptance. No further probes or changes were performed by this
assessment.

## Root reconciliation

Both read-only assessments are retained as recovery evidence. The unchanged
formal source reviews are neither reset nor upgraded. The environment blocker
is unresolved and remains local #1030. Capture the complete source/history/state
with the existing checkpoint tool and preserve its actual creation and upload
results. No chapter credit follows from checkpoint success.
