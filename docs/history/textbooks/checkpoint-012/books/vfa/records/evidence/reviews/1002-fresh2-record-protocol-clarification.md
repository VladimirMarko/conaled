# Preface/Perm: fresh2 native-record protocol clarification

## Identity, scope, and unchanged dispositions

Candidate: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.
Fixed enclosing base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Existing review loop: Round 8 in `1002-Perm.md`.
Coordinator: `/root/perm_review`.

Original independent reviewers:

- Standards: `/root/perm_review/standards`.
- Spec: `/root/perm_review/spec`.

Both original axes independently assessed the existing repository protocol from
pinned static source and policy. This note preserves their completed prospective
consensus and clarifies earlier checklist wording. It is not a new source review,
a changed formal gate, a waiver, a completed-evidence approval, or a replacement
for the historical review and observations.

| Finding or axis | Disposition retained |
| --- | --- |
| ST-001 | Fixed with the previously recorded evidence |
| ST-002 | Open; no incident-resolution claim |
| SP-VAL-001 | Open; completed candidate evidence still required |
| Standards | **Blocked** |
| Spec | **Blocked** |

The motivating frozen observation is
`../validation/1002-fresh2-handle-loss-first-observation.json`: root reported that
the original fresh2 checker continued running after its external recorder and
tool handle became unavailable. Its stale recorder state and stopped heartbeat
do not establish validation completion. Neither reviewer inferred the recorder's
cause of loss or the checker's eventual result. No active validation output,
process, or cache was inspected for this assessment.

## Exact static sources

The following SHA-256 identities were calculated from the immutable candidate
Git objects when this clarification was recorded, without inspecting live
validation output or cache contents:

| Repository path | Bytes | SHA-256 |
| --- | ---: | --- |
| `check.sh` | 74 | `d4a16262232c26dd48191217c1113cbbeda7dbc8ea0826505ca1bf767d0f8acd` |
| `scripts/check.py` | 16,119 | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` |
| `README.md` | 26,541 | `3f3a7d6e7c77bfd923998c2b297931d92fade83d2be266cd9a0feb3ee6d82030` |
| `AGENTS.md` | 3,118 | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `docs/agents/review-loop.md` | 7,113 | `0561fafdb97423533dd3d85ba71ab89b09c4e148c1312035846fdf80be45e64c` |

The two checker files, AGENTS, and review procedure are byte-identical to the
enclosing base. The candidate README differs from that base only by the already
reviewed VFA workstream table row; its build/audit and verification-record policy
is unchanged. The full README hash above identifies the exact candidate file,
not the pre-work README. No source or policy file was modified for this note.

## Shared conclusion

**An unrecoverable original parent wait status does not, by itself, require
repeating a completed, verified fresh run.** A genuine newly produced native
fresh success record, corroborating compilation/audit evidence, and successful
supported record verification can establish recorded fresh build/audit
completion under the repository's existing acceptance mechanism.

**The original raw return code remains unknown unless actually recovered.**
Neither the native record nor later verification permits inventing an observed
exit zero for the original checker, recorder, or launcher.

This conclusion is conditional. It does not establish that fresh2 has completed
or that its record exists, and it does not retroactively approve fresh1 or any
other incomplete or unavailable attempt.

## What precedes publication of the native record

Both reviewers independently traced the same immutable implementation:

1. `check.sh` directly executes the Python checker. It adds no separate
   post-check validation gate.
2. Candidate validation removes the previous active verification record before
   starting the new validation attempt.
3. The checker verifies the clean candidate, tracked integrated sources, clean
   Git-pinned dependencies, source policy, import coverage/cycles, and pinned
   compiler version.
4. Fresh compilation checks each individual compiler return code while building
   all inventoried project modules in private fresh outputs. A compilation
   failure prevents the audit from starting.
5. The exhaustive `ProofAudit.lean` subprocess must succeed; it is invoked with
   `check=True`.
6. The fresh temporary-output context exits, including its cleanup, before the
   final identity comparison.
7. Candidate, dependency, and compiler identities are checked again and must
   equal their starting identities.
8. Only then does `save_record` write and close the complete JSON and atomically
   replace `.lake/verification.json`, recording `result: "passed"`,
   `mode: "fresh"`, and a completion timestamp.

An authentic record produced through this path represents a completed
substantive validation milestone, including exhaustive audit and final input
checks. It is not merely an external launcher's assertion that a process started.

## Conditions for establishing fresh completion without the original wait status

Root must establish, preserve, and submit the following for evidence review:

### 1. Attribution and freshness

The record must be attributable to this original fresh2 checker and its
completed audit. It must not be a stale, restored, inherited, or copied record
from an earlier attempt. Retain the preserved launch and child identity,
chronology, and direct-log evidence, including that completion follows this
attempt's start and audit.

The record schema has no PID, invocation identifier, or worker-count field.
`--verify-candidate` does not independently authenticate the producer or
establish the age or chronological appropriateness of `completed_at`.
Attribution therefore needs the surrounding preserved evidence rather than
an assumption based solely on a matching candidate hash.

### 2. Complete matching contents

The usable record must have the supported format, `result: "passed"`,
`mode: "fresh"`, the exact candidate
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, and the expected pinned dependency
and compiler identities. A merely present file is insufficient.

### 3. Corroborating completion evidence and honest limits

Preserve the direct checker's corresponding complete compilation and exhaustive
audit outcome. Assess any truncation, missing output, later error, or conflicting
evidence explicitly. The stale external recorder JSON and heartbeat are not
completion evidence and must not be silently rewritten as such.

### 4. Quiescence before later operations

The original checker and its owned compiler activity must have ended before
another validation attempt, repair, or operation requiring an idle checkout.
Losing a recorder or UI handle does not establish termination and is not a
reason to launch an overlapping replacement checker.

This assessment did not observe quiescence. Root owns establishing and recording
it when the existing activity actually finishes.

### 5. Successful supported record verification

In the stable isolated checkout and pinned environment, use the existing route:

```sh
nix develop --command ./check.sh --verify-candidate HEAD
```

Do not add `--fresh` or `--jobs`. Preserve this new short command's actual
successful result and exact identity.

The command reads and validates the supported record, checks the current clean
candidate/dependency identities and compiler version, and compares them with
the record. It does not rebuild, rerun the audit, repair outputs, rehash project
artifacts through the integrity guard, or replace the success record. Its
success is record verification, not a newly executed fresh audit.

### 6. Preserve the accepted evidence before another validation

Save the matching fresh record, command, direct log, chronology, identity
evidence, unknown-status account, and successful record-verification result in
separate immutable attempt-specific evidence. Starting another candidate check
removes the active record and success creates a new record for that attempt's
mode. Do not restore an old record to conceal a later failed attempt.

## Post-publication finalization and unknown raw status

The checker publishes its record before printing the final candidate-recorded
and PASS messages and reaching its normal `return 0`. A later reporting or
stream-flush error, interruption, interpreter finalization failure, or exceptional
record-writing cleanup after replacement could prevent an observed zero process
termination even though the substantive validation milestone was reached.

Any known post-publication failure must be preserved and assessed for its
actual effect on the record and input stability. Its mere possibility does not
erase completed checks; an actual contradictory integrity or provenance issue
cannot be ignored.

If the stated conditions are demonstrated, an accurate conclusion is:

> Fresh compilation, exhaustive audit, and final identity checks completed;
> the native success record was subsequently verified. The original
> checker/launcher wait status is unavailable.

It must not be rewritten as “the original process exited 0” without observation.
The external recorder's unknown outcome and cause also remain unknown unless
separately established. This note supplies neither a fabricated status nor a
reconstruction of lost process evidence.

## Original independent axes' agreement and checklist clarification

### Standards — `/root/perm_review/standards`

Standards confirmed that AGENTS delegates acceptance modes to README and that
README/review-loop require candidate validation, its native record, and the
supported verification step. They do not add a mandatory rebuild solely to
recover a lost parent wait status. Standards independently verified the record
emission path and the post-publication finalization limitation above.

Standards explicitly clarified that its earlier checklist's request for an
observed exit zero described normal recording practice too narrowly. That
wording does not supersede the repository's existing native-record route.
Missing, unusable, mismatched, or materially uncertain evidence still requires
investigation and applicable revalidation; parent-status loss alone is not that
trigger. Overall Standards remains **Blocked** pending completed evidence and
the other outstanding gates.

### Spec — `/root/perm_review/spec`

Spec independently agreed that the authentic success record and successful
supported record verification can establish recorded fresh completion while
the original process return remains unknown. The schema's lack of an attempt
identifier makes external attribution and chronology material. Spec confirmed
that the stale recorder state is not completion evidence and that no present
active-run approval follows from this prospective interpretation.

Spec likewise clarified that its earlier request for an independent exit code
zero was straightforward evidence to collect, not an extra formal gate that
forces a complete repeat when the repository's authoritative protocol proves
the required completion. Overall Spec remains **Blocked**, and SP-VAL-001
remains open until the applicable completed evidence is assessed.

## Limits and remaining gates

If the native record is missing, unusable, mismatched, or materially uncertain
in provenance, audit text alone does not discharge the record requirement.
Investigate and perform applicable revalidation under the existing policy.
No verification command or successful result is claimed by this prospective
note.

The clarified route can establish only the fresh-verification portion. It
does not replace the separate guarded incremental recovery, the non-repairing
inspection/evidence-preservation plan, the managed `+ProofAudit` prerequisite,
required regression, both independent completed-evidence assessments, or final
`./check.sh --verify-candidate HEAD` immediately before acceptance. The four
original mismatch artifacts and unresolved origin investigation remain governed
by the existing ST-002 assessment.

The historical `1002-Perm.md` review, its past observations, and all frozen run
records are unchanged. Both reviewers performed only the authorized static
source/policy and frozen-observation assessment. Recording this clarification
used immutable Git-object reads and created only this separate note. No live
validation outputs, processes, or caches were inspected, and no compiler,
helper, test, or verification command was run.

This writer is frozen after recording and returning the file's external SHA-256.
Any later evidence or disposition belongs in an explicitly identified follow-up.
