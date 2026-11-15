# Local #1025: proportional acceptance disposition

Recorded: 2026-11-02T10:05:49.566809+00:00
Candidate: `39c3e2fd0c3a7b39e56373d453a1a17382bc3749`.

## Established evidence

The inactive main Mathlib cache and uploaded local checkpoint 000 reappeared
after deliberate removal. A task-scoped lsof observation found an rsync reader
on one main-cache artifact, without recording a recreating writer or transfer
scope. Three harmless-file probes (sequential modes and both overlap directions)
did not reproduce recreation. A separate forty-second process capture found no
rsync holder or active-input write. These negative observations do not establish
absence of another writer. No Lake artifact/trace mismatch, source/dependency
identity drift, shared writable project build directory or active-cache
replacement has been observed.

## Decision and policy basis

Root initially held acceptance while classifying the event. Independent
reassessment by reuse_survey concluded that retaining a global hold solely
because writer scope remains unknown would add a requirement absent from the
repository's ordinary acceptance contract. The reviewer corrected its earlier
stronger recommendation. README explicitly describes trusted local bookkeeping,
not certification against all transient edits, external inputs or hostile
substitution. The incident runbook requires relevant failures or evidence of
unsafe active inputs before its stabilization/recovery procedures apply.

Root therefore removes the extra hold and leaves #1025 open as a nonblocking
storage/provenance investigation. This does not assert that the unknown copier
excludes the active checkout. It retains the normal trusted stable-checkout
assumption, supported by coordinated writers, separate actual paths/inodes,
observed dependency paths, clean pinned sources and unchanged recorded inputs.
The complete guarded candidate build and exhaustive audit, managed ProofAudit
prerequisite, required regression, both independent review outcomes and final
`--verify-candidate` remain mandatory. No result from a focused check or this
policy assessment accepts a chapter.

## Evidence that changes the disposition

An actual active-input change, unexpected active-cache replacement, source or
dependency identity drift, output/trace mismatch, unexplained repeated
invalidation, or another concrete challenge to active-input stability will
reopen the blocking incident assessment under the existing runbook. Preserve
the evidence before cleanup and choose fresh verification when its stated
conditions apply. Do not repeatedly delete inactive caches or run unbounded
process probes merely to try to prove a universal negative.

The user explicitly substitutes local tickets for GitHub writes. No GitHub
comment or issue is created. Related evidence is listed in tickets.json #1025.
