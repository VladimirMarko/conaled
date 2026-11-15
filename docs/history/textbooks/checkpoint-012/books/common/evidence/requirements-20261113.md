# Textbook integration requirements

Version: 2026-11-13, including the user's native-setup and priority clarifications.
Authority: the current conversation. This file preserves the full acceptance
intent outside the source diff; the local tracker is `ISSUES.json`.

## Requested result

Integrate the VFA, FDSA and PFDS developments with the current `master` of
`VladimirMarko/conaled`. Pin that master before implementation. The fixed full
integration baseline is `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`.
Do not silently move it when upstream advances. Future ticket incorporation
does not replace this original whole-task review base.

This is a cohesive library integration, not just textual conflict resolution.
Discover and use the actual pinned library architecture and capabilities.
Check the external agents' process and evidence against the current required
workflow. Integrate modules with each other and existing owners, prove useful
relations and equivalences, and support interchangeable clients where the
explicit contracts justify them. The user's examples of multiple equivalent
specifications and multiple implementations are illustrations, not a prescribed
new abstraction. Reuse existing structures; do not invent a parallel framework
merely to resemble those examples.

## Priority and unfinished work

1. Library coherence is the highest priority.
2. Preserve useful mathematics, particularly formalized mathematics.

The user authorizes improving useful unfinished work before or after merging.
Choose the order by architectural coherence and actual dependencies. Do not
force every draft into public imports. Keep useful deferred mathematics intact,
with exact source pointers, an explicit local issue owner and concrete next
steps. Preserved or uncompiled does not mean accepted or fully integrated.
Retain useful stronger results, counterexamples, source corrections, witnesses,
domains, partiality, occurrence/order distinctions and explicit cost models.
Do not preserve redundant active interfaces solely to preserve old filenames.
Retain old source/evidence in the immutable history while proving the required
specializations or correspondence for a coherent replacement.

## Governing workflow and current user exceptions

Follow the pinned master `AGENTS.md`, README, domain guidance, architectural
standard, applicable ADRs and skills. Use `implement`, the shared review loop,
example-driven development and statement review. The current exceptions are:

- **Issue/spec tracking is local and persisted in this checkpoint.** Do not
  create or update GitHub issues/comments to satisfy the tracker instructions.
- **Nix is optional. Pinned inputs remain mandatory.** The user supplied the
  unified native kit and authorized its compatible route. Verify actual
  `lean-toolchain`, `lake-manifest.json`, `flake.lock` and required tool identities;
  do not change pins to make setup pass. `docs/RESUME.md` owns current setup.

The 2026-11-03 native kit is byte-identical to the copy embedded in001 and its
compiler/dependency hashes match the new master. Its old project statuses and
old fresh-build prescriptions are dated evidence. The current pinned checker,
README triggers and this user's exceptions control.

Record the initial clean state and full specification before edits. Preserve
`review_snapshot.py` baseline/candidate/compare receipts outside the source diff.
Use independent Standards and Spec review on the same exact candidate, retain
stable finding IDs and unresolved scope across corrections, and perform the
applicable full build, exhaustive axiom audit and immediate candidate verification.
Historical external-agent approval does not approve the new integrated candidate.
Focused compilation is development evidence only. No admissions, new application
axioms, narrowed public coverage or altered proof policy are permitted.

## Preservation and ADWH lessons

Inspect all preserved source refs and paper records, not only three current tips.
Use compact capability-level dispositions: integrated; generalized with checked
specialization; replaced with proved correspondence; corrected with rationale
and retained counterexample; or preserved pending work with a named owner.
Inspect current issues149/458/459 for integration lessons and superseded status,
while keeping this task's tracker local. A successful build and review of a
selection is not evidence of exhaustive mathematical capability preservation.
Source-page coverage, compiler validation and whole-book completion are distinct.
See the compact `analysis/` reports and original evidence pointers.

## Durability and setup limits

The checkpoint's `docs/DURABILITY.md` remains binding on the coordinator and all
delegates, including recovery, setup, cleanup and documentation. After a wipe or
missing/incomplete recovery material, explicitly request the latest durable
archive, wait, verify and restore it before project work. A verified attached
archive is sufficient; an old sidecar receipt is not required.

Before another extended phase, handoff or session end, save substantial source,
paper, recovery and packaging milestones. A checkpoint is complete only after
integrity/recovery checks and an observed successful `create_library_file`
owner-root upload with `directory_id` omitted. An unavailable, failed or uncertain
upload requires prompt user notification and a stop in further project work.

Keep setup bounded: ten minutes, one documented route, at most one concrete retry.
Record blockers honestly, then continue useful paper/source work if allowed by
the relevant gates. Do not turn environment repair into the project. Checkpoints
must be self-contained, serially numbered and free of new nested checkpoint
copies, partial downloads, installed toolchains, caches and recursive inventories.
The exact inherited archive blobs already in the pinned Git history are retained
once to preserve the original commits; they are not a general archive exception.

## Completion boundary

A coherent merged candidate requires the same-current-candidate implementation,
connected mathematical consumers, applicable validation and both review axes.
The whole integration remains open while required capabilities or findings lack
dispositions or required gates are blocked. A bounded accepted component may
coexist with explicitly owned unfinished research. No remote publication has
been requested; local integration commits and checkpointed patches are sufficient
delivery artifacts for this session.
