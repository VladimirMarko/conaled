# Blocking durability and recovery contract

This is the single authority for durability, interruption and restart gates.
It applies to the coordinating agent and every delegate, including during
recovery, setup, archive cleanup, documentation and mathematical work.
Preparatory work has no exemption. The workspace is disposable.

## Gate 1: establish recoverable input before work

At session start, and after any disconnect, reset or suspected wipe, make only
the minimal check needed to establish whether the expected files still exist.
If the workspace was wiped, or the expected checkpoint/source is absent or
incomplete, **stop project work and explicitly ask the user to attach the latest
durable checkpoint archive. Wait for it.** Do not resume implementation, cleanup,
integration or environment setup while this request is unresolved.

Use the archive supplied in the current conversation, verify its integrity and
declared source identities, and restore into a fresh directory before resuming.
An attached and verified durable archive is sufficient recovery input; recovery
must not require a separately retained old upload receipt. If the latest archive
is unavailable, ask which available checkpoint the user authorizes recovering
from. Never silently select an older cut.

Conversation summaries, remembered paths, a subagent handoff and partial files
are navigation aids. They cannot reconstruct authoritative Lean source, proof
evidence, source identity or acceptance status. A corrupt/incomplete archive
remains a blocker; request the correct material rather than editing checksums
or inferring missing proof data.

## Gate 2: make progress durable before the next extended phase

Checkpoint after a substantive mathematical milestone, useful incomplete work
that would be costly to recreate, or a substantial recovery/packaging milestone.
Do this **before starting another extended phase**, before a handoff, and before
ending a session with new work. Save a verified intermediate checkpoint when
needed; do not postpone every save until final cleanup or polish is complete.

First pause writers and preserve all useful source and paper mathematics at
their canonical owners. Then build a self-contained archive and verify its
payload and recovery. Follow `CHECKPOINTS.md` for the mechanical pack/upload
procedure. Local metadata verification is not Lean acceptance.

A checkpoint is complete only when BOTH conditions hold:

1. The exact self-contained archive has passed its integrity/recovery checks.
2. `create_library_file` has returned an observed successful save of that file
   to the owner's root, with `directory_id` omitted.

A local archive, sandbox/download link, planned filename, successful pack,
attempted upload or agent report is not a durable-upload receipt. Report a
planned or locally verified artifact using those exact qualifications. Declare
it saved/delivered only after the successful result is observed, and provide an
actual file link. Keep the filename, byte size, SHA-256 and returned identity
together in the delivery record. The receipt follows creation of the immutable
archive and need not be embedded inside that same archive.

## Gate 3: upload failure blocks further accumulation of work

If the required upload capability is absent, denied, fails or returns an
uncertain result, **tell the user promptly and stop further project work**.
State the observed blocker, the local filename/size/hash, and that durability
has not been confirmed. Preserve the local bytes. Further project work waits
until durable saving succeeds or the user explicitly directs a different course.

Allow only the bounded capability check/retry in `CHECKPOINTS.md`; an uncertain
result must be resolved before another create. Do not silently change upload
routes, install upload infrastructure or launch an environment-repair campaign.
A known successful create followed by local metadata-helper failure is already
a saved file; report/fix that metadata separately without duplicating the upload.

## Delegation and successors

The coordinator owns the save. Files produced by delegates in the shared
workspace remain transient until included in a verified, durably uploaded
checkpoint. A delegate must report missing recovery material or a durability
blocker immediately and must not treat another agent's memory as source.

Every successor preserves these gates, the self-contained structure, the
increasing delivery serial and the anti-bloat rules. Do not weaken them because
the current environment makes compliance inconvenient. A user-authorized
contract correction must preserve mathematical bytes, document its rationale
and undergo appropriate verification before its own durable upload.
