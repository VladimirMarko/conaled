# Checkpoint upload recovery notes

## Checkpoint 0032 — 2026-11-02

The initial official prepared-upload helper ran in the default sandbox, where
its transfer worker could not connect (`operation not permitted`). No Library
finalization request was created or issued. Progress counters were initially
misread as temporary capacity pressure; the user-facing diagnosis was explicitly
corrected after inspecting the actual network-error values. No capacity-error
claim should be propagated from that initial diagnosis.

The exact original transfer worker was identified as a descendant of this
checkpoint's helper and stopped using approved escalation. No compiler or
other job was touched. The helper then returned a definite per-item
`transfer_failed` result; its completion was not treated as a successful save.
Only after that known pre-finalization failure, the same unchanged archive was
retried through the same unmodified official helper with approved network
access. That attempt finalized once and returned successful per-item status
and applied local identity metadata. Its receipt is in `checkpoints.json`.

For subsequent uploads in this request, use the official helper through the
supported escalated execution path for network access. Do not repeat an
unknown finalization, run concurrent duplicate uploads, switch to a direct
write, change returned session data, or expose transfer URLs. A known
pre-finalization transfer failure is distinct from an unknown write outcome.
This note retains no transfer credential, URL or private error body.
