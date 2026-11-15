# Current recovery instruction — 3 November 2026

The current user supplied checkpoint 0069 plus the unified native kit and asked
to resume whole-book formalization and prepare integration. The user reaffirmed
permission for frequent checkpoint uploads and specified that checkpoints are
for recovery of current work, not reconstructing historical project states; keep
them small where possible. Include the updated environment in the next one.

This supersedes older packaging requirements only where necessary to keep
recovery checkpoints small. It does not reduce the full book scope, chapter
order, proof standards, local-only Git/tracker scope, or review/validation gates.

Compact checkpoints retain all reachable Git objects and refs except one large,
unchanged tracked public archive. It is an explicitly pinned external recovery
input, with exact length, SHA-256 and Git blob ID, optionally supplied from a
local seed. Thus the compact archive does not contain every byte offline, but
requires no prior task checkpoint or conversation and restores the exact source
identities. The restore must fail closed on a missing or mismatched input.
The complete unified environment kit is included under tooling/.
