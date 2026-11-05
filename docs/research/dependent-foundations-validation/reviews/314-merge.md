# Issue 314 merge evidence

Accepted candidate `3484ce523bf23524f715a3a2029c290a2d43c4c0` by fast-forward on `integration/dependent-foundations-314-320` in `/tmp/conaled-314-320/integration`.

- Acceptance time: 2026-11-04T23:40:44.409259+00:00.
- Required and observed integration base: `9b0a0fe143c6f97f399632d4bb34a179db012181`.
- Approved candidate and resulting integration tip: `3484ce523bf23524f715a3a2029c290a2d43c4c0`.
- Approved and resulting tree: `878dc22c59f05c46b4ba806e07068ee300ef6baa`.
- Candidate source: `/tmp/conaled-314-320/314`, branch `research/dependent-structure-314`.
- Both source and integration checkouts were clean before acceptance and after the fast-forward. Exact HEAD and branch identities were asserted before and after integration.
- `direnv exec . ./check.sh --verify-candidate HEAD` passed immediately before acceptance in the candidate checkout. See [verification log](314-merge-verify.log).
- `git merge --ff-only 3484ce523bf23524f715a3a2029c290a2d43c4c0` passed. See [Git log](314-merge-git.log). No merge commit, conflict resolution, source edit, or commit rewrite occurred.
- Reused [review approval](314-review.md) for this exact base and candidate: independent Standards and Spec each passed with zero findings. The approval records the 1014-module candidate build, exhaustive proof audit, audit regressions, and final candidate verification. [Handoff](314-handoff.md) and [orchestration](../specs/orchestration.md) remain the scope references.
- Local master remained `9b0a0fe143c6f97f399632d4bb34a179db012181`. No tracker operation or push was performed.

This integration preserves the review record's stated mathematical limits and successor obligations.
