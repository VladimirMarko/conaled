# #316 merge record

The merger fast-forwarded `integration/dependent-foundations-314-320` in
`/tmp/conaled-314-320/integration` from
`f0773fee8fa40214c67606c46ba8c41eed8e674b` to the exact approved candidate
`d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`.
The integrated tree is `a3baf0c1f6213e135371f9f1ee428fc144c6162c`.

The merger read [316-review.md](316-review.md) and
[316-review-final-verify.json](316-review-final-verify.json).
Both independent review axes passed with zero unresolved findings on this
base and candidate. Approval covers the precise-prerequisite outcome and
retained Agda evidence; it does not establish a Lean higher interpretation
or open the higher adoption gate.

Immediately before acceptance, artifact checks run through `direnv exec .
python3` confirmed the clean ticket checkout at the approved candidate and
the clean integration checkout at the assigned base, on their expected
branches. They verified the candidate tree, merge base, all 13 authored files'
SHA-256 hashes and Git blobs, the validation script, the successful validation
record, the reused Agda receipt, both independent review report hashes, and
diff whitespace. The validation record's SHA-256 is
`cac987b345ec903b9dd72d9714e97ebe304a64502a4337b55b2068ff15b3ee50`.

The exact-candidate artifact record supports reuse of the successful fresh
235-module Agda source check. No Agda or Lean compilation was rerun, and no
Lean cache was provisioned. The full evidence remains in
[316-validation-d7d2beeea699bccc2f7eb0fee7f8fa52e6718186.json](316-validation-d7d2beeea699bccc2f7eb0fee7f8fa52e6718186.json).

After a final state recheck, `git merge --ff-only` succeeded. Post-merge checks
confirmed the exact approved tip and tree, the assigned integration branch,
and both checkouts remaining clean. No commit, conflict resolution, or source
edit was introduced. Main/master, trackers, other worktrees, and remotes were
not changed by this merger assignment.
