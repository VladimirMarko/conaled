# Exact integration of #317

The root coordinator separately assigned the merger role after independent
review completed. Only the exact approved candidate was authorized for a
fast-forward into `/tmp/conaled-314-320/integration` on branch
`integration/dependent-foundations-314-320`.

Before integration:

- Branch matched the assigned integration branch.
- HEAD was `bb77d67171e6cb610e43149394c8a9b9a0deab3f`.
- Tree was `b63e5284ff39e5c8ea9e2b9da20100cd3857657c`.
- Git status was empty and the expected base was an ancestor of the candidate.
- Both independent axis reports passed with zero findings for candidate
  `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96` against that base. Full reports are
  `317-standards-round1.md` and `317-spec-round1.md`; `317-review.md` retains the
  approval and matching full-check/audit/four-fixture evidence.
- Immediately before integration, the merger repeated
  `flock /tmp/conaled-314-320/build.lock direnv exec . ./check.sh --verify-candidate HEAD`
  in the unchanged private candidate checkout. Exit status was 0; output in
  `317-merge-verify.log` matches the exact candidate in incremental mode.

The merger rechecked the expected branch, HEAD and clean state immediately
before running:

```sh
git merge --ff-only 7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96
```

The fast-forward succeeded without conflicts or new commits. After integration:

- HEAD is exactly `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`.
- Tree is exactly the approved candidate tree,
  `6ae33024d4ae668a359ab8333fe3b533b1ced760`.
- Git status is empty and the endpoint diff against the approved candidate is
  empty.

No source edits, conflict resolutions, cache changes, master changes, pushes or
tracker operations were performed. Candidate validation was reused for the
identical integrated commit and tree; no new build claim is made for the
integration checkout. The exact-candidate merger assignment is complete.
