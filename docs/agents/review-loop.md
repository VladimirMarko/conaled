# Review-and-fix procedure

Read this before coordinating a ticket, integration, or whole-task review loop.
The calling workflow assigns a reviewer and an implementer, supplies the spec
and standards pointers, and chooses the review base. Reading this procedure
does not create another agent layer. The reviewer coordinates corrections;
the implementer implements an assigned iteration and returns, without
recursively launching the enclosing workflow. `code-review` retains its
independent Standards and Spec subagents.

## Candidate and record

Pin each round to immutable base and candidate commit SHAs and record the spec
version or saved contents used for acceptance. Keep the base stable across
ordinary fixes so each round covers the whole task change. For a ticket that
incorporates a newer integration tip, use that exact incorporated integration
commit as the next round's base, verifying it is an ancestor of the candidate.
This excludes other tickets' integrated changes while including the ticket's
remaining changes and its conflict resolutions. Record the base change and
carry all findings forward; a finding disappearing from the diff is not a
resolution. The full-spec integration review retains its original starting
base. Review snapshot files, not a concurrently edited checkout.

For a current-checkout workflow, capture the task's starting state and each
candidate as stable Git snapshots. A temporary index, `git write-tree`, and
`git commit-tree` can produce synthetic commits without changing the real
index, `HEAD`, branches, or worktrees. Parent every synthetic candidate to the
captured starting-state commit (or a descendant of it), so `code-review`'s
three-dot diff compares against that starting state. Sibling snapshots parented
only to the original `HEAD` would include pre-existing changes in the diff.
Include staged, unstaged, and relevant
untracked task files; preserve unrelated user changes and record exclusions.
Use a stable capture window with the implementer paused, then release it only
after capture completes. Keep the snapshot objects reachable for the loop's
lifetime. No tickets, branches, or worktrees are required by this procedure.

Maintain one review record outside the source diff, accessible to the reviewer
and implementer. Record each round's SHAs, spec version, validation results,
and findings in separate Standards and Spec sections. Give findings stable
identifiers and retain their status across rounds: unresolved, fixed with
review evidence, or explicitly resolved with a documented reason. A fresh
review does not erase prior findings.

## Repeat until passing

1. Run `code-review` with the pinned base, candidate, spec, and existing finding
   record. Both axes review the full candidate, including prior corrections.
2. Reconcile the reports with the record. The reviewer verifies proposed fixes
   and any reason offered to resolve a finding without a change. Keep disputed
   findings unresolved until the requirement or disposition is established.
3. Send unresolved findings to the implementer with their identifiers. The
   implementer returns corrections and relevant validation evidence. Capture
   the resulting candidate and repeat review, including for improvements made
   independently of the findings.
4. Pass only when both axes have no unresolved findings on the same candidate.
   Return the base and candidate SHAs and both reports with the finding record.
   Before merging or declaring completion, the caller verifies that the result
   being accepted matches that candidate. Later edits, integration conflict
   resolutions, or other changes require a new round; an older approval does
   not approve a newer tip.

If a dependency, missing decision, or repeated lack of progress prevents
resolution, return the latest candidate, unresolved findings, attempted fixes,
and the specific blocker to the caller. Leave completion pending; do not turn
an iteration limit or an unavailable reviewer into approval.
