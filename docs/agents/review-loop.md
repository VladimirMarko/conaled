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

## Reuse across review entry points

Use one ordinary review loop and finding record for a task's acceptance scope.
`implement`, direct `code-review`, and optional `originator-review` may refer to
that same loop; invoking another entry point does not require another review
of an unchanged candidate. Reuse completed Standards and Spec outcomes only
when base, candidate, requirements, applicable standards, and validation inputs
match. Record that reuse rather than dispatching the same reviews again.

The coordinator reconciles findings and evidence; it does not perform a third
Standards or Spec review. Originator review assesses retained intent directly
in the originating session. When requested during implementation, collect its
findings with ordinary findings before preparing the next candidate where
practical. Its corrections go through the existing implementer and reviewer;
reuse them while available, or hand their record to replacements.

A changed candidate still requires both ordinary axes to review the full task
scope. Retain prior analysis and matching validation evidence so reviewers can
focus on changed content, affected dependencies, and unresolved findings without
repeating unchanged exploration. A no-change originator assessment does not
invalidate ordinary approval. Originator review cannot replace either ordinary
axis, and ordinary review cannot claim the originator's retained intent.

## Validation of the candidate

Validate the captured candidate in an isolated checkout using the repository's
development environment and required checks. Earlier results may be reused
only with evidence that the validated source tree, dependencies, configuration,
and other relevant inputs match this candidate. Record the commands, results,
input identity, and coverage in the review record.

For integrated Lean verification, run `./check.sh --candidate HEAD` in the
captured candidate's isolated checkout, adding `--fresh` when README requires
it. Preserve the reported commit and `.lake/verification.json` with the review
evidence. Immediately before acceptance, run `./check.sh --verify-candidate HEAD`
in that checkout and confirm that its resolved commit is the approved candidate.
A failed or mismatched record check requires investigation and applicable
revalidation. The record covers the build/axiom audit only; retain evidence for
other required tests and both review axes. Before/after input checks do not
replace checkout isolation or prove absence of transient edits and undeclared
external inputs. For tasks that do not require integrated Lean verification,
retain the artifact-appropriate checks described in README.

A live-checkout check may depend on unrelated edits excluded from the review
snapshot. When those inputs differ or their identity is uncertain, run the
applicable checks against the captured candidate. Missing or failed required
validation prevents passing; report limitations explicitly. Apply this rule to
every correction candidate and verify the final delivered task content matches
the approved snapshot, accounting for recorded unrelated exclusions.

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
