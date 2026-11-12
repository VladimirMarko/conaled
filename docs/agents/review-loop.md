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

Use `scripts/review_snapshot.py` for Git capture and comparison. Before editing,
run `baseline` with explicit task scope; for an existing committed baseline,
use `validate`. Before each review, run `candidate` for current-checkout work
or `validate` for an existing committed candidate. Save the complete JSON
receipt outside the checkout and give it to the reviewer with the full
requirements. See the [CLI reference](#snapshot-cli-reference) for manifests,
mixed ownership in one file, and ticket/integration modes. A failed command or
incomplete JSON output supplies no candidate evidence.

Pause writers during capture. The helper preserves the real index, HEAD,
branch and working files, constructs through a temporary index, and retains
immutable commits under helper-owned refs. It does not establish ownership or
prevent other processes editing the checkout. Scope and same-file projections
remain the caller's responsibility. Inspect the returned diff command and
inclusions/exclusions before releasing the stable capture window. Synthetic
candidates descend from the captured base; sibling snapshots parented only to
the original HEAD would incorrectly include pre-existing unrelated changes.

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
every correction candidate. Immediately before acceptance or merge, run the
helper's `compare` against the accepted commit or paused live checkout with the
approved receipt and explicit exclusions. A mismatch requires another review
round. Retain its output alongside the independent review and validation
records. This content comparison does not certify execution of validation or
its external inputs.

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

## Snapshot CLI reference

Run commands through `direnv exec . python3 scripts/review_snapshot.py` (or
`nix develop --command python3 scripts/review_snapshot.py`). Each command takes
`--repo /absolute/worktree/root`. Successful output is one complete JSON object;
errors go to stderr with a nonzero exit. Store manifests, projections and
receipts outside the checkout so they do not become unclassified inputs.
The public regression suite is `python3 scripts/test-review-snapshot.py` in
the development shell; it needs Git and Python, not a Lean build or credentials.

A manifest has exactly these fields:

```json
{"scope": ["path/to/task-file", "path/to/new-file"], "entries": {}, "exclude": []}
```

`scope` lists literal task paths, including additions and deletions. Paths may
contain spaces/newlines but must be relative, without traversal or `.git`
components. A missing scoped file denotes deletion. Normally leave `entries`
empty: scoped paths use their current bytes and modes. `exclude` names unrelated
paths explicitly excluded from the baseline's live input. Tracked exclusions
retain HEAD's content; untracked exclusions remain absent. Other tracked files
use their live state in the baseline, including staged/unstaged edits. Every
nonignored untracked path must be in scope, entries or exclude. Ignored files
are included only when explicitly named. Candidates retain all non-task
content at the baseline version, independently of later unrelated live edits.

`entries` provides deliberate overrides. A `live` entry is
`{"source":"live"}`. For mixed ownership or pre-existing task work, supply:

```json
{"source":"file", "file":"/outside/checkout/projected-bytes",
 "mode":"100644", "expected":{"mode":"100644", "sha256":"actual-live-byte-hash"}}
```

Use `observe --manifest M` to obtain the `expected` descriptor from `sources`.
Use `expected: null` for an absent source. Allowed modes are `100644`, `100755`
and `120000`; for a symlink, supplied bytes are its target text. An override
`{"source":"delete","expected":...}` deliberately removes the path from the
snapshot. Keep projected content stable too. Outside baseline capture, overrides
must be within scope. The manifest records exclusions and overrides; the helper
never guesses which lines belong to the task.

| Operation | Arguments and result |
|---|---|
| `baseline` | `--manifest M [--mode whole\|integration]`; capture starting state before edits. Removing pre-existing task changes uses projected bytes only; live files remain intact. An identical existing commit is reused. |
| `candidate` | `--manifest M --record BASE_OR_PREVIOUS_RECEIPT`; capture scoped live content against the record's fixed base, retaining unrelated baseline content. Save a separate receipt for every correction. |
| `validate` | `--manifest M --base B --candidate C [--mode whole\|integration] [--record PREVIOUS_RECEIPT]`; resolve committed inputs once, require base ancestry and reject undeclared changed paths. Entries must be empty because committed bytes are authoritative. No synthetic commit is made. |
| `validate` (ticket) | Add `--mode ticket --incorporated I --original-base ORIGINAL`; `B` must equal `I`, which must be an ancestor of `C`. For a later incorporation supply the previous ticket receipt; the new base must descend from the old one. Carry findings forward outside the helper. |
| `compare` | `--manifest M --record REVIEWED_RECEIPT --accepted COMMIT_OR_LIVE`; compare accepted scoped bytes and modes with the reviewed candidate. Save its successful result before acceptance. |
| `release` | `--record RECEIPT`; release that receipt's owned refs after the review lifetime. Each receipt retains its own base/candidate refs; release all completed rounds separately. |

For whole-task and full-spec integration review, preserve the initial base in
every record; supply the previous receipt for ordinary correction validation.
A fresh `validate` cannot infer an earlier agreement, so the coordinator must
retain the original full-spec base. Ticket incorporation changes only the
ticket base, not that original base or unresolved findings. For committed-only
review without a dirty starting state, `validate --base B --candidate B` can
record the initial base. It is a baseline, not a passing empty-diff review.

For final comparison, full-owned paths are read from the accepted input. A
same-file projection must carry the identity of the actual accepted file:
replaying an old projection after that file changes fails. If only unrelated
lines changed, supply a fresh explicit projection tied to the current bytes;
then unchanged task content passes. This is caller classification, not automatic
ownership inference. An outside-scope change is ignored for task comparison,
but still changes the full observed source identity. Capture a new candidate
and review it whenever task content or an integration resolution changes.

Receipts include resolved base/candidate/tree IDs, effective tree entries,
`scope_identity` for the path set, `projection_identity` for the manifest,
`source_identity` for observed live descriptors, and `content_identity` for
captured tree descriptors. `excluded` lists paths outside task scope;
`manifest.exclude` separately records exclusions from baseline capture.
`diff_command` supplies the three-dot comparison.
A dirty live checkout can have matching task content and different validation
inputs. Associate external dependency/toolchain/configuration identity and
actual test execution evidence with the exact candidate separately; this helper
does not run checks, certify receipts from `check.sh`, store review decisions,
or change optional originator review.

The supported adapter is POSIX Python plus the installed Git CLI, in a
repository with an existing HEAD commit. It uses raw
bytes without clean/smudge filters, an isolated temporary index, and Git object
and ancestry operations. Symlink parents, submodules, skip-worktree entries and
unresolved index conflicts are rejected. Supply ordinary non-sparse worktrees;
linked worktrees are supported. Inherited `GIT_*` overrides other than
`GIT_PAGER` are rejected. No hooks, checkout, reset, stash, branch changes,
network operations or automatic merges are performed.

Before/after index, HEAD, branch, file and inventory checks reject observed
interference. The helper lock coordinates its own invocations, not editors;
endpoint equality cannot prove absence of transient edits or that all observed
files coexisted. Pause other writers and validate in isolation. Git, OS reads,
process execution and hash correspondence remain adapter assumptions, not a
proved library refinement. The helper's source identity covers the observed
inventory, not undeclared ignored files or external dependencies.

Retention uses random refs under `refs/conaled/review-snapshots/` and matching
ownership metadata in Git's common directory. Release verifies the record and rejects symbolic retention refs, even if
their resolved OIDs match. Creation and deletion use non-dereferencing Git
transactions with expected-value checks. If a ref becomes symbolic after the
pre-check, deletion can affect only the named helper ref, never its target.
Git checks the queued updates together; concurrent readers can still observe
a subset of the individual updates. See [git-update-ref](https://git-scm.com/docs/git-update-ref)
for these transaction semantics. Mismatched expected OIDs fail. It never runs GC or removes user work. Interrupted attempts may leave
objects or ownership metadata; inspect the recorded metadata and refs before
recovery, and retain uncertainty about interrupted publication. A complete
metadata JSON object can recover a lost stdout receipt when its refs exist.
This is object lifetime management, not crash-durable backup or authentication
against an adversary who can rewrite the repository and metadata.
