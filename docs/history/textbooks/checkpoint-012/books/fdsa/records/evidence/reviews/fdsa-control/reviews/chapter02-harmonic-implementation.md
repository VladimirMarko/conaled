# Chapter 2 shared numerical quicksort mean — implementation handoff

## Saved checkpoint 0090 boundary

This continues the existing authorized Chapter 2 loop. Root approved the complete
read-only plan in `provenance/chapter02-harmonic-preparation-20261104/` and released
exactly two new numerical source files after the uniqueness author readback.
At that checkpoint the source-only draft was coherent but **uncompiled, uncommitted, and unaccepted**.
No Lean or Lake invocation, dependency-cache mutation, public import, coverage-map,
tracker, existing-source, or pin change was made.

The author worktree is `conaled-ch02-three-way`, branch
`work/fdsa-ch02-three-way`, at unchanged
`3b727e83fcf9f00ad7d0c95d07305b036ebecbca`. Only the two owned new files are
untracked. Exact status, hashes, sizes, and all 24 declaration names are recorded
in `provenance/chapter02-harmonic-author-draft-20261104/checkpoint0090-boundary.json`.
The pre-edit frozen scope and case inventory are in the same directory's
`start.json`.

## Implemented source scope

`Applications/Resources/QuickSortMean.lean` proposes the exact real closed
expression `8*(n+1)*harmonic n - 12*n + 1`, its base, weighted successor,
scaled prefix-sum and positive-size recurrence. A generic real sequence with
explicit base and recurrence is connected to that expression. The predecessor
form is restricted to positive sizes. Nonnegativity, the positive-size
`16*n*(1+log n)` bound, the eventual natural-log bound and binary-log bound
`32*n*logb 2 n` at `n >= 2`, and standard norm-based Big-O statements are included.
There are 15 core declarations, including one private algebra helper.

`Examples/QuickSortMean.lean` contains nine connected numerical cases: exact
values 1, 5, 13 and 71/3 at sizes 0 through 3; generic recurrence specialization
at size 3; scalar binary-log bound failures at zero and one for every real
constant; the explicit size-two bound; and generic standard binary-log Big-O.
All numeric expectations and domains retain the approved plan. These are source
proofs awaiting compilation, not claims that a compiler has checked the cases.

The module imports existing Mathlib harmonic, logarithm and asymptotic APIs.
It has no algorithm or probability import and does not postulate an execution
recurrence. Actual random-pivot and uniform-input mean bridges remain with their
separate authors. No acceptance or probability coverage follows from this draft.

## Work pending at checkpoint 0090

All source statements and proof bodies in the two files have been read back;
there is no identified mismatch in the frozen mathematical contract. The complete
durable per-claim assessment still needs finalization. After root releases the
checkpoint hold, finish that record, perform the scoped staged whitespace check,
make the authorized local Conventional Commit with the required per-command
identity, and return the exact immutable candidate for root's central compiler.
No local build or cache work is authorized.

**Historical checkpoint 0090 HOLD:** this boundary was captured and the hold
was subsequently released by root. The current candidate status is below.


## Completed source candidate after checkpoint release

Candidate: `012ff45e3bd34a36b67e62a8cc2ee00125613e53`. Parent: `3b727e83fcf9f00ad7d0c95d07305b036ebecbca`.
Commit: `feat(resources): solve numerical quicksort recurrence (#174)`.
Author and committer: `ChatGPT <chatgpt@openai.com>`, supplied per command.
The worktree is clean. The commit adds only the two authorized new files,
283 lines total, and preserves all existing source, pins, and history. The
source bytes are exactly those captured untracked in checkpoint 0090.

| File | Lines / bytes | SHA-256 |
|---|---:|---|
| `Applications/Resources/QuickSortMean.lean` | 215 / 9,714 | `6ac46b57a39ad60eaae10d6b90ac4c46c9cbdc02d5caf214097b1e794d03794b` |
| `Examples/QuickSortMean.lean` | 68 / 2,488 | `924ce55ee6af374b55cea67ee6f2da25997b5a81ad098e2e3789622bd793b904` |

### Complete source assessment

`provenance/chapter02-harmonic-author-draft-20261104/source-assessment.json`
contains exactly 24 separate source-level assessment rows: 15 core
declarations (one numerical definition, 13 public theorems, and one private
helper), and all nine example theorems. Its SHA-256 is
`3895228bec19ff2b972e44b8e865f380bb3daf9613f40575cef2b784492bba20`.
Each row records the exact declaration source, quantifiers and hypotheses,
intended claim, proof/case connection, and its domain boundary. The whole
source and staged diff were read. No source-contract mismatch was found.
This is the author's source assessment, not elaborated statement evidence
or an independent review.

The numerical definition retains Mathlib's rational harmonic sequence cast
to Real and the exact coefficients 8, 12 and 1. The weighted successor and
scaled-prefix identities include zero only where their mathematics permits
it. The positive recurrence and predecessor identity require positive size.
`eq_closedForm` has only the explicit real-sequence base and positive-size
recurrence; no extra positivity, monotonicity, finiteness or execution
premise is silently added.

The nonnegative result is derived. The natural-log estimate requires
`1 <= n`; both scalar `n log n` estimates require `2 <= n`. The two Big-O
statements use the standard `Asymptotics.IsBigO`, `Filter.atTop`, an explicit
Nat input domain, Real outputs and actual norm bounds. Binary logarithm
means `Real.logb 2`, with coefficient 32, not a substituted natural ceiling
logarithm.

The frozen expected values are 1, 5, 13 and 71/3 at sizes 0 through 3.
`sequence_three` connects the generic recurrence theorem to the last value.
The two negative boundary cases quantify over every real constant and
show why zero and singleton cannot satisfy the scalar binary-log bound.
`two_log_bound` exercises the first valid size through the public estimate,
and `sequence_binary_growth` connects the generic recurrence solution to
the standard binary-log Big-O result. No probability theorem follows until
the separate actual clients prove their recurrence and transport premises.

### Validation and current hold

The scoped staged `git diff --cached --check` completed with exit 0 and no
output. Staging and the commit contained only the owned source pair. The
source hashes and Git blobs were reconciled with the committed objects,
and the final status was empty. Exact metadata and the complete source
diff are in `result.json` and `source.diff` in the same provenance directory.

**No Lean/Lake compilation has been run for this numerical pair.** The
proof scripts and all examples remain uncompiled development. Root owns
the immutable focused build, full elaborated-type assessment, actual
execution bridges, public import and coverage integration, applicable
complete candidate check/audit, independent review gates and immediate
candidate verification. No acceptance or new coverage status was asserted.

**Current HOLD:** all author source, reference, provenance and control
writes stop after this handoff, pending root's next bounded instruction.


## First actual numerical diagnostics and proof-only successor

Root supplied emitted diagnostics from the still-live central attempt 5 at
`c0440a99c2a503b7816a44367f7e4168378dbbf1`. The secured observed-prefix log
contains 32,431 bytes, SHA-256
`b45bded7778156f7829c4fc80e374276edcc9252ea433f848dbb89ac58239126`,
and is preserved in
`provenance/chapter02-focused-attempt5-partial-diagnostics-20261104/`.
The complete numerical diagnostic section was read. These are actual emitted
core failures, not a secured terminal aggregate result.

The findings were unused `<;>`/`ring` tails after field simplification at the
original lines 36, 58, 70 and 180, plus a mismatched orientation of the additive
inequality helper at line 155. The repair uses sequential useful tactics at
line 36, removes the already discharged tails at 58/70/180, and derives the
unchanged additive inequality directly by linear arithmetic from `hdiv`.
No linter is suppressed and no recurrence, coefficient, hypothesis, bound,
example, import or option changes.

Successor: `e0df28b7bbfa722b25623606a5a1905620fac91e`; parent `012ff45e3bd34a36b67e62a8cc2ee00125613e53`.
Commit: `fix(resources): repair numerical mean proof elaboration (#174)`. Only
`Applications/Resources/QuickSortMean.lean` changes (7 insertions, 6 deletions).
Its 216 lines / 9,673 bytes have SHA-256
`888bae2d149f2664f41e37f702ce5352718ac2d008f13fa51952239d85e5d09a`.
The nine-example file remains byte-identical, SHA-256
`924ce55ee6af374b55cea67ee6f2da25997b5a81ad098e2e3789622bd793b904`.
All 24 declaration source headers, including the 23 public contracts, were
compared byte-for-byte with the parent and are unchanged. The exact five-hunk
diff and 24-row source assessment are in
`provenance/chapter02-harmonic-proof-repair1-20261104/`.
The scoped staged whitespace check exited 0. Author and committer were supplied
per command as ChatGPT <chatgpt@openai.com>; the resulting worktree is clean.

The successor remains **uncompiled development**, with no new type inspection,
audit, independent review or acceptance. Root retains the central compiler
and all final gates. No local build, cache change or child agent was used.
**Current HOLD:** all source/ref/control/provenance writes stop after this
receipt, pending the parent's next bounded release.
