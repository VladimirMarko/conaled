# Chapter 2 — independent Spec review, round 1

## Outcome

**Blocked pending exact integrated validation.** Full-scope static Spec review
is complete. I found **zero unresolved implementation or source-coverage
findings** and request no code correction on this candidate. This is not a
passing acceptance review: CH02-PRE-005 remains open, and the isolated chapter
checkout has no `.lake/verification.json` at the time of this review.

- Reviewer: `/root/chapter02_review/spec`.
- Date: 2026-11-02.
- Fixed base: `82501d108f33c62d21b5e0d0f7d2376b902d8d49`.
- Candidate: `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`.
- Read-only checkout: `validation-chapter02`, branch `pfds/ch02-review-r1`.
- Full scope: 38 changed files, including 35 Lean files; 4,464 insertions and
  4 deletions in 31 commits. No exclusions or omitted uncommitted task work.
- Review diff: `git diff 82501d108f33c62d21b5e0d0f7d2376b902d8d49...69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`.
- Commit list inspected with `git log --oneline 82501d108f33c62d21b5e0d0f7d2376b902d8d49..69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`.

The review covers the whole chapter implementation and its two FRP import-list
prerequisite changes. It does not inherit approval from earlier worker builds,
the preparatory audit, or the separately pending #10013/#10018 loops.

## Requirements and input identity

The acceptance specification is the complete saved user request, its union
clarification, and Chapter 2 requirements version 1. Fingerprints inspected:

| File under `session/` | SHA-256 |
| --- | --- |
| `requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `requirements/chapter02.md` | `240b6bfec9f9e8599f1034abc309499928c8472edf76481b553ef99ce40ff944` |

I confirmed exact candidate HEAD, a clean worktree, and that the merge-base is
the supplied fixed base. Every one of the 38 changed source files matches its
SHA-256 in `validation/chapter02-candidate-r1.json`; the manifest neither omits
changed files nor adds unrelated paths. These identity checks establish the
read snapshot, not compilation or proof-audit success.

I read the supplied book's complete Chapter 2 text, printed pp7–16, and used
the previously completed visual figure/exercise inventory in
`research/book-full-inventory.md`. The independent source identity is the
232-page supplied book, SHA-256
`b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
I also inspected the book/thesis crosswalk and its source distinctions. The
thesis's Chapter 2 is a lazy-stream development assigned to book Chapter 4;
its trace/debit analysis belongs with later amortization work. The current
chapter correctly does not claim those developments or the whole union.

Applicable review guidance read includes AGENTS.md, the shared review loop,
architectural-quality and domain guidance, GLOSSARY, ADR 0001, ADR 0010,
example-driven-development statement review, code-review and its heuristics,
and README's candidate-validation rules. The user's local-ticket and no-GitHub
instructions remain controlling. No compiler, build, source/ref/dependency
mutation, or external write was performed by this reviewer.

## Source-to-statement assessment

### Stacks, append and source integer update

`Sequences.AbstractStack.Ops` contains only the five source operators.
`Laws` is a separate relational observation contract, permitting validity
invariants without a total decoder. The relation is demonstrably satisfiable:
`lists_laws` uses ordinary lists and `custom_laws` uses an actually distinct
inductive `Stack`. Empty tail failure is distinct from a successful empty
tail, and the head law similarly retains empty failure.

`appendRun` calls only the supplied operators. `appendRun_correct` proves
sufficiency of any fuel at least the observed left length; no successful
valid call is justified by assuming its result. The exact `4*n+1` count
matches the executed emptiness/head/tail/cons calls, including the terminal
emptiness call. `appendDirect_eq`, `lists_appendRun`, and `custom_appendRun`
connect both implementations to ordinary concatenation. The retained examples
use those public results, including excess fuel, empty left input, and the
composed append/head client.

The reused shared-list implementation traverses actual tail references,
allocates on successful return, and proves the original right-root identity
after append's copied prefix. `Extends` preserves old represented versions;
its meaning is cell preservation, not merely a version-name convention.
`updateRun_success` states the exact `List.set` value, copied-prefix frontier
increment and untouched-tail identity, while out-of-range failure is explicit.

`IntegerUpdate` genuinely decrements an `Int` in its source recurrence. The
nonnegative refinement is equality of the complete measured raw-fuel
execution, including malformed roots and insufficient fuel. The negative
theorem requires a represented finite list and sufficient fuel, then proves
failure after `length+1` visits. It does not substitute an early negative
check. The public frontier supplies sufficient fuel; the all-integer square
covers both signs. The examples exercise -1, -20 and a successful interior
replacement through the new public theorems. Mathematical integer and unit
cost qualifications are explicitly documented.

### Exercise 2.1 and the shared-space claim

`suffixesRunFuel` follows the actual input tail fields and returns those roots,
including null. Correctness relates them in order to `List.tails`, proves
root count `n+1` and non-null count `n`, and proves distinctness from the
backward-reference invariant. The additional `SuffixChain`, `ClosedRoots`,
`Reaches`, and `suffixesRun_reachable` results justify interpreting those
counts as the reachable element cells; equal suffix values alone are not
used as a sharing proof. `nonnull_nodup` excludes overcounting. The explicit
space model charges those `n` element cells plus `n+1` outer list cells,
with linear asymptotic theorems. It does not claim total heap occupancy,
stack space, allocator metadata, garbage collection, or a Lean runtime bound.
This inspection confirms the required reuse, while #10013's own acceptance
gate remains separate.

### Ordered values, finite sets and baseline comparisons

The representation is Mathlib `BinaryTree`. Independent `Contains` and inorder
`entries` inspect both children. `OrderedBy` constrains every descendant,
not just child roots. For sets, lawful `LinearOrder` supplies coherent strict
order and equality. The `badDescendant` example exposes the difference between
the actual invariant and the inadequate child-root-only condition.

`member_correct` links directed search to whole-tree membership under that
invariant. `memberRun` charges each executed strict comparison: one on a left
step, two on a right or equal step, and zero at empty. `memberRun_bound` proves
at most twice the node-height. The valid right-spine family attains the bound
and has size equal to height, preventing an unsupported balanced-tree claim.

Baseline insertion preserves the strict invariant and adds exactly the target
to independent membership. Pairwise increasing inorder entries, `Nodup` and
the explicit length/node-count theorem witness finite unique contents.
`AbstractSet` separates operations, validity and laws; both baseline and
candidate realizations discharge the generic contracts. Its insertion-word
client reuses reachable fold fusion and has connected repeated-key examples.

### Physical baseline insertion and all unaffected subtrees

The store uses the existing fresh-cell allocator and independent `Represents`.
Backward child references prove a sufficient public frontier bound on height;
they are not an assumption that the desired output already exists. General
trees permit shared children; ordering is a separate client hypothesis.

`insertRunFuel` reads actual cells and allocates only on recursive return.
`insertRun_correct` ties that execution to the independent value insertion,
heap extension, exact comparison/visit/cell profile, frontier increase and
`Rebuilds`. A match returns its existing subtree; strict ancestors are still
copied. The baseline duplicate example therefore has one new cell and a
different root even though the resulting tree value is equal.

`Rebuilds.off_path` establishes actual address equality at every divergent
ancestor branch. Its unconstrained focus is not mistaken for endpoint
retention. The separate `insertRunFuel_duplicate_endpoint` reaches the same
old nonempty matched root; `insertRun_duplicate_subtree` adds exact strict
ancestor allocation, old-version retention and every further descendant-path
observation in the final heap. The new examples use a matched node with a
nonempty child, and also exercise a failing observation beyond a retained
leaf. Thus CH02-PRE-001 is resolved in the candidate's formal statements and
connected cases, subject to the final integrated gate.

### Exercises 2.2–2.4

Candidate membership has one strict comparison per visited nonempty node and
at most one final equality. `LowerBound` is the genuine all-descendant bound
that lets a new candidate replace the old candidate; initial `none` satisfies
it. The correctness conclusion is independent membership or equality with
the carried candidate. The `height+1` bound is attained on valid nonempty
right spines. The no-candidate empty case correctly uses zero comparisons.

The aborting and combined physical algorithms distinguish invalid/fuel failure,
duplicate abort, and insertion success. Recursive branches propagate abort;
`handleAbort` occurs once at the public boundary. The duplicate theorems return
the identical original store/root pair and zero fresh cells, rather than only
an equal tree value or a frontier comparison.

Absent execution has the ordinary insertion observation and copied-path
sharing; the independent `ordered_insert`/`contains_insert` laws then supply
ordered finite-set meaning. For the combined algorithm, `candidateProfile`
and `insertCandidateRun_retention` refer to that same physical execution and
include its `height+1` comparison bound. Its path continues to empty, even
after passing an equal key, which is reflected in the differing duplicate
visit counts. These are not two separate implementations being counted as
one joint solution. Both raw refinements work on arbitrary represented tree
values; ordered-set claims add the appropriate separate hypothesis.

### Exercise 2.5(a,b)

`completeValue` has the independently proved height and unfolded node count;
`completeRun` recurses once per level and stores its returned root in both
child fields. The execution theorem proves exactly `d` fresh cells and
`d+1` visits. `completeRun_children` states actual stored-root sharing.
Repeated payloads are deliberately not subjected to the strict set invariant.

`Fits` separates uniform contents, exact unfolded size and recursive
`SizeBalanced`. Both child-size inequalities hold at every node. The paired
constructor creates sizes `n` and `n+1`, recursing once on half the predecessor
size and sharing the returned pair in two new parents. The independent value
fits proof and actual execution/child-root proof establish the requested
shape and sharing. Exact counts are `2*log2(n+1)+1` fresh cells and
`log2(n+1)+1` visits; the visit-plus-cell work is logarithmic. Zero requests
still allocate the one-cell companion, which the docs and example preserve.
No minimal live-space or machine arithmetic bound is inferred.

### Exercise 2.6 and observation composition

The abstract map interface has empty, bind and optional lookup; its laws use
functional update. The concrete key-only invariant imposes no payload
equality/order. Whole-tree `observe` is independent of directed `lookup`;
their equality requires ordering. `lookup_bind` legitimately holds at the
weaker directed level for all tree values, and `observe_bind` adds ordering
when establishing the intended finite-map meaning. The valid subtype realizes
the abstract laws and an explicit finite key list witnesses finite domain.
The function-payload and optional-payload examples test the stated generality.

Physical bind and lookup follow heap references. Their counts distinguish
comparisons, visits and allocated cells; bind copies the endpoint as well as
strict ancestors. `WrittenAt` preserves both actual child addresses at an
overwritten endpoint, while `Rebuilds` handles the ancestors' other children.
The root-replacement example has two nonempty children, so it is not vacuous.
Its old root still looks up the previous payload. The universal physical
`bind_lookup` law and `bindThenLookup_correct` connect actual execution to
the same all-query update semantics.

The new relational adapters use existing squares and compose with independently
specified observers. The optional physical bind/lookup composition preserves
outer operation failure, successful missing lookup and a stored optional-none
payload as different results. Optional-root observers similarly distinguish
operation failure from successful empty-root observation. The simpler
append/head observation intentionally uses the existing flattened optional
client and its specification; valid append behavior is proved before that
observation. No result conflates pointer identity with value equality.

### Context, integration and the FRP prerequisite

The destructive append diagram, collection discussion, historical attributions,
and mentioned but unspecified augmented-set operations have explicit contextual
dispositions. They do not create claims to formalize every cited paper, all of
Standard ML, or the Lean allocator. Later stream/effect/history obligations
remain separately owned. This is consistent with the retained full union goal.

The chapter's changed files are in the public import structure through the
added examples and resource module. That source inspection is not a substitute
for the stock coverage guard and exhaustive audit. Both FRP files differ from
the prerequisite's preceding candidate only in import lines: I compared all
non-import text and found exact equality. Their declarations and proofs are
not silently changed by the chapter integration. Compilation remains the
necessary check that the narrower imports supply the required dependencies.

## Prior findings and dispositions

| Stable ID | Spec disposition at this candidate |
| --- | --- |
| CH02-PRE-001 | Implementation closure verified: exact nonempty matched root, strict-ancestor count, old version and arbitrary descendant observations; both retained endpoint examples consume the public theorem. |
| CH02-PRE-002 | Implementation closure verified: actual raw abort/combined traversals, single outer handler, exact original duplicate state, zero cells, absent refinement and bound on the same combined execution. |
| CH02-PRE-003 | Implementation closure verified: `WrittenAt`, `nil_children`, universal physical bind correctness and two-nonempty-child root replacement example. |
| CH02-PRE-004 | Implementation closure verified: physical baseline, optimized and map squares plus meaningful composed observers/examples are present. |
| CH02-PRE-005 | **Open mandatory validation gate.** All expected source families are integrated and identity-reconciled, but no full check/audit/success record/final verification exists for this candidate yet. |

These closures are static source/statement assessments, not an assertion that
integrated Lean checking has completed. There are no additional CH02-SPEC
implementation findings in this round.

## Validation evidence and limits

I inspected the focused records and terminal log lines for the ordered-set
(598 jobs), shared-constructor (1,587), root integer/baseline (669), optimized
(672), pure-map (592), shared-map (666), and terminal-retention (665) passes.
The stack report records its earlier focused pass. Their purpose is development
feedback; none validates the full frozen chapter candidate.

The records' owned source hashes/blobs match the candidate. Two historical
records have an older `SharedTree/Observation.lean` dependency: the constructor
record and physical-map record. I inspected the exact difference: the current
file adds `optionalRootValueSquare`; every prior declaration is unchanged.
The current observation file is separately covered by the root r9 and optimized
focused records. This explains the difference but does not turn either older
closure into exact whole-candidate validation. The full check must check the
integrated imports and all affected consumers.

The currently running prerequisite check is for `226ebae`, not `69f6f00`.
No `.lake/verification.json` exists in the chapter checkout. Required remaining
evidence is a successful stock `./check.sh --candidate HEAD` in the stable
isolated chapter checkout, its exhaustive audit and matching success record,
followed by `./check.sh --verify-candidate HEAD` immediately before acceptance.
The separate prerequisite acceptance evidence and both review axes must also
be reconciled. No acceptance is authorized by this report while these are absent.

## Continuation

If candidate, requirements, standards and input identities stay unchanged,
return the terminal integrated evidence and final verification to this same
reviewer for the validation continuation. Any source change requires both axes
to assess the revised complete candidate against the same fixed chapter base,
retaining all findings and matching unchanged analysis.

**Final status:** base `82501d108f33c62d21b5e0d0f7d2376b902d8d49`;
candidate `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`; zero unresolved
implementation findings; no implementation severity to rank; CH02-PRE-005
validation gate unresolved; **Spec Blocked**.
