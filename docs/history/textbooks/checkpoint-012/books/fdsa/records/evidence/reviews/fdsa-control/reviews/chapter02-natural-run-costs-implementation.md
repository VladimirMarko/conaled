# Natural-run comparisons and builder operations: implementation plan

Recorded 4 November 2026, before source edits for this continuation. This is
implementation planning within the existing Chapter 2 loop, not a new review
loop, acceptance claim or replacement of C02-001–112.

## Starting state and ownership

- Worktree/branch: `conaled-ch02-natural-runs` /
  `work/fdsa-ch02-natural-runs`.
- This resource-phase starting HEAD is
  `ff9749d1ccbcb0949486f67d6273e28c262280e0`, clean, with its two natural-run
  value modules already passing focused compilation and author statement
  review. Their definitions, statements and connected cases remain unchanged.
- The accepted whole-chapter integration base remains
  `07e480f6ec9958d4975bb90151005b84f2907614`; root retains the enclosing
  implementation/review baseline and all acceptance authority.
- New owned source paths for this bounded slice:
  `Applications/Resources/NaturalRunComparisons.lean`,
  `Examples/NaturalRunComparisons.lean`,
  `Applications/Resources/ListBuildCosts.lean`, and
  `Examples/ListBuildCosts.lean`.
- This new handoff and natural-run cost provenance records are also owned.
  No existing shared file, public import root, ticket, coverage table,
  dependency, other worktree or foundation candidate is to be edited.
- No build is authorized in this source worktree. Root owns the only private
  focused dependency tree, currently at top-down, and will run later focused
  checks on detached immutable candidate checkouts there and return exact
  diagnostics. No cache copy or build is to be made in this source worktree.

## Source and current requirements

The complete current `reviews/chapter02-requirements.md`, C02-058–088 and
C02-108–112 in the current inventory, the explicit frozen-scope reconciliation,
`research/natural-runs-proof-plan.md`, the full difference-list preflight/spec
and its provenance erratum, the builder candidate, and the mergesort resource
readiness record were read. AGENTS, architecture/domain/glossary, relevant
ADRs, implementation/review and example-driven instructions, and README's
actual acceptance rules were re-read. The Nix-only exception remains in force;
the compiler/dependency pins and other gates do not change.

The actual pinned book text was inspected again, printed pp.21–24:

- p.21 gives the actual mutual scanner, strict descending initial branch and
  singleton ascending seed;
- p.22 contrasts repeated ordinary append with prepend/reverse, and describes
  closure composition and subsequent materialization;
- p.23 explicitly starts a comparison-only observation, with separate `Cruns`,
  `Casc`, `Cdesc` and `Cnmsort` recurrences.

The PDF SHA-256 remains
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The frozen chapter requirement digest remains
`f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`.
All current input digests and the unchanged value-source identities are
recorded in `provenance/chapter02-natural-run-costs-plan-20261104/identity.json`.

The AFP natural-merge theory is the member of the dated Efficient-Mergesort
archive, SHA-256
`2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51`.
It is not the separately pinned Isabelle Sorting theory. The retained
XD01-DOC-001 erratum continues to qualify the older preflight attribution.
This slice derives its proofs from the stated source recurrences and existing
Lean interfaces; no upstream proof text is copied into source.

## Dependency boundary and chosen coherent slice

The comparison scanner needs only the checked value module and the accepted
`Resources.Measured` / `CallCount` interfaces. The ordinary-list construction
comparison needs accepted `Workload.run`, `ListReversal.appendRun_exact`,
`ListReversal.accumulator_exact` and the existing growth interface. These are
present in this starting branch.

The closure-accounting part has a real separate dependency:
`Applications/Resources/DifferenceListCosts.lean` from shared XD01 candidate
`62809ced86c561c7a6cce8b71e727177a3f17fb8`; its core digest is
`567683626b9a46d07c465ceb44faaafc941e2dc1c83491b093599ca7f8c698a5`.
The exact source and frozen requirements were inspected through that Git
object. It is absent from this worktree and remains uncompiled/unaccepted in
the current records. The source plan expressly requires validation/integration
before using it as a dependency. This worker has reported that boundary to
root and will not duplicate or silently import the draft.

Measured ordinary BottomUp integration is also needed for the complete
natural-sort equation, zero merge comparisons, logarithmic bounds, and final
dispatch. Root owns that reconciliation. No substitute merge implementation
or assumed cost equality will be introduced here.

**The present bounded implementation slice is therefore** the actual natural
comparison scanner and exact source-counter correspondence, plus C02-109's
actual ordinary append/prepend-reverse constructions and their separate
observations. This advances C02-108's scanner component and C02-109 while
keeping the remaining parts of C02-108–112 mandatory and explicitly pending.

## 1. Actual comparison execution and the source equations

Namespace `Resources.NaturalRunComparisons` will contain the three source
comparison specifications, together with mutually recursive measured workers
`runsRunBy`, `ascRunBy`, `descRunBy`. The measured workers return their actual
recursive child's value, use the same Batteries.DList operations and same
restart boundary as the checked value functions, and charge one only at an
actual adjacent comparison. Empty/singleton scanner inputs and empty worker
tails cost zero. Builder application, cons, key evaluation, control entry and
all machine work are outside this comparison tariff.

The independent source-counter recurrences retain the source's omitted worker
accumulators. Prove the measured value erasure and cost-to-counter laws
separately, for every comparator and every worker accumulator. The common
termination measures stay input length and worker-tail length plus one.

Then prove, simultaneously:

```text
Casc lt a ys  = ys.length
Cdesc lt a ys = ys.length
Cruns lt xs  = xs.length - 1
```

The final subtraction is natural subtraction. Retain C02-083–085's weaker
bounds as named corollaries. Transfer the arbitrary raw-function source bridge
through `dListOfLaw` without adding an application-cost hypothesis to a
comparison theorem. Combine erasure/count with the already checked one-run
value laws to obtain the exact measured result on nonempty sorted and strictly
descending inputs. These results do not yet prove the merge portion of C02-108.

Connected expected cases: empty payload type and singleton cost 0; ascending
ties and strict descent at length four cost 3; `[1,3,2,4]` returns two runs and
costs 3; mixed tied records keep the independently expected runs and cost 3;
the arbitrary raw `[1,3] ++ suffix` builder starting at 5 on `[4,6]` costs 2;
an unsorted lawful prefix and a weak descending tied accumulator still cost 0
on an empty remaining tail. These cases consume the public execution,
erasure and count laws, including the previous independent value examples.

## 2. Ordinary list construction and the exact cost boundary

Namespace `Resources.ListBuildCosts` will reuse the actual measured append
implementation, whose cost is `prefix.length + 1`, including its terminal
call. `appendSubRun items prefix` uses existing `Resources.run` to execute
these append operations in input order. Its observation excludes loop entry,
wrapper entry and the already supplied seed's construction.

For `n = items.length` and `p = prefix.length`, target:

```text
value(appendSubRun items prefix) = prefix ++ items
2 * cost(appendSubRun items prefix) = 2*n*p + n*(n+1)
cost(appendSubRun items prefix) = n*p + n*(n+1)/2
```

Prove the doubled equality from the actual updated prefix in each append;
derive natural division afterward. In particular the empty seed's append-only
subcost is the required triangular count `n*(n+1)/2`.

An explicit `appendLoopRun` will charge one recursive loop entry, including
the terminal entry, in addition to the actual append call. Prove its value
agreement and `cost = appendSubRun.cost + n + 1`. A named `appendBuildRun`
wrapper adds one more fixed entry and supplies the initially empty seed:

```text
cost(appendBuildRun items) = n*(n+1)/2 + n + 2
2 * cost(appendBuildRun items) = n*n + 3*n + 4
```

For the alternative, use the already verified accumulator-reversal execution
as the prepend loop, bind its actual returned reversed list into a second
accumulator reversal, and charge the same one-unit wrapper. This
`consReverseBuildRun` returns `items` with cost `2*n+3`. Both observations
count declared source-model operations; neither is a statement about the
standard library's compiled reverse or machine time.

Retain explicit uniform bounds witnessing the distinction: for `n >= 1`,
`n*n <= 2*appendBuildCost` and `appendBuildCost <= 4*n*n`, while the
cons/reverse count is exactly `2*n+3` and at most `5*n`. Package relevant
upper/lower eventual bounds through existing growth interfaces if useful;
the exact source-execution equations remain the primary evidence.

Independent expected cases: empty input at payload type Empty (append-only 0,
full append 2, full cons/reverse 3); singleton (append-only 1, full append 4,
full cons/reverse 5); duplicate `[3,1,3]` (append-only 6, full append 11,
full cons/reverse 9); nonempty seed `[9]` followed by `[3,1]` (value
`[9,3,1]`, append subcost 5, excluding prior seed creation). The same ordered
result has different actual observations, so no cost transfer follows from
value equality alone.

## 3. Pending closure integration: exact C02-110/111 contracts

After root validates and integrates XD01, reuse its ordinary callback alias
`Builder`, separate `Rep` and `AppCost`, creation operations, `pushRun`,
seed-general `buildFrom` and actual DList bridges. No new builder datatype,
interpreter, executor or measured Monoid instance is needed.

For a source ascending run written `first :: middle ++ [last]`, the actual
singleton seed is extended by exactly `middle.length` compositional pushes,
then applied to `[last]`. The source correspondence must be proved through
the actual ascending branches, not inferred from a final extensional DList
equality. With `m = middle.length`, creation including the seed and later
application each have count `1 + 2*m`. For run length `r = m+2`, the
subtraction-safe equality is `cost + 3 = 2*r`; only then derive `2*r-3`.

Keep creation, one application, and repeated independent application distinct.
Reuse XD01's empty-prefix padding, charged-identity and shared-self-composition
counterexamples. The linear representation weight is unfolded invocation
occurrence weight, not the number of distinct shared closures. An arbitrary
lawful raw function retains its semantic worker laws; a resource bound for
an arbitrary measured seed additionally needs `AppCost f k`, and includes k.
Batteries' fused push receives a value bridge only, not an invented exact cost.

## 4. Pending full scanner operation model: concrete proof route for C02-112

The following is a proposed fixed tariff and proof target, not a checked
claim yet. It reuses XD01 operations at the actual source branches:

- one unit for each scanner/worker entry and each tested adjacent pair;
- XD01's actual singleton/composition creation and callback application costs;
- one unit for each direct descending cons, each final singleton suffix cell,
  and each emitted outer-run cons, outside the builder callbacks;
- one unit for the eventual empty/single-run merger dispatch.

The singleton callback's own unit entry accounts for its constant local cons;
do not double-charge it as an additional direct descending/suffix operation.
Supplied accumulators/callbacks are already constructed values at worker entry.
This is a declared abstract operation model, not compiler allocation or timing.

Let W denote its actual mutually recursive measured execution, and let k be
the supplied ascending callback's uniform application contract. The planned
branch accounting, directly derived from the listed operations, is:

| Branch | Work equation |
| --- | --- |
| runs empty / singleton | 1 / 3 |
| runs on two-or-more elements | 3 plus the selected worker, including singleton callback or descending seed creation |
| asc empty tail | k + 3 |
| asc continuation | 4 plus the worker with application contract k+2 |
| asc restart | k + 4 plus W of the actual restarted tail |
| desc empty tail | 3 |
| desc continuation | 3 plus the selected worker |
| desc restart | 4 plus W of the actual restarted tail |

These recurrences support the simultaneous proposed bounds
`W_runs xs <= 6*xs.length+1`,
`W_asc a f ys <= k+6*ys.length+5`, and
`W_desc a acc ys <= 6*ys.length+5`.
For ascending continuation the added 4 units plus the 2-unit growth in
future application weight explain the coefficient 6. Restart consumes the
old builder once and uses the initial scanner bound for the remainder.
No unproved disjoint-run or memoization assumption is needed.

After the actual common merger's base dispatch is connected, the single-run
natural sorter gets a proposed bound `6*n+2` in this operation model, while
retaining exactly `n-1` comparisons under the separate comparison model.
Expected operational boundary cases for that later proof include empty 1,
singleton 3, a sorted ascending run of length r>=2 with scanner work `6*r-5`,
and a strict descending run of length r>=2 with scanner work `3*r`; dispatch
adds one. These are transparent hand-derived targets, not accepted theorems.

## Validation and continuation

The plan precedes all source edits in this slice. No new compiler result,
cost coverage completion, independent review or acceptance is claimed here.
Use meaningful connected cases and inspect the actual elaborated hypotheses
when root runs the qualified immutable candidate check. Preserve every real failed
and successful terminal attempt, source identity and closed log. Keep the
existing value module hashes unchanged. Notify root before draft commits and
checkpoint holds. Full guarded candidate validation, exhaustive axiom audit,
independent Standards/Spec review and immediate verification remain root-owned
gates on the reconciled candidate.

## Checkpoint 0084 hold

Root approved the bounded slice and explicit XD01/BottomUp dependency boundary.
Before any of the four new source files was authored, root requested a safe
checkpoint hold. This plan and its input-identity record are the only new
artifacts in the continuation. The source worktree remains clean at
`ff9749d1ccbcb0949486f67d6273e28c262280e0`; no new resource code, ref mutation,
compiler invocation or dependency change has occurred. Source/ref/control
writes are held after this note until root releases the checkpoint hold.

## Checkpoint 0084 release and initial source draft

Root released the hold after checkpoint 0084 was saved and exposed. The four
planned new source files are now authored. Their first compiler check is
pending in root's detached qualified development checkout; no build or cache
operation was run in this author worktree. The checked value modules still
match the two hashes recorded above. All full-scope operational and integration
obligations in sections 3–4 remain pending.

The draft implements the source `Cruns`/`Casc`/`Cdesc` specifications separately
from the actual measured scanner. The scanner executes one selected recursive
branch, with actual DList values and the actual returned restart value.
Its joint refinement proof computes both observations from these branches;
separate public value and counter projections do not infer cost from value
equality. Exact `length - 1` / remaining-tail-length counts, the original
weaker bounds, raw lawful-builder transfer, and measured sorted/strictly
descending one-run laws are included.

The ordinary-list draft uses `Workload.run` for append-only observation and
the existing measured append's actual next prefix. An explicit full append
loop adds each loop entry, including its terminal call; its wrapper adds
one. The cons/reverse alternative binds the actual first reverse result
into the second. Seed-general triangular subcost, fixed overhead, full
quadratic/linear exact counts and uniform bounds are included. The chosen
tariff is an explicit source-operation model, not compiled runtime.

### Author statement and connected-case review before compilation

- Quantifiers preserve arbitrary payload universes, arbitrary Boolean
  comparators and arbitrary supplied worker accumulators. Ordering appears
  only in the inherited one-run value hypotheses. No payload equality,
  order, default value or inhabitedness premise is introduced.
- Counts test `lt next current`, follow strict descent, continue ascent on
  ties, and retain each restart boundary. Empty/singleton scanners and empty
  worker tails have zero comparison cost. The raw D law is a value premise;
  no builder application-cost claim is inferred from it.
- Exact comparison cases consume public measured laws and the prior
  independently expected value cases: restart, ties, strict descent, mixed
  records, arbitrary seeded raw builder, unsorted lawful prefix and unstable
  weak descending tied state. The last two retain their counterexamples.
- The append-only subcost excludes already supplied seed construction,
  loop entries and wrapper. Full counts explicitly restore their declared
  entries. Empty `Empty` payload and singleton cases make fixed costs visible.
  The duplicate three-element case gives subcost 6, full append 11 and
  cons/reverse 9. A nonpalindromic four-element case separately checks order
  restoration, because `[3,1,3]` alone would not distinguish one reversal.
  The nonempty seed `[9]` with `[3,1]` gives append-only cost 5 and loop cost 8.
- The source proof terms and intended statements have been reviewed without
  a Lean invocation. Elaboration, termination proofs, tactic closure and
  elaborated-type inspection remain pending. This is not a passing focused
  build, full audit, independent review, coverage completion or acceptance.

Root will receive the clean immutable draft commit and its exact four-file
manifest. Subsequent compile diagnostics will be preserved and corrected
without changing independent expected values or weakening public statements.

Initial immutable draft: `3d5238737299cd365f36e39e5e8a61d34138cba5`, direct
parent `ff9749d1ccbcb0949486f67d6273e28c262280e0`, with a clean author
worktree. Exactly the four planned new Lean files were committed (693 added
lines); the staged whitespace check exited 0. The source manifest and
unchanged value hashes are saved at
`provenance/chapter02-natural-run-costs-draft-20261104/identity.json`.
Root has been notified of this immutable candidate and the four focused build
targets. The manifest explicitly records an empty build-attempt list and
uncompiled status; a static forbidden-keyword scan is not an axiom audit.

## Closed central focused attempt 1 and bounded correction

After checkpoint 0085, root released the author for corrections from the
completed six-target check of central immutable candidate
`8ec1d9cb93e4c38168dc357e8b6f254f8fe83668`. The four cost-source/example
files in that candidate exactly match their original author commit
`3d5238737299cd365f36e39e5e8a61d34138cba5`, as confirmed by Git blob IDs.
This is evidence about that actual central check, not a check performed in
the author worktree.

The recorded command used the unchanged qualified native launcher, one Lean
thread and the QuickSort cost pair plus both natural-run/list-build module
pairs. It started at 05:12:15 UTC and terminated at 05:15:23 UTC on
4 November 2026, actual exit **1**, elapsed 188.162 seconds. The final central
HEAD matched the candidate and the checkout remained clean. No candidate
verification record was present; no successful focused gate or audit is
inferred. Root retains the complete closed records in
`provenance/chapter02-measured-sorting-focused-20261104-attempt1/`.

The full log was read completely and verified against its recorded SHA-256
`fd65b65eab6a5cc03a6252895665864a16ac7c3724b9539b938f8800a5c8a44e`.
The native output is an exact contiguous part of that full log, SHA-256
`5e301d5ba4ff0326e81ea2082eaaf4dea6c7b628d1e76a09fe02607a079d2482`;
its native terminal result separately records exit 1, no timeout and no
recorder error. Historical incomplete attempts are not being polled or reused.

| Owned diagnostic | Bounded source correction | Remaining validation |
| --- | --- | --- |
| `ListBuildCosts`: reserved token `prefix` in binders/patterns, followed by parser and unavailable-declaration cascades | Rename only the bound identifier and its occurrences to `acc`; all comments, other expressions, contracts and expected counts are unchanged | Recompile to expose any independent errors previously hidden by parsing |
| `NaturalRunComparisons`: unused `h` simp argument at lines 163, 166, 179, 182, 195, 199 | Remove precisely those six redundant list arguments; the case splits, recursive proof uses and all theorem statements remain unchanged | Recompile the corrected core and its retained cases |

The central log also records the separately owned QuickSort example
diagnostic; no QuickSort file was edited here. Linter settings, proof
restrictions, environment, public roots and validation gates are unchanged.

Correction commit: `dd01c1cbdbf181039f62873996935f2b868412a1`, direct parent
`3d5238737299cd365f36e39e5e8a61d34138cba5`. Exactly two files changed,
with 45 insertions/45 deletions. A source comparison confirmed the precise
identifier-only and six-argument transformations. Both example files and
both checked natural-run value files are byte-identical to the parent.
Unstaged and staged whitespace checks passed; the author checkout is clean.

- `Applications/Resources/ListBuildCosts.lean` SHA-256:
  `9b93f522703ec9e3254bac47f8836b4edf70db1e0a747c785fa4464826b128cc`.
- `Applications/Resources/NaturalRunComparisons.lean` SHA-256:
  `920e1832416afcdc47a0c2301c2e27c7cd5f0c614a209c8dea21fc2561d809b0`.

The complete correction manifest is
`provenance/chapter02-natural-run-costs-correction1-20261104/identity.json`.
No compiler or cache action was run by this author. Both fixes are implemented
but await matching compilation; all full acceptance and remaining operational
obligations remain pending. Source/ref/control writes are held after this
handoff until root's next release.

## Closed central attempt2 and root's bounded proof correction

Central841413dc6b1e332ba07063fb62e66dea0802ab37 closed with actual exit1,
unchanged clean HEAD. NaturalRunComparisons and its example module PASSED,
as did the separately owned QuickSort cost library/examples. ListBuildCosts
reported only line109 No goals to be solved: the preceding rw already closed
appendBuildRun_cost. Its example was not built. Complete recorder/native logs
are preserved in chapter02-measured-sorting-focused-20261104-attempt2/.

With the author held, root deleted only that redundant omega in the author
tree, committing27d7f9f70dd76a35007dd62cde2b78cf575c4b3f afterdd01c1cb. All
definitions/statements/expected values and other files remain unchanged; source
SHA256 is6c2450b98fcb2677fddeea1116519e968223bc0872353d9e34979fc38607547f.
The actual emitted diagnostic was inspected while the central run was still
active; only the separate idle author tree changed. Matching central recheck
is pending. Its exact patch/start/result are preserved in correction2 provenance.

## Closed central attempt 3 and minimal example-proof correction

Root released only the example repairs after central candidate
`e582eb3fe15492ca8182e530ebd24a15c3d0e4ff` closed its six-target focused
command. Its four owned resource/example inputs exactly match author parent
`27d7f9f70dd76a35007dd62cde2b78cf575c4b3f`. The actual result is exit **1**,
from 05:31:18 to 05:32:37 UTC on 4 November 2026, elapsed 78.497 seconds,
unchanged final HEAD and clean status. The same qualified native launcher and
one Lean thread were used; no candidate verification record was present.

The ListBuildCosts core explicitly built successfully. NaturalRunComparisons
and its examples had built successfully in closed attempt 2 and remain
unchanged; they were included again in attempt 3 without failure. Attempt 3's
only failed target is `Examples.ListBuildCosts`. These module-level successes
do not turn either failed six-target command into a successful gate.

The complete attempt 2 and 3 logs and native terminal records were inspected.
Both native records confirm exit 1, no timeout and no recorder error. Each
native output is an exact contiguous part of its closed full log, whose
digest matches the corresponding recorder result:

| Attempt | Full log SHA-256 | Native output SHA-256 |
| --- | --- | --- |
| 2 | `a8367b26cf50c6f2ad762e19d54d4455338f60b9615a09bb42c0688d17850f68` | `459f752379abcee00041489ee57b1c88436cb52e9a94cffe4c907acae02ac708` |
| 3 | `089d314f5856c9a26420442d592a8564ff9c76ec9f3ed19363f7b00b08a132ac` | `f9c103e6e12486b9543af06b748c13f54b39aec54a2d4200c1b979a500f89b20` |

Both retained diagnostics concern proof elaboration in the examples:

- `nonempty_seed_full_loop` left the concrete goal
  `([9,3,1],5).2 + [3,1].length + 1 = ([9,3,1],8).2` after rewriting.
  Its proof now uses `simp` through the same `appendLoopRun_cost` and
  `nonempty_seed` laws, including their remaining projections and arithmetic.
- `polymorphic_order` could not use a bare application of the general exact
  family as the numeral-cost equation. Its proof now uses `constructor`
  followed by `simpa using` the same two public exact results. The arbitrary
  payload universe and expected append cost 11 / cons-reverse cost 9 are
  unchanged. This also makes the second specialization's numeral reduction
  explicit instead of relying on the same definitional reduction.

Correction commit: `8f4bbe8dec5e8653acda1b309d9da1c42385c564`, direct parent
`27d7f9f70dd76a35007dd62cde2b78cf575c4b3f`. Only
`Examples/ListBuildCosts.lean` changed, with 5 insertions and 3 deletions;
new SHA-256 `eba2961e501f545323e5403e7874ce3ddb256bad8f4046398acc55ca6ec230a1`.
Both resource cores, the natural-comparison examples and both checked value
files are byte-identical to the parent. All statements, expected values,
resource models, linter settings and proof restrictions remain unchanged.

The minimal proof-text changes and unstaged/staged whitespace checks were
verified, and the author checkout is clean. Exact source identities and
terminal-evidence digests are saved in
`provenance/chapter02-natural-run-costs-correction3-20261104/identity.json`.
No compiler, cache or other-worktree operation was performed by this author.
The corrected example still needs a matching qualified build; no pass is
guessed. Full acceptance, independent reviews and the remaining XD01/BottomUp
operational obligations remain pending. All source/ref/control writes are
held after this handoff until root's next explicit release.

## Complete elaborated author readback — 4 November 2026

All91 assigned public declarations (43+13 natural comparison,26+9 list builder)
passed explicit/universe-visible type inspection at clean1ffb61fc. The author
read every actual type and exact source against original contracts/cases with
zero concrete findings. Full identity/scope/assumption/counter/example findings
are preserved in
provenance/chapter02-measured-sorting-types-20261104/natural-builders-author-readback.md.
This is author statement assessment, not either independent final axis or
full acceptance. Every failed aggregate retains its actual exit1.

## Natural sorter and comparison composition: pre-code plan — 4 November 2026

Root released this continuation after saved checkpoint0086. The source-only
natural author tree was clean at 8f4bbe8dec5e8653acda1b309d9da1c42385c564.
Its authorized development-only fast-forward to exact central
5d7a479549f5acd64a9e5adb418ab48780c238ef completed with a clean result after
checking ancestry and identical bytes for all six checked natural-run,
comparison and list-builder files. The start/result records are under
provenance/chapter02-natural-sorting-plan-20261104/. Original history remains
reachable. Accepted Chapter1 stays at R=07e480f; first foundation f17cc6b stays
pending and unchanged. This does not accept any incorporated shared draft.

This iteration owns exactly four new source paths:
Applications/Sorting/Natural.lean, Examples/NaturalSorting.lean,
Applications/Resources/NaturalSorting.lean, Examples/NaturalSortingCosts.lean.
It also owns this existing handoff and its assigned provenance. No public
root, reconstruction map, tracker, shared source, cache, dependency or other
worktree is to change. No author compilation is authorized. The root-managed
BottomUp comparison correction is being checked separately; no success is
assumed when preparing this dependent draft.

Source/standards read before code: current full Chapter2 requirements and
112-obligation inventory, frozen-scope clarification, the natural-run proof
plan and relevant merger reuse plan, actual pinned book pp.21–25, AGENTS,
architecture/domain/glossary and ADR0001/0010, implement/review-loop,
example-driven-development/worked-example, and README acceptance rules.
The exact current scanner/merger/value/comparison/Growth APIs were read.
All source and dependency identities are recorded beside this plan.

### Intended pure statements and assumptions

Define sortNaturalBy lt cmp xs as the actual mergeAllBy cmp (runsBy lt xs).
Keep the scanner and merge operations independently supplied for law-free
value results. Prove empty/singleton equations, full List.Perm preservation,
multiset equality, length, and support. Derive sortedness using the scanner's
sorted-run theorem and the same merger's input-local compatibility theorem,
with only a preorder on observed keys and separate input-local scanner/merge
compatibility assumptions. Do not assume sortedness of the requested result.

The source keyed interface supplies strict key< to scanning and left-tie
key≤ to merge. Its correctness uses a linear key order and retains arbitrary
payloads, without payload equality, order, default or inhabitance instances.
A one-run bridge and ascending/descending chain specializations preserve
weaker generic value laws. Sorted input is a fixed point; strict descent is
reversed. Nonempty one-run claims keep that premise; empty input remains its
own equation. No new generic stability claim is part of this slice.

### Intended measured statements and numerical boundaries

Define Resources.NaturalSorting.run by binding the actual runsRunBy result
to BottomUpSorting.allRun. Prove its value erasure, occurrence/length laws,
keyed correctness, and exact independent source equation
C(xs)=Cruns(xs)+Cmerge_all(runsBy lt xs). The scanner's already proved exact
Cruns=len-1 then yields an unconditional count lower bound len-1≤C(xs).
No builder, function-entry or machine-runtime costs enter this observation.

Write n=xs.length and r=(runsBy lt xs).length. Derive, from the actual bound
for allRun and the checked flattened-length/run-count invariants:
C(xs)≤(n-1)+n*Nat.clog 2 r≤(n-1)+n*Nat.clog 2 n.
Retain the book's explicit weaker n+n*Nat.clog 2 n and length-parameterized
form. Reuse BottomUp's integer-ceiling correspondence for all n, including
zero/one; cast truncated natural n-1 as a whole in the sharper statement.
The printed integer-ceiling bound does not introduce a hidden positivity
premise or confuse the two ceiling conventions.

For a nonempty sorted input, derive actual runs=[xs], zero merging comparisons
and run=(xs,n-1). Treat [] by its own exact zero-cost equation. Strict descent
similarly yields (xs.reverse,n-1). General one-run and adjacent-chain results
can retain arbitrary comparators. For n≥2 the lower bound implies n≤2*C(xs).
Obtain O(n log₂ n) for arbitrary length-indexed input families using Growth
only after a proved C≤2*n*clog bound. For sorted length-indexed families prove
exact count n-1 and linear upper/lower eventual bounds, hence Θ(n) in this
comparison model. No numerical bound is inferred from a value equation.

### Independently chosen connected cases

- Empty input at Empty and singleton with arbitrary payload: zero comparisons.
- Sorted [0,1,2]: one run, zero merge comparisons, total 2; descending [2,1,0]
  also costs 2 but reverses its run.
- [3,1,2]: scanner returns [[1,3],[2]], scan cost 2 and actual merge cost 2,
  sorted result [1,2,3], total 4. This distinguishes detection plus merging.
- [1,3,2,4]: retained two-run fixture, scan 3, merge 3, total 6.
- [1,3,2,4,0]: three unequal runs [[1,3],[2,4],[0]], first merge pass costs 3,
  next merge costs 1, scan costs 4, total 8; adaptive budget 4+5*2=14.
- Tied tagged input [(3,A),(2,B),(2,C),(1,D)]: sorted output
  [(1,D),(2,B),(2,C),(3,A)], total 6; tie order is an explicit concrete case,
  not an unproved generic stability theorem.
- Existing weak-descent tie case remains two runs, and its complete sort must
  not be presented as one whole-run reversal.
- Generic bad comparators still preserve occurrences/count bounds without an
  unsupported sortedness claim; an input-local compatible case exercises the
  weaker correctness interface.
- Shared allRun empty/sole-run and empty-inner-run boundaries remain available;
  the source scanner itself never emits empty inner runs.
- Arbitrary-payload correctness and constant-key repeated families exercise
  absence of payload instances; sorted range/replicate families connect the
  exact best case and eventual linear comparison statements.

Before committing, inspect every declared statement and its actual proof
connection against these intentions; record exact source identities and any
static issues. The four-file candidate remains explicitly uncompiled until
root returns a secured terminal result and later elaborated-type inspection.
C02-110–112 XD01 construction/invocation/full-scanner/dispatch obligations stay
mandatory next work. No focused pass, statement inspection or local draft
commit constitutes full audit, independent final review or acceptance.

Concrete example reuse: the cost examples will import the existing
Examples.BottomUpCosts.all_two_runs specialization rather than duplicate its
measured two-run composition proof. This source is already present at exact
5d7a479 and remains subject to root's pending focused validation. The existing
checked NaturalRunComparisons/NaturalRuns fixtures supply the scanner cases.
These explicit example dependencies and their hashes were added to the plan
identity before writing Examples/NaturalSortingCosts.lean.

## Natural-sort four-file authored draft — 4 November 2026

The pure and measured scanner-to-ordinary-merger composition is now authored
in the four assigned new files, against exact development base5d7a479.
All105 public declarations (16+22+37+30;99 theorems) received complete static
source/derivation statement review with no concrete source-contract findings.
The complete per-claim manifest and connected expected-case assessment are
under provenance/chapter02-natural-sorting-author-draft-20261104/.
No compiler/type-inspection/audit pass is claimed for this draft. Root now
reports the identical BottomUp resource core passed at6d91b822; its example
correction changes only proof elaboration and leaves the reused all_two_runs
interface unchanged. The root integration must retain that corrected example
source. Author dependency files remain untouched at the exact5d base.

The draft preserves generic occurrence/order contracts, actual measured bind,
exact scan-plus-merge count, unconditional natural n-1 lower bound, adaptive
and source/general bounds, integer ceilings including zero, sorted/strict
one-run exact behavior and Growth-derived comparison asymptotics. Cases
retain total2 for sorted[0,1,2], total4 for[3,1,2], total6 for the retained
restart/mixed-record cases, total8 for three unequal runs, arbitrary payload
correctness and nonvacuous all-length families. No stability or operational
runtime theorem is inferred. C02-110–112 remain pending and mandatory.

The next step is the authorized four-file local uncompiled draft commit,
followed by a source/ref/control HOLD for root's exact candidate diagnostics.
No author builds, cache changes, public-root edits, coverage or acceptance
updates are authorized. Complete commit/source identity follows below.

### Committed identity and author HOLD

Candidate `9c5858d0feb56b42701ab1f84e5d9265b953cfea`, sole parent `5d7a479549f5acd64a9e5adb418ab48780c238ef`,
branch `work/fdsa-ch02-natural-runs`, clean index/working tree.
Conventional commit: `feat(sorting): compose natural runs and measured merging (#174)`.
Only the four owned new files were added (748 lines); exact source hashes,
105-declaration inventory, original-history and unchanged-six-source checks
are in `provenance/chapter02-natural-sorting-author-draft-20261104/identity.json`.
The staged whitespace check exited0; no source/compiler/build/audit success is
claimed beyond the expressly static checks. Root must retain the corrected
BottomUp example dependency at6d91b822 during integration. All author source,
ref and control writes are now HELD pending explicit root diagnostics/release.


## Natural-sort compiler correction 1 — 4 November 2026

Root released only bounded repairs after central candidate
`e2db54211dfe3b2efd76904f1797a9460567ebbc` closed the natural/XD01 focused
attempt with actual exit 1 (27.319240105000063 seconds), unchanged clean HEAD.
The complete full.log and result.json were read; log SHA-256 is
`057996ba9c497d0821e21cb47efad8b7eda3a2a8db26b7f112259adf77e0983f`.
The pure natural-sort core built, while the combined target set failed.
No dependent-module success or full audit is inferred.

Stable local findings C02-NAT-ELAB-001–004 record, respectively: exposing the
keyed goal before strict-descending simplification; proving arbitrary
constant-key Pairwise through the existing all-elements theorem; correcting
implicit element binders in Pairwise.imp; and explicitly typing the inverse
Big-O function index as Nat. The downstream uses-sorry diagnostic is retained
as compiler recovery from the ill-typed declaration, not a source admission.
XD01 diagnostics remain root-owned. No operational source is authored here.

Only the resource core and value examples changed. Complete corrected-file
readback covers their 37+22 declarations; all 105 original source declaration
headers were compared, with 104 identical and one explicit intended Nat-index
annotation. Three remaining changes are proof-only. All expected values,
hypotheses, algorithms, comparator/measurement boundaries and source options
are retained. Detailed identities, complete diff, findings, per-declaration
comparison and actual commit/whitespace outcomes are preserved under
`provenance/chapter02-natural-sorting-correction1-20261104/`.

Correction candidate `ce28f2f3248b334b17ec339a1cae0e2099cd887a` has sole parent
`9c5858d0feb56b42701ab1f84e5d9265b953cfea` and a clean index/worktree.
Commit: `fix(sorting): repair natural-sort proof elaboration (#174)`.
Resource core SHA-256:
`bfca759cd0f1014d39824bdcb124a3a0b33d1459be2cc4635739965382a50e7a`.
Value examples SHA-256:
`69cc14a5f40421076a3af3f8066c0bf2b20678d11f4cbc5e3eefab8454fdbf57`.
The pure core and cost examples retain their previous exact hashes. Both
unstaged and staged whitespace checks exited 0. No author compiler or cache
operation ran; these repairs remain uncompiled pending root's actual next
terminal result. All source/ref/control writes are HELD after this receipt.
Full type assessment, independent axes, audit and immediate verification are
still required; no acceptance state changes.

## Root compiler continuation, 4 November 2026

At clean central7b4f9bad, focused attempt2 exited1 with only Examples.NaturalSortingCosts failing; value core/examples and comparison core passed. Root changed only this held author example file in successor 6e332c5fe00bb1f4a62e8a98ecc2d877c8058212. The30 public headers and all expected cases are identical. C02-NAT-ELAB-005 covers the descending comparator alias;006 narrows ceiling-bound normalization so the public theorem remains consumed;007 exposes the constant-key comparator;008 supplies arbitrary Pairwise and singleton-length witnesses;009 aligns both range relation binders. Exact failed/native records and correction diff are preserved in provenance/chapter02-natural-sorting-correction2-20261104/. Compilation, complete elaborated-type assessment and all final gates remain pending.

C02-NAT-ELAB-010: focused attempt3 at2024a392 closed exit1 with only the range exact-count example reporting the same comparator-alias mismatch. The minimal successor 5679b4ff6cbc4895afab6aa078de00ef8e9743ba exposes the intended definitionally equal predicate before applying the unchanged public theorem. Every example statement and expected value remains unchanged. Exact diff/native failure and central integration identity are in provenance/chapter02-natural-sorting-correction3-20261104/. No acceptance is inferred.

C02-NAT-ELAB-010 remains unresolved after actual focused attempt4: the explicit comparator now matches, but restricted simplification still retained id in the theorem side. Successor 33a7c616bbb5d4a774ec614838d7670c61083ec4 adds only id_eq to that restricted simp list. Prior attempt4 exit1 and its complete/native records are retained; no success is inferred before the next terminal result.


## Natural composition — secured focused pass and complete author type readback

Focused attempt5 passed at clean immutable central `0ec9954479b081664bd4504c90fb66fba5fd22c8`
with actual exit 0 in 56.93164911299937 seconds; complete log SHA-256
`93dd85d55c2705109a0fd804e942737a29fd69342088d8e9286b600cadbe7d30`.
The separate 105-declaration type inspection passed at that same clean candidate
with exit 0 in 157.81176944300023 seconds; complete 79,992-byte log SHA-256
`136335c62dbd1bd67c9f0ce77c69056b47f4e37b5b42e67ea91b233c1a71e50a`.
Both sets of native terminal records are secured. Prior failed attempts and
correction findings remain preserved, including the intermediate failure of
C02-NAT-ELAB-010 before id_eq was added.

The author read all four current source files, all root correction2/3/4 diffs
and all 105 complete explicit/universe-visible type blocks (16+22+37+30),
comparing every claim with its frozen intent and connected cases. Outcome:
zero new concrete statement findings. This is author readback, not either
independent final review axis. The full per-claim assessment is
`provenance/chapter02-natural-sorting-author-readback-20261104/report.md`,
SHA-256 `b96cea9ece3e3998eb53e358998ab61f25d94beae50735fd9cbc10853692c32a`.

Author HEAD remains clean `33a7c616bbb5d4a774ec614838d7670c61083ec4`. All four reviewed source
files match checked central0ec995 exactly. Of the 22-file project import
closure, only Examples/BottomUpCosts differs: central retains its previously
checked proof-only corrections; all_two_runs and every value/resource core
match. Lean/Lake dependency pins and project config match. The report explicitly
does not claim the older author dependency tree was compiled. Root must retain
the corrected dependency bytes during the next authorized alignment.

No source/ref/index/build/cache changes occurred in this readback. The only
writes are its dedicated report and this handoff. C02-110–112 operational
implementation remains mandatory and awaits source release despite approval
of its plan. Full candidate audit, both independent axes and immediate
verification remain required. All further writes are now HELD.


## C02-110–112 operational source draft — scoped commit and hold

Root released the approved operational plan after the complete natural-composition
type readback and checkpoint 0089. The source-only author branch was verified clean
at `33a7c616bbb5d4a774ec614838d7670c61083ec4` and fast-forwarded to the exact fixed
base `0ec9954479b081664bd4504c90fb66fba5fd22c8`; all earlier checked own sources and
pins were preserved, with the checked BottomUp examples and current XD01 now
aligned. Actual alignment records are retained in
`provenance/chapter02-natural-operations-implementation-20261104/`.

The complete uncompiled operational draft is now committed as
`e1f3b5c43ba3b0f4aca5964f2b4568e06b47700c` with parent `0ec9954479b081664bd4504c90fb66fba5fd22c8`.
The commit changes only these two new files:

- `Applications/Resources/NaturalRunOperations.lean`: 29,861 bytes, 690 lines,
  SHA-256 `c5742c0b6e1617b9646aaf9b92d8c5f4dfd02457735c1eb6d4a561fede258e24`.
- `Examples/NaturalRunOperations.lean`: 15,966 bytes, 352 lines,
  SHA-256 `fe08adbd075edbed29bd094e3c3a4d5ef156b31cf84463f5b1957c5f019dff9a`.

The core contains 63 declarations (six definitions and 57 theorems); examples
contain 43 theorems. All 106 declarations received full static intended-statement
and source readback, with zero unresolved mathematical/statement findings. The
299-line complete author assessment and all per-claim rows are in
`author-assessment.md`, SHA-256 `03ececbd93a3b763965379ee5a15576b02fc379c5670a46e6e5dae41f819704a`.
The copied-source declaration headers, exact identities and text-only checks are
saved in `source-inventory.json` and `static-source-checks.json`; actual Git
terminal records, complete two-file diff and clean commit receipt are preserved.
These are source observations, not elaborated-type or kernel evidence.

The source now executes the approved actual mutual scanner branches, XD01 callback
creation and applications, direct descending cons, suffix and outer-run cons,
and the fixed entry/test tariff. The arbitrary-builder path equations retain
actual returned callbacks and observations. Rep and AppCost remain separate;
worker bounds do not assume a sorted supplied prefix or a bounded supplied
accumulator. The actual singleton-seeded builder has creation/application count
1+2*m and the proved prefix-size weight. Exact homogeneous costs precede the
simultaneous bounds Wr ≤ 6*n+1, Wa ≤ k+6*m+5 and Wd ≤ 6*m+5.

The base merger observation has an explicit outer-length ≤ 1 domain, including
both [] and [[]]. The composed source execution uses the actual scanner output,
costs scanner work plus one, and is bounded by 6*n+2. Ascending length n≥2 has
scanner/total costs 6*n-5 and 6*n-4; nonempty strict descent has 3*n and 3*n+1.
Empty totals 2 and singleton totals 4 remain separate. No multi-run operational
merger, arbitrary D-law-to-runtime, machine-time or stability claim was added.
Connected cases preserve all planned counts and show multi-run domain exclusion,
arbitrary supplied worker states, unbounded padded empty-prefix callbacks,
expensive captures, repeated application and shared closure counts 5/31/36.

No builds, cache operations, child agents, public import/map edits, global tracker
changes or existing-source edits occurred. All recorded dependency and pin bytes
still match fixed base 0ec. Actual Lean elaboration, focused terminal evidence,
all 106 actual type inspections, both independent review axes and every complete
candidate/audit/immediate verification gate remain pending. The accepted R and
first pending F remain unchanged. This draft is not accepted or integrated into
the accepted branch. Root owns the immutable compiler checkout and all gates.

Author HEAD is clean at `e1f3b5c43ba3b0f4aca5964f2b4568e06b47700c`. All source, ref and control writes
are now **HELD** pending root diagnostics or an explicit further release.


## Operational correction 1 — actual partial diagnostic, proof-only successor

Root observed the still-live central nine-target attempt at `e4965499954e2afe6bb6be0b8a4a61167a0ff2ce`. The complete secured prefix is 20,626 bytes, SHA-256 `301c176cae878f0a321efe879cfbe9df1dbcd731760ba3dfe0a47306ee86222f`; its observation explicitly has no terminal result. No aggregate success or failure is inferred.

`buildAscending_counts_add_three` had two `omega` failures because `List.length_cons` expanded `[last]` and left `[].length` unconstrained; the subsequent `List.length_singleton` was unused. The sole source change replaces that simp argument with `List.length_nil`. All 106 declarations and statements, every supplied case/count, and the whole examples file are otherwise byte-identical to e1. No definition, hypothesis, tariff or domain changed.

The exact clean successor is `c7aa6fa810af070434155ece48b92470ca4a91ec`, parent `e1f3b5c43ba3b0f4aca5964f2b4568e06b47700c`. Core SHA-256 is `ccbe8f58dd53cbfaa4600780d5d8a2a78da994ba33c3d6edaa3098446d1f09eb`; examples remain `fe08adbd075edbed29bd094e3c3a4d5ef156b31cf84463f5b1957c5f019dff9a`. `git diff --check` passed; no author compiler or cache was used. Full diff, actual diagnostic identity, statement readback and commit receipt are under `provenance/chapter02-natural-operations-correction1-20261104/`.

The uniform-input draft was saved separately at its prepared 204d prefix and not merged here. Root owns the next immutable compile and all full audit/review/immediate verification gates. No acceptance is claimed. Source/ref/control writes are HELD pending release.


## Operational correction 2 — exact example diagnostics, no statement changes

The fixed attempt5 live-log prefix at central `c0440a99c2a503b7816a44367f7e4168378dbbf1` is 32,431 bytes, SHA-256 `b45bded7778156f7829c4fc80e374276edcc9252ea433f848dbb89ac58239126`. It records the corrected operational core individually built in 138 seconds and 18 diagnostics in its examples. The saved observation has no terminal result; no aggregate exit/pass is inferred.

All 352 original example lines, all 18 exact diagnostic goals and the full correction diff were read. The changes explicitly unfold `natLT` in four descending specializations and the range family, normalize the constant false comparator in the repeated-payload family, and close 12 displayed concrete pair-projection/cons/nil-append goals with `rfl` after their existing source theorem rewrites. All 43 theorem headers, propositions, premises and expected values are byte-identical. The 63-declaration core is completely unchanged, preserving all 106 operational source contracts/cases.

The clean scoped successor is `b87e4e05d89d774a3e217d0fafd271bee4a9cd9a`, parent `c7aa6fa810af070434155ece48b92470ca4a91ec`. It changes only `Examples/NaturalRunOperations.lean` (365 lines, 16,153 bytes), SHA-256 `8bbd6c17eadd48a3af7a7f4c5f8ee3c2e9a97f03317bf373032314cdc835ebbc`. Core remains SHA-256 `ccbe8f58dd53cbfaa4600780d5d8a2a78da994ba33c3d6edaa3098446d1f09eb`. The complete 18-finding record, diagnostic text, proof-only diff, source-header comparisons and readback are in `provenance/chapter02-natural-operations-correction2-20261104/`; readback SHA-256 `683799a40f7835832bc13162ffd69126a8c9e05dc105639dfc97db3608cd9caa`. Actual commit and committed diff-check both exited0.

No author compiler/cache/central edits occurred, and no linter setting or mathematical requirement was relaxed. The separate uniform-input candidate remains clean and frozen at `9d5dcd2cfbd6fc5df572234a85bf4957d0c32a21`. Root owns the next immutable compile, full actual statement inspections, independent reviews and all complete acceptance gates. Source/ref/control writes are now HELD.
