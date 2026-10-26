# Finite symmetric lists and prefixes

Issue #170 reconstructs finite sequence operations from checkpoint 233. The
implementation is in `Applications/Sequences/Symmetric`; checked applications
are in `Examples/SymmetricLists.lean`. The preserved archive remains unchanged.
The [declaration ledger](adwh-symmetric-lists-ledger.json) records each source
name, destination and disposition, with archive and member hashes.

## Representation and reuse

`Core` retains the actual pair algorithms. `fromSL (front,rear)` means
`front ++ rear.reverse`. `Inv` only constrains an empty side: the other side
then has length at most one. It permits arbitrarily uneven nonempty sides.
It neither implies balance nor establishes amortized cost. Empty endpoints
return `none`, and deletion from empty returns empty.

`Prefixes` uses standard `List.inits` and the shared reachable scan fusion law.
The ordinary append scan proof supplies the independent prefix specification
for both symmetric and reversed accumulators. Conversion uses shared reachable
foldr fusion. Standard inits append and tails/reversal laws replace the source's
local list library. `Finite` preserves the exhaustive four-element
classification and offline reverse/tails/reverse/map-reverse algorithm.
Finite indexed observations use standard folds; symmetric accumulation uses
shared reachable foldl fusion, and reversed accumulation uses standard List
simplification. No lazy-domain or cost implementation is imported.

`Observation` interprets raw pairs by `Inv s ∧ fromSL s = xs`. Existing
`Relational.compose` combines actual insertion, deletion and endpoint-query
squares in `editHead`. Its specification edits ordinary lists. The second
consumer composes nested prefix generation with represented length observation.
The resulting lengths are `List.range (lengthSL s + 1)`, including zero and the
full length in order. Prefix output validity includes both outer and inner
representations. Proofs inspect neither decoded implementation equality alone
nor a source-specific correctness predicate.

Core operations and list theorems are universe generic. The existing relational
interface puts representations and semantics in one universe. The length
consumer therefore lifts `List Nat` with `ULift`; `.down` exposes the ordinary
result. This changes no list content and introduces no monomorphic restriction.

## Statement review and checked applications

The initial missing connections were from the source algorithms to standard
`List.inits`, the shared fusion laws, and actual composed consumers. The
retained examples discharge those connections through public contracts.
Source implementation proofs were retained when they concern representation
cases or well-founded recursion; generic fold/scan/list proofs were replaced
where existing contracts fit.

- Queries, reversal, conversion and invariant tests: the decoder is the
  independent sequence meaning. Invariant tests are iff statements. Singleton
  and empty cases are total and non-vacuous. `reverseSL_reverseSL`, length,
  null/single tests and `headSL_eq_none_iff` retain their raw-pair domain.
- Cons/snoc: output validity is unconditional, but decoder correctness needs
  input validity. The malformed pair `([], [1,2])` demonstrates the distinction:
  snoc restores validity but reverses the represented original prefix. No
  stronger balance or element-distinctness assumption was added.
- Split, tail and init: half splitting retains floor division and reversed
  suffix. Semantic correctness has exactly the original validity premise.
  Strict length descent for tail/init holds for every nonempty raw pair.
  Concrete odd/even rebalancing and the dual init branch check the actual
  representation, while public decoder theorems establish ordinary deletion.
- Recursive dropWhile: the Boolean predicate is tested on represented heads;
  the recursion uses represented tail, with raw length termination. Validity
  and decoder theorems require valid input. Checked cases remove none, all,
  or elements across a rebalance boundary.
- Prefix algorithms: equalities are exact ordered lists, including repeated
  values, empty and full prefixes. Outer `initsSL` validity is unconditional;
  inner validity and decoded enumeration require valid input. All four finite
  implementations are checked on `[1,2,1]`, and the composed length consumer
  yields `[0,1,2,3]`. Empty input yields `[0]` for lengths.
- Representation classification: arbitrary symbolic elements cover repetitions
  as well as distinct elements. All three constructor paths feed the same
  endpoint-edit consumer. The theorem is an exhaustive iff, not a list of
  possible witnesses. A highly uneven valid representation checks the weak
  invariant directly.
- Finite indexed scans: zero and three-element indexed observations use public
  value theorems. The public `finitePrefix_foldl_shift` quantifies arbitrary
  accumulator types, seeds and input functions. Private `sourceScanState`
  retains the exact source shifted-input recurrence; its successor law and
  equality to finite foldl prove correspondence for arbitrary seeds and shifts.
  The recurrence is not offered as another public scan framework.
- Consumer squares: representation validity travels through composition; query
  and prefix-length conclusions follow from `.preserves`. Length enumeration
  uses standard inits indexing, so neither ordering nor cardinality is assumed
  as a premise.

These checks establish finite semantics, not a proof that every informal
textbook intent has been captured. The integration workflow supplies independent
Standards/Spec and originating-intent review, full build and exhaustive audit.

## Provenance and remaining scope

The archive SHA-256 is
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
The two primary members are `ADWH/Chapter03/SymmetricLists.lean` and
`ADWH/Chapter03/SymmetricPrefixes.lean` under `project/adwh-lean/`.
Their hashes are respectively
`259b40fb4710846f4dd4d9dfede16548ade259c65428c1a025b75190377810d2` and
`4b22ff629c7967c09580e77acd2278135b2cbbfb4a966e85d90d73cbe03f1e5c`.
The inspected helper member `ADWH/Chapter01/LazyListEvaluation.lean` hashes to
`4f6308bd80e6b10c58d2eb97dbccf40abb8e3b625e2f93b1d5288c6e277ad01c`;
only `scanState` and `scanState_succ` (lines 154–163) are reconstructed.
Actual ZIP bytes and extracted source bytes were compared before implementation;
member bytes and archive hashes were checked again for ledger generation.

The initial inventory counted 66 SymmetricLists declarations because its regex
missed five same-line `@[simp]` declarations. All 71 are included here, together
with the 15 selected finite SymmetricPrefixes declarations. The primary ledger
therefore has 121 rows: 86 selected and 35 deferred. The two finite helper rows
bring the ledger to 123. This corrects accounting without expanding the agreed
mathematical scope. Public source-facing names are preserved except where their
semantics deliberately use standard List definitions; private helper names are
identified as such in the ledger.

Twenty evaluator/demand-cost declarations remain in the preserved reference.
They are finite computations but use delayed observations and explicit costs;
outer work and total symbol work are different claims. Fifteen lazy-domain
statements remain reference, including finite-input statements whose codomain
is lazy. No continuity, partial/infinite behavior, productivity, reversal to
bottom, delayed-output cost, or asymptotic cost result is claimed here. Each
remaining declaration is named individually in the ledger and remains under
#149 for a later explicit slice.
