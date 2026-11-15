# Chapter 2 implementation requirements — version 1

Source: the user's original whole-book instruction and REQUEST-union-v2.md.
Primary inventory: research/book-full-inventory.md, complete book pp7–16.
Source-book SHA256 b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41.
Chapter1 introductory accounting accepted at integration82501d108f33c62d21b5e0d0f7d2376b902d8d49.
Chapter2 full change review base is that commit. Its preexisting formal10013
remains separately unaccepted until its own full verification and reviews pass.
No source-access blocker remains. Later chapter work awaits full Chapter2
acceptance except the explicit cross-cutting ticket graph.

## Complete scope

- B2-STACK/LIST/CUSTOM: operation-only stack interface, separate semantic laws,
  empty/isEmpty/cons/head/tail, observable empty failures, built-in List and a
  distinct custom inductive realization, reusable relational observation.
- B2-APPEND-ABSTRACT/LIST: generic append through the stack operators alone,
  terminating valid calls, correspondence to direct recursion and ordinary
  concatenation. Any fuel must be proved sufficient, with no failure on valid
  bounded calls. Preserve empty head/tail failures.
- B2-PERSIST/APPEND-SHARING/UPDATE/E2.1: reuse SharedList10013, prove or map
  exact old-root retention and physical tail identity, copied-cell and terminal
  visit counts, suffix value/order/closure/reachable distinct-cell space.
  Source indices are integers: nonnegative calls refine the Nat traversal;
  negative calls reach empty and fail. Do not relabel a fast negative check as
  source evaluation/cost equivalence.
- B2-ORDER/SET/MEMBER/INSERT: generic ordered node-valued BinaryTree with strict
  all-descendant invariant, independent finite membership semantics, empty,
  member and insert laws. Baseline primitive element comparisons are counted
  separately from visits. Insert copies the search path and preserves actual
  off-path roots; a match returns its subtree but ancestors may be copied.
- E2.2: candidate-carrying member with one comparison per visited node and a
  final equality, correctness and at most d+1 comparisons for node-height d.
- E2.3: duplicate insertion propagates an abort to a single outer handler;
  duplicate case allocates zero cells and returns the original root, while
  absent insertion preserves ordering, content and off-path sharing.
- E2.4: one combined insertion algorithm establishes both no duplicate copying
  and at most d+1 comparisons. Separate algorithms do not discharge this item.
- E2.5a: repeated-value general tree with complete depth d, shared equal child
  roots, unfolded node count2^d-1, exactly d fresh cells and linear modeled work.
  This is not a strict ordered set tree.
- E2.5b: repeated-value general tree with exactly n unfolded nodes and child
  subtree sizes differing by at most1 at every node, produced by create2 paired
  sizes m,m+1 using actual sharing and logarithmic work/cell bounds. State
  small-size and size-parameter conventions explicitly.
- E2.6: minimal finite-map interface and ordered-tree realization with arbitrary
  values, key-only ordering, overwrite-on-bind, optional lookup/missing failure,
  invariant/lookup laws, connected examples, and persistence interpretation.
- B2-NOTES: historical/contextual disposition; no claims to formally prove all
  cited external results or the entire SML/Lean runtime.

## Architecture and validation

Use Mathlib BinaryTree rather than duplicate node-valued tree syntax. Reuse
conaled relational squares, resources and immutable heap algebra; keep
operations/laws, pure values/shared roots, actual recurrences/measures,
correctness/asymptotic assumptions distinct. Generic sources need generic
proofs with their concrete implementations as checked specializations.

Follow AGENTS.md, implement/example-driven-development and review-loop. Every
formal claim needs statement review and meaningful connected public uses.
No admissions, new axioms or unchecked native proof shortcuts. Each new module
must enter SquareApplications and exhaustive audit. Only exact isolated
candidate build/audit, matching verification record, final verify and both
independent review axes allow formal acceptance. Focused compilation is
progress evidence only. All local tracking/reviews/commits enter immediate
uploaded recovery checkpoints; no GitHub writes.

## Parallel assignments within ticket10002

All code is unaccepted implementation until full Chapter2 review. Agents use
separate worktrees from82501d1 and do not edit shared entrypoint/tracker.
Root owns AbstractStack, custom/list correspondence and source integer update.
Pure-tree worker owns Applications/Search/OrderedTree/* and its examples.
Shared-tree worker owns Applications/Search/SharedTree/* and its examples,
including general DAG representation and Exercise2.5 constructions. Root later
connects ordered algorithms to graph traversal; interfaces agreed directly.
Build output directories remain private; external dependency checkouts are
shared read-only. Use supported LEAN_NUM_THREADS=1 for focused builds and
coordinate to avoid redundant simultaneous heavy compiler invocations.
