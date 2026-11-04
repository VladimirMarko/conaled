# Retained parser snapshots

[#282](https://github.com/VladimirMarko/conaled/issues/282) implements an explicit
finite snapshot for the binary alphabet. The native parser still accepts arbitrary
finite words; the bound applies to this retained instance's observations.
[RetainedSnapshot](../../Applications/Languages/RetainedSnapshot.lean) contains the
representation and proofs; [examples](../../Examples/RetainedParserSnapshot.lean)
cover repeated words, shared prefixes, depth boundaries and nullable star.

## Representation and exact meaning

`Tree P n` stores a decision at every node, with separate stored children for
false and true. Neither child is a function that might recompute a derivative
when called. `build p n` recursively constructs both subtrees once and returns
an instrumented derivative-call count. A caller binds and retains that result
for a batch; rebuilding it for each request forfeits the reuse contract.

The key is the word's Boolean path within this one instance. Its identity includes
the originating parser and its selected decisions, not merely the language's
Boolean membership test. Snapshots built from different parsers are not merged.
The witness-sensitive example constructs different selected Boolean witnesses
with identical recognition, so Boolean keys cannot justify such merging.

`build_toTrie` connects the stored tree to native `WitnessTrie.unfold`.
`lookup_build` proves exact `Decision (P word)` agreement with `Parser.parse`.
The proof covers every parser at the binary alphabet, including nullable star;
it does not quotient successful witnesses. The empty-star example retains the
native empty list of empty parses.

A request supplies a visible depth and a word. `query` returns `none` if the
requested view exceeds the stored depth or the word exceeds the requested view.
It does not fall back to parsing or silently expand the cache. A requested depth
of two on a depth-one instance is rejected even for a one-symbol word. This is
an explicit view-validity policy, not an assertion that the word itself is too
long. Rebuilding a larger instance would require a separate lifetime and cost.

For admitted requests, `query_restricted` proves agreement with actual native
`WitnessTrie.truncate`. The implementation uses a depth-checked view of the same
stored tree, avoiding materialization of that truncation. Restriction therefore
allocates no snapshot nodes and consumes no input. The retained case also uses
`truncate_comp` to establish repeated restriction. This reuses the native laws
underlying #274's restriction coherence.

## Counted reuse and overhead

The cost model separates derivative calls, stored decisions, lookup edges and
admission checks. It does not assign the same cost to these different operations
or claim that a derivative's internal work is constant.

- `build_work` counts the actual two derivative calls at each internal node.
  `Tree.size_eq` counts stored decision cells: `cells 0 = 1` and
  `cells (n+1) = 1 + 2*cells n`. Build derivative calls equal `cells n - 1`.
- `parseCounted` instruments the recomputing baseline's one derivative call per
  symbol; `parseCounted_correct` proves both its exact result and count.
  `baseline_instrumented` connects the workload total to those calls.
- `lookupCounted_correct` proves that reading a retained result traverses exactly
  the word length in stored edges. `batch_edges` connects this to batch accounting.
  Queries perform no parser derivative calls.
- `batch` returns the actual decisions with hit/miss counters. It counts two
  bound checks per request as an upper bound on predicate comparisons; the
  second may short-circuit. Computing the list length also traverses the input
  word, in both admitted baseline and retained-query contracts. This cost is
  separate from tree edges and derivative calls.
- The batch retains the same tree, with no lookup insertions, evictions or
  maintenance traversal. `batch_output_size` counts one returned answer entry
  per request, independently of the retained tree. Metadata and witness payload
  bytes are not bounded by the cell count. In particular, selected witnesses can
  have size not represented by the number of nodes.

`repeated_saves` proves a sufficient condition for a strict derivative-call saving
for any repeated admitted word: its repeated baseline calls must be at least
`cells depth`. This includes the initial eager build, not only subsequent hits.
The result does not imply a reduction in every other work component.

The checked depth-two workload uses ten requests with repeated words, a shared
true prefix, and view depths zero, one and two. Its snapshot stores seven cells
and makes six derivative calls. Recomputing admitted words makes fifteen calls.
The retained batch has ten hits, no misses, fifteen stored-edge traversals and
at most twenty bound comparisons. It still traverses request words and returns
ten answer entries. A single two-symbol request instead needs two baseline
derivative calls versus six for the snapshot, exposing eager precomputation's
adverse case. No timing benchmark or universal speedup is claimed.

## Scope and reuse

The implementation fixes the finite alphabet to Bool so that both children are
explicit data without a second generic heterogeneous-table library. Extending
it to another finite alphabet needs complete, duplicate-free enumeration and
dependent child lookup with exact transport. Infinite alphabets need a different
retention strategy. Storage grows with the chosen depth, not a global finite-state
bound for arbitrary parser inputs.

[#263](https://github.com/VladimirMarko/conaled/issues/263) remains open for the
generic function-representation/memoization interface; it had no accepted shared
retained representation to instantiate at this baseline. A future adapter must
preserve exact indexed decisions, parser-instance identity, depth validity,
lookup/build correspondence and explicit retention costs. This binary client
adds no competing generic memoization framework.

EDD began with the missing distinction between `WitnessTrie`'s function children
and a stored finite tree. The new tree discharges that obligation, then reuses
native unfold/lookup/truncate laws. Statement review checks exact same-fiber
results, all parser values, depth-zero and exact-bound cases, rejected views,
nullable star and incompatible selected witnesses. Native APIs are unchanged.
The author supplies a parser, retained depth and requests; eager construction and
their lifetime remain explicit. Semantic correctness, derivative-call savings
and Lean runtime allocation are separate claims. #263/#174 own broader reuse
and resource questions; #235 owns adapter and author-interface obligations.
