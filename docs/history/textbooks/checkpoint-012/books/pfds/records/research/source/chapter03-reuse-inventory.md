# Chapter 3 implementation reuse inventory

Prepared 2026-11-02 by chapter02_map, read-only apart from this record. Read
`chapter03-union-inventory.md` first; its B3/T6 labels and source review remain
the authority for book/thesis coverage. No Chapter 3 implementation, compiler
run, acceptance decision, tracker change, or Git ref change occurred here.
Chapter 2 remains the formal frontier.

Code inspected in `conaled` (HEAD observed during inspection:
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`). Pinned dependency HEADs agree with
`lake-manifest.json`: Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`. “Existing” below means
the cited definitions/proof bodies were inspected, not that Chapter 3's source
correspondence or exact-candidate acceptance gate has run.

## 1. Local capabilities to preserve

| Component | Existing contract | Boundary for Chapter 3 |
| --- | --- | --- |
| `Applications/Search/LeftistQueue.lean` | `PQ α π` separates arbitrary payload and priority. `Ranked`, `Heap`, `Valid`, `All`, and independent occurrence list `entries` are separate. `fork` uses the source's non-strict rank comparison. `combineQ` really merges right spines; `insertQ` merges a singleton; `deleteQ` returns the root occurrence and merged children, with `none` on empty. | Operations use `LE π`/`DecidableLE π`; ordering proofs need `Std.IsLinearPreorder π`, not antisymmetry or payload equality. Preserve these assumptions and literal tie choices. |
| Same file, shape | `rank_paths` identifies cached rank with shortest empty path and right-spine length. `rank_size : 2^rank q ≤ size q+1`; `rank_log : rank q ≤ (size q+1).log2`. | Substantial direct reuse for B3-LEFTIST/E3.1; source cases and measured operation bounds still need connection. No costed merge occurs in this file. |
| Same file, semantics | `combineQ_entries`, `combineQ_size`, `combineQ_valid`, `insertQ_entries`, `insertQ_valid`, `deleteQ_spec`, `deleteQ_none_iff`, `nullQ_iff`, `makeQ_spec`; `toListQ_perm` and `toListQ_sorted`. Occurrences use `List.Perm`, retaining duplicates. | `toListQ` recursively merges child lists, not repeated `deleteQ`. `makeQ` is right-fold insertion, not adjacent-pair rounds. No direct-insert variant or weight-biased implementation is present. |
| `Applications/Search/PriorityInterface.lean` | `Operations` has Carrier/empty/bulk-add/fused-remove. `Laws` and `Queue` keep observation and validity separate. | Its add contract allows keyed replacement; it is too weak for ordinary heaps. Do not silently change its existing search clients. |
| `Applications/Search/ExactPriority.lean` | In namespace `Search.PriorityInterface`, `ExactLaws` strengthens add to exact permutation; `ExactQueue`, `exactLeftist`, `exactList`, and `ExactQueue.keyed` provide two realizations and a checked weakening. Remove preserves all remaining occurrences and returns a minimum priority. | This is the existing ordinary-heap abstraction to extend. It has no meld, direct minimum observation, separate delete operation, or runtime cost field. `exactList` sorts at deletion; no logarithmic implementation claim follows from its laws. |
| `Applications/Search/PrioritySearchQueue.lean` | List reference for keyed replacement and minimum removal. | Its “book” means the older Algorithm Design with Haskell source, not PFDS. It cannot realize exact duplicate-preserving insertion without changing its semantics. |
| `Applications/Huffman/{Priority,SourcePriority,Observation}.lean` | Generic exact-queue client, checked literal leftist specialization, relational result square and observation composition. `costResult_eq` permits different tied output trees. | Huffman's `pathCost`/`costSquare` concerns the optimization objective, not heap running time. This is a useful architectural client, not a heap cost proof. |

Connected existing examples: `Examples/Huffman.lean` covers empty/singleton,
duplicate occurrences, distinct lawful tied outputs, generic exact insertion,
keyed weakening and composed observation; `Examples/HeuristicSearch.lean`
`literal_leftist_tie` checks that a newly inserted tied path is selected before
the old one. These prevent accidental tie/equality strengthening, but are not
PFDS Chapter 3 figure/exercise cases.

## 2. Pinned dependency reuse: substantial, with source mismatches

### Binomial heaps

`Batteries/Data/BinomialHeap/{Basic,Lemmas}.lean`, namespace
`Batteries.BinomialHeap.Imp`, contains actual executable heaps. This is more
than a topic match:

- `HeapNode α` is an unannotated first-child/next-sibling binary encoding of
  a descending-rank forest. `Heap α` holds top-level rank/root/children/next.
  This is relevant to Exercise 3.6, but is not the book's recursively annotated
  rose tree. A child forest of rank r contains `2^r-1` nodes; adding its top
  root gives the source tree's `2^r` nodes.
- `HeapNode.WF`, `Heap.WF`, `HeapNode.WF.rank_eq`,
  `HeapNode.WF.realSize_eq`, and `Heap.WF.size_eq` prove structural ranks,
  increasing top ranks and size correctness. WF's parent-edge comparison is
  explicitly conditional on `TotalBLE le`. Global descendant minimum proofs
  will also need transitivity; do not read WF alone as unconditional minimum
  semantics for an arbitrary Boolean comparator.
- `Heap.WF.merge`, `.deleteMin`, `.tail?`, and `HeapNode.WF.toHeap` establish
  preservation. `realSize_merge`, `realSize_deleteMin`, and
  `realSize_toHeap` prove numeric accounting.
- `Heap.head?` scans roots directly. `Heap.findMin` carries a difference-list
  context; `deleteMin` reverses children through `toHeap` and merges forests.
  `Heap.findMin_val` and `Heap.deleteMin_fst` prove that this implementation's
  observation/removal select exactly the same occurrence, even for tied
  non-antisymmetric comparators.

Missing from these files: independent occurrence-permutation laws, global
minimum correctness, forest-count logarithmic theorems, exact binary-bit
correspondence, measured comparison/link/traversal bounds, and the source's
annotated/unannotated representation equivalence. The `O(log n)` comments are
not cost theorems. `Heap.merge` is an optimized carry recurrence with additional
rank lookahead, not the printed `merge` calling `insTree`; public `insert` is
singleton merge. Source equation/tie correspondence therefore needs proof, and
the required literal `insTree`/nested merge recurrence cannot be discharged
merely by adopting this backend. Its structural termination measure
`length left + length right` is a useful starting point for a measured bound
on the backend itself.

Recommendation: reuse this carrier and structural lemmas for the unannotated
realization where useful; use a small explicit source representation/adapter
for the annotated rose-tree equations, proving contents, ranks and operation
correspondence. Decide the encoding after the source contract is fixed. Do not
introduce a general tree or heap hierarchy solely to connect two encodings.

### Red-black trees

`Batteries/Recycling/RBTree/{Basic,WF,Depth,Lemmas}.lean`, namespace
`RBTree.RBNode`, provides the actual four Okasaki rotation cases as
`balance1`/`balance2`, `ins`, `setBlack`, independent `Ordered`, inductive
`Balanced`, and temporary `RedRed` invariants. Useful proved results include:

- `Ordered.balance1`, `.balance2`, `.ins`, `.insert`;
  `RedRed.balance1`, `.balance2`, `.setBlack`; `Balanced.ins`, `.insert`.
- `balance1_toList`, `balance2_toList`, `setBlack_toList` preserve inorder
  contents; `Ordered.toList_sorted`, `Ordered.find?_some`, `mem_insert`, and
  `RBSet.find?_insert` supply lookup/content foundations.
- `Balanced.depth_le`, `.le_size`, `.depth_bound`, and `WF.depth_bound`.
  The last bound is exactly `depth t ≤ 2 * (size t + 1).log2`, with depth the
  maximum number of nonempty nodes to nil. It holds for either root color.
  Nil is black and has black height zero.

Two important adapter obligations: `ins` replaces the stored representative
on comparator equality, and public `insert` blackens the result only when the
*old* root was red. The book retains the existing equal element and always
blackens the final root. Under a faithful equality comparator, the first
difference disappears; an explicit source insertion using `ins` and
`setBlack`, or a proven corresponding wrapper, addresses the second. The
dependency's split balancing already resembles E3.10a, but source baseline
balance and actual eliminated-test accounting still need connection. It does
not establish E3.10b's no-off-path-color-tests discipline.

`WF` in Basic includes closure constructors for insert/erase; use the actual
proved `WF.out`/`WF_iff` from WF to obtain ordering and balance. Do not treat
the closure constructors alone as a proof of the source invariants. Lookup
semantics use `Std.TransCmp cmp` and comparator equality; an adapter to literal
set membership must state equality faithfulness. `RBSet.ofList/ofArray` fold
insertion, so they do not discharge E3.9's linear sorted-list construction.

Import the `Recycling/RBTree` modules directly if selected: `Data/RBMap/*`
are deprecated forwarding modules. The library recommends `Std.TreeMap` for
general users, but that recommendation is not a proof that its implementation
matches PFDS's colored algorithm. No local source adapter or resource proof
for this red-black family was found.

### Other tree material and misleading matches

Mathlib `Data/Tree/Basic.lean` gives node-valued `BinaryTree`, `map`,
`numNodes`, `height`; the old `Tree` alias is deprecated. Chapter 2 already
uses it. `Search.OrderedTree` supplies independent contents, strict
`OrderedBy` (only LT to state), membership correctness, comparison bounds and
finite inorder enumeration. `Search.AbstractSet.Ops/Laws` and insertion-word
square/fusion results are the public set interface for colored realizations.
An erasure from `RBNode` to `BinaryTree` can preserve contents/order/height
and reuse those results without another set interface.

`Bracketing.Tree` and `RandomAccess.Tree` are leaf-valued; their perfect-tree
and cached-size proofs are not binomial rose-tree proofs. Targeted local,
Mathlib and Batteries searches found no generic source-compatible rose-tree
library; the concrete Batteries child/sibling encodings are relevant.
`Batteries.Data.PairingHeap` also has a child/sibling tree and a pair-combining
delete, but that operation is not E3.3's repeated adjacent-pair build rounds.
Its amortized complexity comments do not prove those rounds' linear cost.
Mathlib binomial-coefficient/ring files and discrimination trees are unrelated
name matches.

## 3. Smallest compatible API and construction proposals

These are proposals, not implemented definitions or proved statements.

1. **Extend capabilities over the existing exact queue.** Keep the same
   Carrier/entries/Valid and separate operation/law records. Add actual meld,
   peek and empty-test capabilities; expose singleton insertion through
   `add [entry]`, and separate delete through `remove.map Prod.snd` when that
   is the selected implementation. Require meld validity and
   `entries (meld a b) ~ entries a ++ entries b`; require peek/removal
   consistency on valid heaps, not just two unrelated “is a minimum” laws.
   Conversely, a six-operation source HEAP can derive fused removal and bulk
   add with checked `ExactLaws`. Preserve the fixed priority order across a
   meld and leave cost assumptions in separate measured refinements.
   Defining peek as fused removal's projection is semantically possible but
   cannot establish constant-time leftist peek under strict evaluation.

2. **Generic ExplicitMin: exclude the cached occurrence from the rest.** Use
   empty or `NE cached rest`, with contents `cached :: Q.entries rest`, valid
   rest, and cached priority below every rest priority. Peek returns cached;
   remove returns that exact occurrence and refills the cache by
   `Q.remove rest`, becoming empty when rest is empty. Insert keeps the lower
   of new/cached and adds the losing occurrence to rest. Meld combines rests,
   selects one cache and inserts the other. This works for arbitrary payloads
   under a total preorder. Caching an arbitrary minimum *inside* the original
   heap would require an additional same-occurrence tie guarantee, since
   underlying removal could choose a different tied payload. Explicitly prove
   peek/remove consistency, every empty/nonempty branch and exact occurrence
   accounting. Constant peek and inherited insert/meld/delete bounds must be
   conditional on the underlying measured primitive contracts, not attached
   to every `ExactQueue` (the list realization is the counterexample).

3. **Paired construction is a new generic client of lawful meld.** Map inputs
   to singleton heaps; merge adjacent pairs per round, carrying an unmatched
   last heap; stop at zero/one heaps. Prove length changes to `(n+1)/2`,
   validity and exact flattened occurrences. Mathlib `Nat.clog` already has
   the ceiling-halving recurrence (`clog_of_one_lt`/`clog_of_two_le`), including
   zero/one conventions. Prove a geometric level-cost sum with unmatched
   heaps accounted for. Counting n−1 merges or invoking `makeQ_spec` does not
   prove linear time; the cost of each merge depends on its operands' sizes.

4. **Weight bias is a distinct invariant and operational variant.** Reuse
   node-valued `BinaryTree` with a cached-weight label, independent unfolded
   size/contents, cached-size correctness, left-size ≥ right-size and heap
   order. Avoid reinterpreting existing `PQ.rank` laws as weight laws. Extend
   the same heap capability interface. For top-down merge, the merged child's
   size is known from the two cached input sizes; decide child placement
   before recursively computing it. That dependency fact, and root availability
   under laziness/concurrency, need an explicit demand/dependency model.
   No such operational model was found in the searched Search/Resources
   modules; eager extensional equality or store extension does not supply it.

5. **Colored sets reuse AbstractSet and the dependency's balance layer.**
   Prefer a small RBNode/BinaryTree erasure and source operation adapter;
   prove the original four-case balance and split variants correspond, then
   instrument actual comparison and color tests. Keep E3.9's linear builder
   and E3.10b's path-sensitive algorithm as genuine remaining implementations.
   A minimum proposal should not grow a new comparator/set hierarchy.

## 4. Resource and observation machinery available

- `Resources.Measured`, `bind`, `bind_erases`, `reweight_bind`,
  `reweight_bound`, `erasureSquare`; `Resources.Workload.run`, `run_append`,
  `run_invariant`, `run_value_fusion`. These compose actual measured
  algorithms and independent value proofs. Count primitive priority tests,
  cache/rank tests, traversals and modeled allocations distinctly when needed;
  choose a declared weighting rather than smuggling costs into heap laws.
- `Resources.Growth.isBigO_of_nat_bound` turns an explicit natural bound into
  standard real-cast Big-O. Existing leftist rank lemmas suggest first proving
  a merge bound by `rank a + rank b`, then bounding it using both operand
  sizes. Cached rank/weight and arithmetic unit-cost assumptions must be stated.
- `Resources.BinaryCounter` proves `incWithCost_eq`,
  `flipCost_eq_leadingOnes_add_one`, `flipCost_potential`, finite workload
  bounds and observation squares. `Resources.RandomAccessCosts` in
  `RandomAccess/End.lean` has `bits_consT`, `bits_value`,
  `consTRun_count_bits`, `consTRun_potential` and `consRARun_log_bound`.
  These show how to prove a carry projection before transferring arithmetic;
  binomial linking still needs its own projection, rank-gap conditions and
  exact k-link family at size `2^k-1`. A binary-counter name match is not enough.
- `RandomAccess/CacheCosts.lean` separates structural-size traversal and
  one-read cached-size observations. `TreeFlattening/Core.lean` separates
  recursive visits from append copying. Their trees differ, but the cost-model
  separation is directly reusable. `Resources.Potential` telescopes a single
  state trajectory with boundary potentials; it does not establish arbitrary
  branching-persistence amortization or parallel demand guarantees.
- `Resources/Dijkstra/Observation.lean` explicitly states that
  `targetRun_queue` gives value agreement only; Dijkstra's measured selection
  and monolithic store costs are not costs of the equivalent priority queue.

Chapter 2 `SharedTree.Basic/Observation` reuses the existing immutable store,
fresh allocation, backwards references, `Represents.mono`, and relational
squares. Merge inputs must use a common extending store; sharing the same
root twice still duplicates *unfolded occurrences* semantically. Rotation or
linking changes shape, so `Path.Rebuilds` for an unchanged search-path shape
is insufficient. Prove the new fringe/root-address correspondence explicitly
before claiming physical sharing or copied-cell counts. These are mathematical
store claims, not Lean allocator behavior.

## 5. Source gaps and meaningful cases to retain

| Source family | Remaining work after reuse |
| --- | --- |
| B3-HEAP/HEAP-ORDER | Six-operation adapter, separate failures, minimum/occurrence laws, fixed order, cost refinements and connected old/new clients. |
| B3-LEFTIST/OPS/E3.1–3.3 | Connect existing invariant/rank/content proofs to source; actual measured merge/peek/delete; direct insertion; adjacent-pair build, linear total work and exact round convention. |
| B3-E3.4a–d | Cached-weight invariant, full interface, logarithmic spine, bottom-up/top-down variants and explicit demand/concurrency interpretation. |
| B3-BINOMIAL-* / E3.5–3.6 / T6-DIRECTMIN | Annotated source equations and linking/shape equivalence; forest bits/rank counts; actual insTree precondition and nested-merge cost; occurrence/minimum proofs; direct/removal minimum tie correspondence; annotated/unannotated conversion and preserved bounds. |
| B3-E3.7 | Generic cache-excluded wrapper and measured lifting, including tied distinct payloads and cache exhaustion. |
| B3-RB-* / E3.8–3.10 | Source recoloring/equality adapter, erased search and measured logarithmic bounds, four surrounding-subtree cases, linear sorted build, split balance and no-off-path-color-test variant. |
| B3-PERSIST | Pure retained-version observations; new graph refinements for any claimed merge/link/rotation allocation and fringe-address behavior. |

Connected new cases should include: empty/singleton heap operations; identical
duplicate entries and distinct tied payloads; both makeT branches; direct versus
merge insertion; odd/even/non-power-of-two build lengths; weight imbalance and
top-down dependency; binomial ranks 0–3, size 21 with ranks 0/2/4, full carry at
`2^k-1`, tied minimum roots with different descendants, child reversal; all four
red-black rotations, duplicate insertion, both old root colors, and sorted-build
boundary lengths. Every case should invoke or instantiate the public general
contract. Existing fold builders, complexity comments and similar names do not
close these source obligations.
