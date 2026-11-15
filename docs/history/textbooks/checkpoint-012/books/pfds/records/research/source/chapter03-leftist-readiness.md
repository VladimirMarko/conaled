# Chapter 3 §3.1 leftist-heap readiness

Prepared 2026-11-02 by `chapter02_ordered`. This is bounded implementation preparation by a prior contributor, **not independent acceptance review**, Chapter 3 acceptance, or permission to bypass Chapter 2's exact gates. No Lean source, build, Git index/ref, tracker, or chapter-status changes were made. The sole output is this report. The inspected worktree was `purity-foundation`, observed at checkpoint-021 HEAD `501a95463f455b52ea839eb8bbcf6ab9379862e4`; that is an evidence locator, not a selected Chapter 3 implementation base.

## Readiness decision and scope

The existing first-slice plan is concrete and compatible with the repository. Reuse the current `PQ`, cached-rank invariant, heap-order invariant, exact occurrence interface, rank proofs, resource observations, and generic clients. Add only the missing source-facing capabilities, direct minimum observation, measured refinements, and connected cases. No fresh heap datatype, replacement rank theory, generic evaluator, or suspension dependency is needed for this baseline slice.

The scope remains **B3-HEAP, B3-HEAP-ORDER, B3-LEFTIST, B3-LEFTIST-OPS, and B3-E3.1**. This does not complete §3.1. `session/requirements/chapter03.md` was absent at inspection: the parent must record the first-slice requirements and exact base after Chapter 2's gate. Later exercises and chapter families retain their obligations.

Primary planning inputs were `chapter03-first-slice-design.md`, `chapter03-union-inventory.md`, and `chapter03-reuse-inventory.md` in `session/research`. The first two inspected SHA256 values were respectively `a1f11a6c5db07b5494116a10611a5c03ef8eee7bce869131085a1f93ff7f212f` and `4f60dbb09f793f5f5ff2e21f67ca002abfe36d511389463d2be13f46f29f2da1`.

## Exact source confirmation

Text and rendered images were inspected for **book printed pp17–20** (physical PDF pp29–32) and **thesis printed p70** (physical PDF p82). The research images are `research-pfds/chapter03/book-p17.png` through `book-p20.png`, and `thesis-p70.png`. Sources remain research assets outside deliverable payloads; this report contains locators and paraphrases only.

| Exact source | Consequence for this slice |
| --- | --- |
| Book pp17–18, Fig3.1 | The six HEAP operations are empty, isEmpty, insert, merge, findMin, deleteMin. Minimum observation and deletion expose empty failure. |
| Book pp18–20, Fig3.2 | Rank counts nonempty right-spine nodes to an empty child. The left child's rank is at least the right child's, and merge descends the selected right spine. |
| Book p19 and Fig3.2 p20, both visually checked | **makeT uses a non-strict rank comparison. Equal-rank children retain their order.** The extracted `>` is an OCR error. Existing `fork` agrees. |
| Fig3.2 | Root comparison is non-strict too: equal priorities select the first heap's root. Insertion merges a direct singleton as the first operand. findMin reads the root directly; deleteMin merges its children. |
| Book p18, E3.1 | Right-spine length is at most floor(log₂(n+1)), including the empty tree. |
| Book p19 | The logarithmic merge/insert/delete and constant minimum claims need a declared unit-cost model; they are not universal bounds on arbitrary priority-comparison implementations. |
| Thesis p70, Fig6.7 and adjacent explanation | EMPTY is explicitly declared. The comparison is fixed at module creation, so heaps merged together use one common ordering. This inspected correspondence adds no separate leftist implementation. |

Book SHA256: `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`. Thesis SHA256: `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`. The PDFs are `research-pfds/source-assets/okasaki-book-2003.pdf` and `okasaki-thesis-1996.pdf`.

## Exact existing reuse points

All declarations below were read; this task did not recompile them or establish Chapter 3 acceptance.

| Existing module/API | Intended use and premise boundary |
| --- | --- |
| `Search.LeftistQueue.PQ`, `entries`, `size`, `rank`, `All` | Keep the payload/priority carrier and occurrence semantics. `entries_length` connects unfolded size to occurrence count. No payload equality is needed by operations. |
| `Ranked`, `rank_paths`, `rank_size`, `rank_log` | Cached ranks equal both shortest empty-path length and right-spine length; `2 ^ rank ≤ size + 1`; the logarithmic bound. These require Ranked, not Heap or a priority order. |
| `fork`, `fork_ranked`, `fork_rank`, `fork_size`, `fork_entries` | Source makeT, including equal-rank order preservation, right-heavier swapping, shape, and occurrence laws. |
| `Heap`, `root_all`, `Valid` | Keep all-descendant priority order separate from rank correctness. `Valid` combines the two. Reflexive/transitive total-preorder reasoning suffices; no antisymmetry or payload ordering is needed. |
| `combineQ_entries`, `combineQ_size`, `combineQ_ranked`, `combineQ_heap`, `combineQ_valid` | Meld's exact occurrences/size and invariant preservation. Contents permutation does not depend on valid ranks or a lawful total order. |
| `insertQ_entries/valid`, `deleteQ_spec`, `deleteQ_none_iff`, `nullQ_iff` | Exact insertion, minimum removal, remainder validity, one-occurrence deletion, size decrement, and failure/emptiness agreement. |
| `PriorityInterface.Operations`, `ExactLaws`, `ExactQueue`, `exactLeftist`, `exactList` | Reuse existing carrier/contents/validity and duplicate-preserving insertion/removal. Keep the checked `.keyed` weakening; the older keyed laws permit replacement and are insufficient for source heap contents. |
| `Resources.Measured`, `bind_erases`, `reweight_bind`, `erasureSquare` | Record an actual instrumented operation, then expose value erasure and additive observations. Do not introduce another execution framework. |
| `Resources.Workload.run_state`, `run_append`, `run_invariant`, `run_value_fusion` | Compose operation sequences and connect their values through the existing reachable-fold machinery when the concrete client needs it. |
| `Resources.isBigO_of_nat_bound` in `Applications/Resources/Growth.lean` | Transfer an explicit natural bound to standard real-cast Big-O for size-indexed families. **The public namespace is Resources, not Growth.** |
| `Huffman.Priority.huffman_correct`, `Huffman.Observation` result/square theorems, `Huffman.SourcePriority` equations | Retain a checked old-client connection through ExactQueue. Huffman objective cost is not heap execution cost; different tied trees may have the same optimal objective. |

Inspected SHA256 values: `LeftistQueue.lean` `14a0d1130e04e2576dea2abb452823b5504cdbac9dbc1010f15a2f327c6bc378`; `ExactPriority.lean` `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879`; `PriorityInterface.lean` `8c1b6d6a08c8d0be52efe211affa7032d02b52e383e8bbdd4a4af82b22ee18a6`.

## Public HEAP obligations and minimum API addition

Use the plan's small capability record **over existing Operations**, with `meld`, `peek : Carrier → Option (payload × priority)`, and `isEmpty`, plus a separate law record over the existing contents and validity. Do not replace ExactQueue or add runtime cost fields to its generic contract.

Required laws on valid inputs are meld validity and concatenated occurrence permutation; isEmpty iff empty contents; and **peek equals the entry projection of actual remove**. The last law identifies the very occurrence selected for deletion, including distinct payloads with equal priorities. Two unrelated minimum laws would not provide this agreement.

The source facade derives empty from the existing operation, insert from `add [entry]`, and deleteMin from the remainder projection of remove. Its public results should state empty validity/contents, insertion of exactly one occurrence, exact merge contents, minimum membership/order, deletion of the observed occurrence, remainder validity, size decrement, and both empty failures. One common order is fixed for the operations and validity of both merge operands.

For leftist heaps, **peek must directly inspect the root**. Its equality to `remove.map Prod.fst` is a theorem, not an implementation using deletion in a strict language. The reference list realization may use its actual removal without a constant-time claim. Keep arbitrary payloads and the current total-preorder assumptions. Recover the book's element-only view with `PQ Unit Elem` and `entries.map Prod.snd`; avoid a duplicate datatype or payload-equals-priority invariant. Interpret `none` as EMPTY at this total interface boundary, distinct from a legitimately stored optional element.

## E3.1 and deletion: prerequisites to preserve

E3.1 follows directly by transporting `rank_log` along `(rank_paths q ranked).2`; the latter equates cached rank with right-spine length. The other projection supplies the shortest-path equality. Thus the new source-facing statement needs **Ranked only**, and should retain the existing natural floor-log convention. Do not build the desired log inequality into a new invariant. A raw singleton with stored rank100 can satisfy Heap but fails Ranked, so heap order alone cannot justify the bound.

For measured merge, let C count actual priority comparisons. Empty operands give zero; either nonempty branch gives one plus the recursively selected comparison count. In that branch the selected operand's rank decreases by exactly one under Ranked. Therefore the first useful bound is

`C(a,b) ≤ rank a + rank b`.

Apply `rank_log` to both operands. For total unfolded size N, this is at most `2 * log₂(N+1)`. Insertion uses a rank1 singleton, giving the useful `1 + rank q` bound before conversion to size.

Deletion must use **both child ranks**, extracted from the root's Ranked proof. For nonempty input size n, child-merge comparisons are bounded by

`rank left + rank right ≤ log₂(size left + 1) + log₂(size right + 1) ≤ 2 * log₂ n`.

The old root rank alone is inadequate. A valid root of priority0 can have a perfect left subtree of rank k, all priorities1, and a right singleton of priority2. Its own rank is2 for every k≥1. Deletion follows the left right spine for k comparisons because each left root wins. This family gives unbounded deletion comparisons at fixed root rank; the concrete k=3 case already defeats the literal bound C≤root-rank. Empty deletion and singleton deletion still need their declared constant work/failure cases.

## Resource conventions that prevent later rework

Use an actual instrumented recursion erasing to `combineQ`, then prove counters and bounds. With C priority comparisons, the planned source model has C smart-constructor rank tests, C constructed merge nodes, and C+1 merge calls. If the chosen weights are wp, wr, wn, wc, total measured work is

`(wp + wr + wn + wc) * C + wc`.

Consequently a valid uniform bound is `2 * (wp + wr + wn + wc) * log₂(N+1) + wc`. The plan's `log₂(N+1)+1` is an asymptotic envelope **with a constant multiplier**, not an exact coefficient-one bound for all these observations. Cached-rank access/arithmetic costs must be declared inside the smart-constructor weight or separately instrumented. Exact source rank reads include both sides of the test and the selected rank again; do not assume compiler common-subexpression reuse without saying so.

Source insertion constructs its singleton directly. That contributes a node constructor, not an extra general makeT rank test. Direct peek has one root dispatch and zero priority/rank tests. These modeled constructor events are not physical allocator calls, retained-cell counts, or measurements of Lean execution.

Two small boundary details deserve explicit implementation decisions:

- Source merge checks an empty second operand first; `combineQ` checks the empty first operand first. Values and the proposed priority/rank/node counters agree. If individual constructor tests become an observation, preserve the source branch order or explicitly use an aggregate call-dispatch convention.
- `Measured` supports distinct value/cost universes, but `Resources.erasureSquare` uses one universe for its input, output and cost. The PQ carrier permits independent payload/priority universes. Preserve those generalities; use a local `ULift` boundary where needed, as existing Huffman observations do, rather than silently restricting PQ or changing the shared square framework.

Existing `makeQ` is fold insertion, not E3.3 pair-round construction; `toListQ` merges recursively collected child lists, not repeated delete; `singleQ` calls deletion and is not the required direct constant-time root observer.

## Concrete next implementation handoff

After Chapter 2's exact gate, the parent can record the scoped requirements/base and start the existing example-driven loop in this order:

1. Add the small capabilities/laws in a proposed `Applications/Search/HeapInterface.lean`, retaining ExactQueue literally or via a checked adapter. Realize both leftist and list interfaces.
2. Add a narrow leftist source adapter with direct peek, `PQ Unit Elem`, Fig3.2 equations, and E3.1 transported from existing theorems. File placement is an implementation choice; no new carrier is justified.
3. Add proposed `Applications/Resources/LeftistHeap.lean`: measured makeT/merge/insert/delete/peek, erasures, exact counters, rank-sum bounds, size bounds, then optional standard Big-O corollaries. Fix the counter/weight model before proving complexity.
4. Grow `Examples/LeftistHeap.lean` alongside those declarations, using public laws rather than duplicate local proofs. Include generic operation composition and an existing Huffman connection; do not demand identical tied result trees from different implementations.
5. Parent integrates the public closure and runs the required stable-candidate gates and independent review axes. This readiness pass supplies no substitute evidence.

The discriminating cases should include empty/singleton and stored optional values; equal-rank child order and right-heavier swapping; forged ranks versus valid sizes0/1/3/7; duplicate insertion and melding a heap with itself; tied roots with distinct payloads/new-singleton precedence; a non-antisymmetric priority preorder; direct peek versus a deleting root with two nonempty children; the fixed-root-rank deletion family; and a higher-universe square client if the public adapter is universe-polymorphic. Self-meld doubles unfolded occurrences/size even if a future implementation shares physical cells.

### Stopping point

Retain E3.2 direct insertion; E3.3 adjacent-pair construction with odd tails, exact rounds and linear total work rather than merely n−1 merges; every E3.4 weight-biased/top-down/lazy/concurrent obligation; binomial work and E3.5–E3.7; and red-black work and E3.8–E3.10. No later source milestone is advanced. Physical two-input sharing needs its own immutable-store refinement if claimed; the existing one-search-path rebuild relation alone is insufficient. The suspension foundation can support later demand claims but establishes none of E3.4d's heap-specific root-availability or concurrency claims by itself.

No additional baseline-source ambiguity or foundational blocker was found. Remaining uncertainty is ordinary implementation detail—precise capability names/file placement and the declared cost weights—to be fixed in the scoped requirements before code, not an unbounded research prerequisite.
