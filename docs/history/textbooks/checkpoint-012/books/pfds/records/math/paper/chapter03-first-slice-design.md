# Chapter 3 first-slice implementation handoff

Prepared 2026-11-02 by chapter02_map. Read-only investigation apart from this
record: no Lean edits, builds, branches, commits, or tracker changes. This is a
proposed next slice, not accepted requirements or a chapter-frontier advance.
`session/requirements/chapter03.md` was not present. Chapter 3 remains owned by
local 10003, with the existing Chapter 2 acceptance dependency unchanged.

## Scope and source boundary

Start with the ordinary HEAP interface and baseline rank-biased leftist heap:
**B3-HEAP, B3-HEAP-ORDER, B3-LEFTIST, B3-LEFTIST-OPS, and B3-E3.1**. This is a
bounded vertical slice of Section 3.1, not completion of that section. Direct
insertion, paired construction, and every weight-biased subexercise remain
explicit Section 3.1 follow-ons before moving to Section 3.2.

Source authority is `chapter03-union-inventory.md`, with the fuller reuse map in
`chapter03-reuse-inventory.md` and identities in `union-source-identities.json`.
For this handoff, book pp17-20 were text-read; page images pp18-20 and thesis
p70 were rechecked. The book's `makeT` comparison is **non-strict**: equal
child ranks retain their left/right order. The extraction's `>` is wrong.
Exercise 3.1 uses floor(log2(n+1)); Exercise 3.3 uses ceiling(log2 n) rounds.
The source pages/renders remain research assets, outside deliverable payloads.

| Source obligation | Required first-slice outcome |
| --- | --- |
| Book pp17-18, Fig3.1; thesis p70, Fig6.7 | Six operations: empty, isEmpty, insert, merge, findMin, deleteMin. Exact repeated occurrences, fixed common ordering, minimum observation, and observable failure on empty. |
| Book pp18-20, Fig3.2 | The actual cached-rank constructor and right-spine merge, both rank branches and both root-comparison branches; separate cached-rank/leftist and heap-order invariants. |
| Book p18, E3.1 | Cached rank equals the right spine and shortest empty path; right-spine node count is at most floor(log2(n+1)), including empty. |
| Book p19 and Fig3.2 | Singleton-merge insertion, direct root findMin, child-merge deleteMin, and both empty failures. |
| Book p19 complexity claims | Measured source recurrences, erasure to the existing operations, logarithmic merge/insert/delete bounds under an explicit unit model, and constant root observation. |
| Book p17 persistence statement | Retain prior pure versions. Any physical cell identity/allocation claim requires a separate immutable-store refinement. |

### Book/thesis union differences relevant now

Thesis Fig6.7 explicitly declares the `EMPTY` exception; the book's Fig3.1
annotates the empty failures and Fig3.2 implements them. A total `Option`
boundary is suitable if `none` is explicitly the source empty failure, not a
valid stored value or an unknown execution result. No full SML exception
interpreter is needed just to expose this first heap API.

The thesis explicitly fixes the comparison function at module creation so that
merge cannot silently combine different orderings. Keep one common order in
the operations and validity premises. The inspected thesis correspondence
adds no separate leftist implementation to this slice. Its later binomial
implementation has direct findMin (the book's E3.5), whereas the book's main
binomial code projects removeMinTree; both variants and their tied-root
selection agreement remain later union obligations. Do not import all of
thesis Chapter 6 into this first slice or treat its other tree families as done.

## Existing contracts to reuse

Code was read in `conaled` at HEAD
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`, matching the earlier reuse inventory.
The following are existing declarations, not new checks or Chapter 3 acceptance
results. AGENTS, architectural-quality, domain/glossary, language-direction,
ADRs 0001/0002/0010, README acceptance guidance and example-driven-development
were read for this design.

| Existing component | Reuse directly | Gap to fill |
| --- | --- | --- |
| `Search.LeftistQueue` in `Applications/Search/LeftistQueue.lean` | `PQ`, `entries`, `size`, `rank`, `All`, `Ranked`, `Heap`, `Valid`, `fork`, `combineQ`, `insertQ`, `deleteQ`, `nullQ` | Direct minimum observation and a source six-operation facade; measured refinements. |
| Same module, shape proofs | `fork_ranked`, `fork_rank`, `rank_paths`, `rank_size`, `rank_log` | Source-facing E3.1 specialization and discriminating valid/invalid-rank cases; no replacement rank theory. |
| Same module, semantic proofs | `fork_entries`, `combineQ_entries/size/valid`, `insertQ_entries/valid`, `deleteQ_spec`, `deleteQ_none_iff`, `nullQ_iff` | Connect the new facade and measured erasures to these exact occurrence/minimum contracts. |
| `Search.PriorityInterface.ExactQueue/ExactLaws` in `ExactPriority.lean` | Independent contents/validity; exact insertion and minimum removal; `exactLeftist`, `exactList`, explicit `.keyed` weakening | Meld, direct peek, and empty-test capabilities, with separate laws. |
| `Resources.Measured`, `bind`, `bind_erases`, `reweight_bind`, `erasureSquare` | Actual measured functions and compositional erasure | Heap-specific recurrences and bounds; no new generic execution framework. |
| `Resources.Workload` and `Growth.isBigO_of_nat_bound` | Sequence composition/invariant/value fusion; transfer an explicit natural bound to standard Big-O | Instantiate after the concrete heap cost model is fixed. |
| `Huffman.Priority` / `Huffman.Observation` | `huffman_correct`, `resultSpec_correct`, `treeSquare`, `costResult_eq` | A checked old-client specialization through the new heap facade's ExactQueue connection. Huffman path cost is an optimization objective, not heap runtime. |

The weaker `PriorityInterface.Laws` permits keyed replacement. It is not the
ordinary duplicate-preserving heap contract and must not be silently changed.
The existing `makeQ` is fold insertion, not E3.3's pair rounds. `toListQ` merges
child lists, not a measured repeated-delete implementation.

## Smallest compatible interface change

Keep the existing Carrier, entries, Valid and ExactLaws. Add a small capability
record over the existing **Operations** for meld, direct peek and isEmpty,
plus a separate law record. Do not add cost fields to ExactQueue or demand a
new global heap hierarchy. Suggested law content:

- Valid inputs produce a valid meld, with entries permuted to the concatenated
  input occurrence lists.
- On valid heaps, isEmpty agrees with empty contents.
- On valid heaps, peek agrees with `remove.map Prod.fst`, including the selected
  occurrence when distinct payloads have equal priorities. A mere pair of
  unrelated minimum laws is insufficient.

The source facade can expose empty from the old Operations, insertion as
`add [entry]`, and deleteMin as `remove.map Prod.snd`. The latter projection is
appropriate for deletion; **peek must have its own implementation**. For the
leftist realization, peek pattern-matches the root and does not call deleteQ.
For the list reference, peek may project its real removal; attach no constant
time claim to that realization. Recover the original ExactQueue interface
through a checked adapter, retaining Huffman and keyed-search clients.

Retain arbitrary payloads and the existing priority assumptions. Operations
use `LE`/`DecidableLE`; ordering preservation uses `Std.IsLinearPreorder`.
Rank/size facts require only Ranked; permutation facts do not need antisymmetry.
No payload ordering or equality requirement should leak into the API.

Recover the book's one-field element representation as **`PQ Unit Elem`**:
insert `((), x)` and project minimum entries by `Prod.snd`. This avoids a new
datatype and avoids a redundant payload-equals-priority cache invariant. Its
contents are `entries.map Prod.snd`; occurrence laws transport through the
existing permutation results. Keep the more general `PQ alpha priority` for
existing consumers and tied-payload cases.

## Concrete resource plan

Instrument the actual source merge recursion, with the existing size-sum
termination measure, and prove value erasure to combineQ before bounding it.
Let C count priority comparisons. The intended recurrences are zero for an
empty operand and `1 + C` for the chosen recursive right-child call. Each
nonempty comparison has exactly one returning smart-constructor rank test and
one new node constructor; the number of merge calls is C+1. Record these as
separate modeled observations where needed, then use declared positive
weights for a total-work bound. They are not Lean allocator measurements.

Under Ranked on both inputs, each recursive branch decreases the sum of cached
ranks by one. First prove

`C(a,b) <= rank(a) + rank(b)`.

Then use existing rank_log on **both** operands. With total unfolded size N,
their rank sum is at most `2 * log2(N+1)`. Include a constant for the empty
terminal call; `log2(N+1)+1` is a convenient all-N total-work envelope.
State the unit assumptions for comparison, cached-rank access, arithmetic and
constructor work. These are not universal runtime bounds for an arbitrary
expensive priority comparison implementation.

Insertion uses a direct singleton constructor and measured merge, erasing to
insertQ (whose singleton smart constructor reduces to the same tree). If exact
rank-test counts are stated, distinguish that direct source constructor from
executing a general smart constructor. Deletion charges root dispatch plus
measured merge of the children. **Do not bound deletion by the old root rank
alone:** a left child's rank can be much larger. Bound both child ranks/sizes.
Direct peek performs one root case inspection and zero priority/rank tests,
independently of subtree size. Empty and singleton cases remain explicit.

Resources.erasureSquare and bind_erases supply the composition layer. A uniform
size bound already expresses the worst-case claim; a Big-O corollary can use
Growth.isBigO_of_nat_bound for size-indexed input families without introducing
an unnecessary maximum over all payloads/heaps.

## Discriminating client expectations, before implementation

These are planned propositions, not newly checked examples. Each must invoke
the public law/erasure/bound it is intended to exercise.

| Case | Independent expected result / connection |
| --- | --- |
| Empty and singleton, including an optional stored element | Both empty observations fail; singleton peek returns its occurrence and deletion returns an empty valid heap. A stored `none` must remain distinguishable from heap failure. Use facade and ExactQueue laws. |
| Equal-rank children | With two rank-1 children, makeT retains their order and returns rank2/size3. This detects the extracted `>` error. Use fork/rank/entries results. |
| Right child larger than left | makeT(root, empty, singleton) swaps children and returns rank1; both contents and heap order survive. |
| Cached rank is not trusted | A one-node raw tree with cached rank100 can satisfy Heap but fails Ranked. Rank1/size1, rank2/size3, rank3/size7 and empty instantiate the intended logarithmic convention. |
| Duplicates and aliasing | Inserting the same entry twice leaves two occurrences. Melding a heap with itself doubles unfolded occurrences/size. Neither operation deduplicates by payload or address. |
| Tied roots with distinct payloads | Source meld chooses the left operand's root on `<=`; singleton-first insertion chooses the new tied entry. Peek observes the occurrence that delete removes. Also instantiate a priority preorder that ignores an auxiliary tag to expose accidental antisymmetry assumptions. |
| Direct peek versus deletion | A valid rank2 root with two nonempty singleton children gives peek zero priority comparisons; deletion performs one child-merge comparison. This rejects the cost claim for peek implemented by projecting deleteQ. |
| Composition and independent reference | Derive the contents/minimum result of insert, meld, peek and delete through the public laws for both leftist and list realizations. Reuse Huffman's generic correctness/observation through the ExactQueue adapter, preserving the existing unequal tied trees with equal optimum objective. Do not require identical tied output shapes. |

## Dependency order and stopping point

1. Parent records the exact first-slice requirements against the union source
   IDs and selects its base only after the existing Chapter 2 gate. This note
   does not perform those tracker/acceptance actions.
2. Add the small heap capabilities/laws over existing Operations/ExactQueue,
   with empty, duplicate and tied-occurrence clients. A plausible module is
   `Applications/Search/HeapInterface.lean`; naming is an implementation choice.
3. Realize them with existing leftist operations and the direct root observer;
   add the `PQ Unit Elem` source specialization. Connect Fig3.2 equations and
   E3.1 using the existing rank/content/validity proofs.
4. Add `Applications/Resources/LeftistHeap.lean` (proposed name): actual measured
   constructor/merge/peek/insert/delete refinements, erasures, exact counters,
   rank bounds, then size/Big-O corollaries. No framework or toolchain change.
5. Grow `Examples/LeftistHeap.lean` alongside those declarations, including the
   generic composition and existing-client connection. Integrate the public
   closure; parent performs stable-candidate build/audit, statement/source
   review, final verification and both independent review axes.
6. Stop this slice. Continue Section 3.1 with E3.2 direct recursive insertion,
   then E3.3 generic adjacent-pair rounds using lawful meld and its size-sensitive
   cost bound. Odd tails, 0/1 inputs, n-1 merges and ceiling-log rounds need
   explicit conventions. Counting merges alone does not establish linear work.
7. E3.4 follows with a real cached-weight invariant/full interface, then top-down
   merge. E3.4d needs an actual demand/dependency interpretation and a checked
   connection to the heap algorithm. The suspension foundation is a reusable
   prerequisite, not a proof of earlier root availability or parallel speed.

The ordinary first slice does not require a new lazy evaluator. The later
binomial and ExplicitMin work can reuse this capability boundary; retain the
cache-excluded minimum design from the reuse inventory so distinct tied
payloads do not silently change which occurrence deletion removes. Physical
merge sharing, if claimed, needs a new two-input fringe/root refinement over
the existing store: the unchanged-search-path Rebuilds law is insufficient.

This makes the next slice concrete. No additional exploration, implementation
or optional validation was performed after preparing the handoff.
