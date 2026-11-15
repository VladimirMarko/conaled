# Chapter 3 union source inventory (preparation only)

Inspected2026-11-02 by root while Chapter2 implementation/validation continued.
No Chapter3 implementation or acceptance frontier advances through this record.
Owner ticket10003 remains open and depends on accepted Chapter2.

## Source evidence

The complete book Chapter3, printed pp17–30 (PDF29–42), was text-read and
visually inspected page by page, including all six figures, ten exercises and
every subpart. Printed p30 is visibly blank. Book SHA256:
b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41.

Thesis correspondence inspected: definition6.2 p64, binomial portions of
Figures6.2/6.3 p65, section6.2.2 beginningp68 and continuingpp70–72, Figure6.7
p70 and complete Figure6.8 p73. All formulas and code onpp64,65,70–73 were
visually inspected. Thesis p69 belongs to the intervening random-access-list
figure, not the binomial-heap code. Thesis SHA256:
f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072.
The neighboring random-access-list text/figures and other tree families remain
with bookChapter9; inspecting them here does not close their obligations.

Research-only extracts/renders: research-pfds/chapter03. They remain outside
recovery payloads under ADR0001. This paraphrased record and exact source
identity are durable. Text extraction misreads the >= test in leftist makeT as
>; visual inspection confirms the non-strict comparison. It also damages
floor/ceiling marks and several primed identifiers, so code/formulas must not
be reconstructed from raw extraction alone.

## Source items and proof obligations

| ID | Location | Required content |
| --- | --- | --- |
| B3-HEAP | pp17–18, Fig3.1; thesisp70 Fig6.7 | Abstract heap/priority-queue operations empty, isEmpty, insert, merge, findMin, deleteMin. Preserve repeated occurrences, minimum ordering and observable empty failure. Comparison structure is fixed across values that can be merged. Separate operations, validity, independent contents and resource assumptions. |
| B3-HEAP-ORDER | p17 | All descendant values of a heap-ordered tree are at least its root; hence root extraction yields a minimum. Keep this distinct from strict BST ordering. |
| B3-LEFTIST | pp18–20, Fig3.2 | Cached rank agrees with right-spine length; every left child's rank is at least its sibling's. Right spine is a shortest path to empty. makeT calculates the new rank and swaps children when necessary. Actual two-heap merge follows their right spines, preserves occurrences, heap order and rank invariants. |
| B3-E3.1 | p18 | Right-spine node count <= floor(log2(n+1)) for an n-node valid leftist heap, including empty. A size/rank exponential inequality is useful evidence. |
| B3-LEFTIST-OPS | p19, Fig3.2 p20 | Insertion via singleton merge; direct root minimum; root deletion via child merge; empty findMin/deleteMin failure. Worst-case merge/insert/deleteMin logarithmic under explicit unit model; findMin constant. Merge size parameter includes both operands. |
| B3-E3.2 | p19 | A direct insertion implementation, with validity/content and correspondence to insertion semantics. A renamed call to merge does not implement the requested direct recursion. |
| B3-E3.3 | p19 | Build singleton heaps and repeatedly merge adjacent pairs in rounds. Empty and singleton inputs must terminate. Content/validity plus linear total work, and logarithmic round count with an explicit positive-size/zero convention. Sequential fold insertion alone does not discharge the exercise. |
| B3-E3.4a | p20 | For weight-biased heaps (left unfolded size >= right unfolded size), prove logarithmic right-spine length. Cached sizes must be correct. |
| B3-E3.4b | pp19–20 | Modify the full leftist interface to use the weight invariant, not merely prove a lemma about a separate predicate. Preserve heap operations, failures and contents. |
| B3-E3.4c | p20 | One-pass top-down merge using known subtree sizes; determine the resulting node's child placement before recursive return. Establish correctness and the intended dependency/operational distinction from bottom-up makeT. |
| B3-E3.4d | p20 | Account for the top-down version's lazy/concurrent advantages under an explicit demand/dependency interpretation. Extensional equality alone cannot establish earlier root availability; do not turn this exercise into an unsupported runtime speed claim or omit it as history. This may need an actual cross-cutting demand-model prerequisite. |
| B3-BINOMIAL-SHAPE | p21 Fig3.3; thesis definition6.2 p64, Fig6.2(b)/6.3(b) p65 | Equivalence between equal-rank linking and descending child ranks r-1,...,0; rank0 singleton; rankr unfolded node count2^r. link must require equal valid ranks and preserve heap order and all occurrences. Small rank0–3 figures should have checked instances. |
| B3-BINOMIAL-FOREST | pp21–22; thesispp70–71 | Forest roots have strictly increasing ranks, children strictly decreasing ranks; no repeated top rank. Root weights correspond to set bits of total size. Number of trees <= floor(log2(n+1)); rank/child counts logarithmic. Preserve the size21/ranks0,2,4 calculation as a connected example. |
| B3-BINOMIAL-INSERT | p22, Fig3.4 p24; thesisp71/73 | insTree links equal ranks while carrying upward; full insertion starts with rank0 singleton. Correctness/invariants/occurrences and worst-case logarithmic cost; size2^k-1 forces exactly k links. A hypothesis ensuring insTree never encounters a smaller existing rank is necessary for source link preconditions. |
| B3-BINOMIAL-MERGE | p22/24; thesisp71/73 | Merge ranked forests with equal-rank link/carry via insTree. Prove the actual nested recurrence's logarithmic bound; merely multiplying a logarithmic merge depth by a logarithmic insTree bound would be too weak. |
| B3-BINOMIAL-MIN | pp22–24; thesisp72/73 | removeMinTree/getMin returns a minimum-root tree and the remaining forest with exact occurrence accounting. Book findMin projects its result. deleteMin removes that root, reverses decreasing-rank children and merges the two valid forests. All four main operations have explicit worst-case logarithmic bounds and empty errors. |
| B3-E3.5 / T6-DIRECTMIN | p23; thesispp72–73 | Direct findMin scans roots without constructing a residual forest. Prove its result, empty case and source tie choice agree with removeMinTree/getMin projection. This is the thesis's main implementation, not an omitted equivalent variant. |
| B3-E3.6 | p23 | Reimplement all binomial operations using unannotated internal nodes and only top-level rank/tree pairs. Relate the new representation to the annotated one, including rank reconstruction, invariants, behavior, failures and preserved cost guarantees. |
| B3-E3.7 | p23 | Generic ExplicitMin functor for an arbitrary heap implementation, not a binomial-specific wrapper. Cached minimum yields constant findMin; insert/merge/deleteMin retain logarithmic worst-case bounds under explicit primitive-operation assumptions. Prove cache/underlying-contents invariant and all empty/nonempty transitions. State whether cached minimum is duplicated in or excluded from the underlying heap. |
| B3-RB-INVARIANTS | pp24–25 | Colored BST order, no red-red edge, equal black-node count on every root-to-empty path, empty leaves considered black. Root recoloring and path-length conventions must be explicit. |
| B3-E3.8 | p25 | Maximum node depth <=2*floor(log2(n+1)); connect size, black height and ordinary height with the chosen empty/root convention. Prove it for the stated invariant domain, not by assuming balance as the desired height inequality. |
| B3-RB-MEMBER | p25/28 Fig3.6 | Membership ignores colors and refines existing ordered-tree search; combine the actual comparison/visit bound with the red-black logarithmic height result. |
| B3-RB-INSERT | pp25–28, Figs3.5/3.6 | Insert red leaf, allow only the specified temporary violation, perform all four black-red-red rotations, and recolor final nonempty root black. Prove strict order, unchanged/add-one set contents, balance invariants and termination; ins always nonempty. Figure3.5 preserves its four surrounding subtrees and their inorder order. |
| B3-E3.9 | p28 | Linear-time construction from a sorted duplicate-free list, with exact contents and valid red-black invariants for every length, including empty and boundary lengths. Repeated logarithmic insertion does not prove the required linear bound. |
| B3-E3.10a | pp28–29 | Separate left/right balancing functions used at the corresponding recursive insertion return; correctness and explicit removal of unrelated-side color tests. |
| B3-E3.10b | p29 | Further path-sensitive insertion that never tests colors of nodes off the search path. Preserve valid insertion, contents and logarithmic costs; an extensional theorem alone does not establish the promised test discipline. Instrument actual tests or an equivalent source-aware operational relation. |
| B3-PERSIST | p17, pp27–28 | Pure operations retain prior versions. Any claimed copied-cell counts or unchanged fringe sharing need the actual immutable-root model; reuse Chapter2's store/extension tools where the tree form permits it. Rotations change the search path's shape, so the unrotated Rebuilds theorem cannot be applied without a suitable refinement. |
| B3-NOTES | pp26–29 section3.4 | Or-pattern syntax is an equivalent presentation of four shared right-hand sides; compiler portability, historical priority, practitioner speed claims and cited alternative AVL/2–3/weight-balanced trees are context. Do not claim a verified runtime ranking or import every cited algorithm as an extra exercise. |

## Thesis union distinctions

The ordinary binomial representation, equal-rank linking, insTree, merge and
reversed-child deletion match the book's statement families. Their full source
equations were compared, rather than assuming equivalence from headings.
Thesis findMin is the direct traversal requested by bookExercise3.5, whereas
the book's main implementation calls removeMinTree. Both must have a checked
correspondence. Thesisp72 explicitly calls out consistent tie selection between
minimum extraction and root removal. The concrete source chooses the earlier
root on <=; keep a tied-root case with different descendant contents.

The thesis's comparison function is fixed when the heap module is created;
this avoids combining heaps with different orders. Its remark about other
sortable collections is contextual here; those collections retain later owners.
Definitions6.1/6.3 (leaf trees/pennants), binary random-access lists, segmented
binomial constructions and skew binomial heaps remain with bookChapter9 and
the existing supplemental tickets. Reuse of definition6.2 does not close all
of thesisChapter6 or its separate table bounds.

## Existing conaled structure to reuse

Read before designing new interfaces or representations:

- Applications/Search/LeftistQueue.lean already has PQ, size/rank/entries,
  Ranked, Heap, Valid, actual fork/combineQ/insertQ/deleteQ, shortest/right-path
  correspondence, rank_size and rank_log, permutation contents and validity.
  The source-compatible rank comparison is non-strict. Its payload and
  priority parameters are separate, and it supports a total preorder on
  priorities; do not replace this with a needlessly stronger mandatory order.
- Applications/Search/ExactPriority.lean already supplies ExactLaws/ExactQueue,
  preserving every repeated occurrence, and two realizations: existing leftist
  queues and a list reference. Its keyed weakening is explicit. The weaker
  PriorityInterface alone permits keyed replacement and is insufficient for
  ordinary heap contents.
- Existing queue Operations have bulk add and remove; the book additionally
  needs separate minimum observation and meld operators/costs. Extend or adapt
  this architecture with checked realization/forgetful connections, rather
  than invent an isolated competing heap hierarchy.
- Existing leftist makeQ is a fold-based insertion client; it does not implement
  Exercise3.3's adjacent-pair rounds. No proof of linear paired building follows
  merely from its existing correctness theorem.
- Search.OrderedTree and SharedTree provide the new strict-set, observation,
  allocator, retained-old-root and partial-result foundations for colored trees.
  Binomial rose-tree shape and red-black rotation sharing need their own source
  interpretations; avoid equating them to unbalanced tree paths by naming alone.

This inventory does not assert any preexisting declaration has already passed
the current chapter's source/statement review or exact-candidate gate. Each
reuse must identify its actual assumptions and connect the required cases.
