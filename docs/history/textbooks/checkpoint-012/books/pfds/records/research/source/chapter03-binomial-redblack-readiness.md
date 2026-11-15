# Chapter 3 binomial-heap and red-black-tree proof readiness

Prepared 2026-11-02. This is source-to-statement preparation, not an
implementation, acceptance review, or completion claim. Chapter 3 remains
unstarted until Chapter 2 is accepted. No Lean source, dependency, toolchain,
compiler artifact, Git reference, tracker, or GitHub object was changed for
this investigation. The only authored artifact is this note.

Read with `chapter03-union-inventory.md` and `chapter03-reuse-inventory.md`.
Their leftist-heap and paired-round material is deliberately not repeated.
The intended additions below are proof obligations, not established local
theorems. Existing declarations are identified separately.

## 1. Evidence and exact source mapping

The inspected book is the user-supplied
`research-pfds/source-assets/okasaki-book-2003.pdf`, SHA256
`b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
The thesis is `research-pfds/source-assets/okasaki-thesis-1996.pdf`, SHA256
`f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`,
from <https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/dissertation.pdf>.
Both identities were rechecked against the files and
`union-source-identities.json`. Book printed page p is PDF page p+12.
Thesis printed page p is likewise PDF page p+12 in the supplied extraction.
Pages below use printed numbering.

Book pp21–29 and thesis pp64,68,70–73 were text-inspected; the actual book
code/formula images on pp24–25 and 27–28 and thesis p73 were also inspected.
The parent inventory records visual inspection of the complete chapter and
the thesis binomial portions of p65. OCR damages comparison symbols, primes,
and floor marks; the source-image readings control those details. Manuscripts,
OCR, and page images remain research inputs outside the checkpoint payload
under ADR0001; this paraphrased evidence record is suitable for preservation.

| Source item | Book location | Thesis union counterpart | Proof content to retain |
| --- | --- | --- | --- |
| Binomial shape and linking | §3.2 p21, Fig3.3; full code Fig3.4 p24 | Definition6.2 p64; binomial portions of Figs6.2/6.3 p65; §6.2.2 pp71,73 | Equivalence of equal-rank linking and descending child ranks; rank-r tree has 2^r nodes; equal-rank link preserves shape, order, and occurrences. |
| Ranked forest and binary weights | pp21–22 | pp70–71 | Distinct increasing top ranks, decreasing child ranks, exact set-bit interpretation, logarithmic forest length; size21 has ranks0,2,4. |
| Literal insertion and nested meld | p22, Fig3.4 p24 | pp71,73 | `insTree` carry precondition; singleton insertion; the actual `merge`/`insTree` recurrence; exact k-link case at size 2^k−1. |
| Minimum-root extraction and deletion | pp22–24 | pp72–73 | Minimum root and residual forest, exact occurrence removal, reverse children before meld, observable empty failure. |
| Exercise3.5 | p23 | Direct `findMin` is the main thesis algorithm, pp72–73 | Direct root scan without residual-forest construction; exact agreement with the root chosen for deletion, including ties. |
| Exercise3.6 | p23 | p71 remarks that internal rank annotations are redundant; no replacement implementation is supplied there | Reimplement every operation with ranks only on top-level trees, including representation, behavior, validity, and cost correspondence. |
| Exercise3.7 | p23 | No corresponding ordinary-binomial wrapper in the inspected thesis section | Generic `ExplicitMin`, cache separated from the rest; constant peek and conditional logarithmic insert/meld/delete. |
| Red-black invariants and search | §3.3 pp24–25; Fig3.6 p28 | No red-black implementation in the inspected thesis union material | Strict BST order, no red-red edge, equal black height, empty-black convention, search correspondence. |
| Exercise3.8 | p25 | None identified | Maximum depth at most 2 floor(log2(n+1)), from structural balance; retain the preceding longest/shortest path consequence with explicit path conventions. |
| Red-black insertion and four rotations | pp25–28, Fig3.5 p27, Fig3.6 p28 | None identified | Controlled temporary violation; four rotations; final black root; independent contents/order and all four surrounding subtrees. |
| Exercise3.9 | p28 | None identified | Sorted duplicate-free list to valid tree in linear time for every length. |
| Exercise3.10a | pp28–29 | None identified | Split left/right balance and remove tests on the unrelated side. |
| Exercise3.10b | p29 | None identified | Insertion must never test colors off its search path; this is an operational property in addition to correctness. |

The thesis's ordinary binomial code has the same annotated shape, linking,
carry and reversed-child deletion equations as the book. Its direct minimum
scan is a real union obligation, not a reason to omit the book baseline.
Thesis p72 explicitly requires minimum observation and removal to select the
same tied root. Figure6.7 p70 fixes the comparator at module construction, so
heaps being melded share an ordering. Searches of the supplied full thesis
text found red-black mentions in the batched-rebuilding discussion (§5.1,
pp49–50) and bibliography, not a second red-black insertion implementation.
Those later rebuilding claims remain with their chapter owner. Likewise,
binary random-access lists, pennants, segmented and skew binomial variants
are not closed by this ordinary-binomial preparation.

## 2. Binomial statements that need to be fixed before proof

### Shape, validity, and contents

Keep the following independently stated: unfolded occurrence enumeration,
rank/shape correctness, heap order, and increasing top-rank validity. The
minimum relation is non-strict and permits repeated entries. An implementation
specialized to the existing payload/priority queue should not impose payload
equality or priority antisymmetry merely to simplify ties.

For a rank-r source tree, the child ranks must be exactly r−1 through 0,
in that order, with recursively valid shapes. Prove equivalence with repeated
equal-rank linking, not just the size equation. The source `link` inspects one
rank and assumes the other agrees: its preservation theorem needs the
equal-rank premise. For a valid forest `ts`, `insTree t ts` also needs the
incoming rank no greater than the first existing rank (or the corresponding
lower-bound invariant). Only then does failure of the strict less-than test
justify linking equal ranks. Calling it on an arbitrary valid tree and
arbitrary valid forest is not a valid general theorem.

State source contents using a recursive list or multiset observation that
retains every occurrence. Insertion adds one occurrence, meld adds both input
multisets, and successful deletion removes exactly the observed minimum
occurrence. Meld of a heap with itself doubles its unfolded contents even if
the physical inputs share one root. Set union or keyed replacement cannot
express these laws. Empty minimum/deletion must remain a partial result;
silently returning an empty heap for empty deletion loses the source error.

For top ranks r1<...<rm, prove n = sum(2^ri) and connection to the set bits
of n. The resulting statements include m ≤ floor(log2(n+1)), each present
rank ≤ floor(log2 n) when n>0, and exactly r children for a rank-r tree.
After removing a rank-r root, reversing its children gives increasing ranks
0,...,r−1. This reversal has both a validity obligation and actual traversal
cost; it is not an uncharged change of notation. [Book pp21–24; thesis
Definition6.2 and pp70–73.]

### Ties and source/backend differences

The printed `link` retains its first root when that root is ≤ the second.
The printed recursive minimum scan and `removeMinTree`/`getMin` retain the
earlier top-level root when tied. Their matching recursive comparison choices
allow a direct source observation/removal agreement proof; the source-to-source
agreement itself need not assume transitivity. Minimum *correctness* does
need lawful ordering assumptions.

Three tempting backend equivalences require care:

1. **Batteries meld does not preserve the source's literal tied choice.**
   Let the left forest have ranks [0,1], with roots A,C, and let the right
   forest have rank [0], with root B. Give A,B,C equal priorities and use
   distinct payloads; the rank-1 tree under C can have a child D of that same
   priority, so both inputs are valid. The source first links A with B,
   producing a rank-1 carry rooted at A, then calls `insTree(carry,C)` and
   links A with C; its resulting root is A. Batteries takes its branch where
   the left tail already has the next rank and the right tail does not. It
   recurses as `merge(leftTail,carry)`, so its next link has arguments C,A
   and its root is C. This follows directly from the inspected equations;
   it has not been compiled as a new example here. Thus an exact value/shape
   operation square with this backend is false for general tied payloads.
   A weaker occurrence/minimum relation may hold, but does not replace the
   required literal-source realization. Even when tied values are literally
   equal, fringe arrangements can differ.
2. **Earlier forest root is not a global left-heap tie rule.** A left
   rank-1 tree rooted at A and a right rank-0 tree rooted at B, with equal
   priorities, meld to a forest starting with B; minimum selects B. Tests
   must follow the resulting rank order rather than assume that every meld
   favors an occurrence from its left argument.
3. **Right-recursive and left-accumulating scans need a law to agree.**
   The thesis uses a right-recursive scan; Batteries `headD` scans with a
   left accumulator. They select the earliest minimum under a lawful total
   preorder, but arbitrary Boolean comparators do not suffice. For a total
   cyclic relation with A≤B, B≤C, C≤A and no reverse comparisons, the source
   scan on roots [A,B,C] returns A while the accumulator returns C.
   Batteries `findMin_val`/`deleteMin_fst` prove its *own* observation/removal
   consistency, even without those order laws; they do not prove equality
   with the differently associated source scan.

These cases do not invalidate the dependency's heap interface. They determine
which observation relation and which literal source implementation can be
claimed. Its `HeapNode.WF` records edge comparisons conditional on a
`TotalBLE` instance; global descendant minimum additionally requires
transitivity. Do not treat `WF` for an arbitrary Boolean function as an
unconditional minimum theorem. [Source ties: book Fig3.4; thesis pp72–73.
Backend: Batteries `BinomialHeap/Basic.lean` and `Lemmas.lean`.]

### Cost obligations and a useful coupled argument

The source claims logarithmic worst-case insert, meld, minimum, and deletion.
Measure the actual recursive functions and make cached rank reads, priority
tests, list traversal, and any chosen allocation charges explicit. These are
unit-cost model claims, not Lean allocator or arbitrary-precision arithmetic
runtime claims. A uniform natural-number bound should allow a constant term,
for example C(1+floor(log2(n+1))); empty input has nonzero possible overhead
although log2(0+1)=0. For meld, n includes both operands.

The main proposed proof targets are:

- Insertion into ranks 0,...,k−1 makes exactly k links and yields a rank-k
  tree. Its size is 2^k−1 before insertion, including k=0. A carry projection
  can reuse existing binary-counter reasoning only after this source
  correspondence is proved.
- For the literal nested meld, count links jointly across `merge` and all
  `insTree` calls. The expected conservation equation is
  `outputForestLength + linkCount = leftForestLength + rightForestLength`.
  Each link reduces the number of pending trees by one; main merge steps
  and carry stopping cases are bounded by the input forest lengths.
  This supports a bound linear in m1+m2+1 for one whole meld, hence
  logarithmic in total element count. It is a proposed accounting proof,
  not a completed theorem. Multiplying a logarithmic recursive depth by an
  independent logarithmic `insTree` bound gives only log-squared and misses
  the needed dependency between the two recurrences.
- On a nonempty forest of m roots, the source direct minimum scan performs
  m−1 priority tests. The book baseline also builds residual-forest data
  on applicable branches; Exercise3.5 must remove that construction in the
  actual measured algorithm, not merely rename a projection of removal.
- Root deletion costs a root scan, reversal of r children, and meld of the
  resulting forests. Both m and r are bounded using total node count.
  A bound logarithmic in the number of roots alone is wrong: one rank-r
  tree has one root but r children to process on deletion.

Exercise3.6 requires erasure/reannotation laws on valid trees and operations,
not just an unannotated datatype. Top-level cached ranks must remain correct;
child ranks can be recovered from the parent's known rank while promoting
children. Avoid recomputing the size of each subtree. Batteries is relevant
here, but `HeapNode.rank` actually traverses the sibling spine. Its `toHeap`
computes that rank once and then traverses the spine again; both traversals
are O(r), so the intended logarithmic bound remains plausible. Charging every
call named `rank` as one cached read would be false. `Heap.size` also traverses
the top forest; it is not a stored constant-time size field.

For Exercise3.7, the cache-excluded representation already proposed in the
reuse inventory gives a concrete invariant: empty, or a cached occurrence e
and a valid underlying rest with contents `e :: entries rest`, where e's
priority is below every rest priority. Peek returns e; deletion returns that
exact occurrence and obtains the next cache by removing from rest. Insert
selects a cache and inserts the losing occurrence into rest; meld joins rests
and inserts the losing cache. Prove empty, singleton, cache-exhaustion,
duplicate, and tied-payload cases. The exercise does not prescribe every tie
choice for this newly completed functor; choose and state one consistently.
It need not reproduce an unwrapped heap's selected tied occurrence.

Constant peek and inherited logarithmic operations are conditional on measured
underlying primitive bounds. `ExactQueue` laws alone give no such bounds;
`exactList` is an existing counterexample to that inference. Keeping the cache
inside an arbitrary underlying heap would require an extra same-occurrence
removal guarantee, since two tied payloads need not be interchangeable.
[Book Exercises3.5–3.7 p23; thesis p72.]

## 3. Red-black statements and operational exercises

### Invariants, depth, and insertion

Use strict BST order and independent inorder contents, plus structural balance:
empty is black; no red-red edge; all root-to-empty paths have equal black
height. State the convention that black height excludes the empty sentinel,
so nil has black height zero. Including that sentinel instead changes every
path count by the same one and needs an explicit translation. Maximum depth
counts nonempty nodes, so nil has depth zero and a singleton depth one.

The two source invariants allow either root color. The public insertion
always returns a nonempty black root. Keep these distinct. For black height b,
the dependency already proves color-sensitive depth bounds:

| Root color | Maximum-depth bound | Size lower bound |
| --- | --- | --- |
| Black | depth ≤ 2b | 2^b ≤ size+1 |
| Red | depth ≤ 2b+1 | 2^(b+1) ≤ size+1 |

These imply Exercise3.8's `depth ≤ 2 * (size+1).log2` for either root color.
The shortcut `depth ≤ 2b` for all valid trees is false for a red singleton.
Also retain the source's longest/shortest path consequence: every path has
at least b nodes for a black root and at least b+1 for a red root, so the
maximum path length is at most twice the minimum under this convention.
That last path statement is a proposed connection, not an already identified
local named theorem. The comment on dependency `depthLB` incorrectly calls
it an upper bound; its definition and the actual proved statements, above,
are what may be reused. [Book p25; Batteries `RBTree/Depth.lean`.]

For insertion, prove `ins` is nonempty before interpreting the source's
nonempty pattern match. Its intermediate invariant allows a red-red
violation only at the result's root edge, with controlled black height.
Batteries `Balanced.ins` returns `RedRed (t.isRed = red) n`, and
`RedRed.setBlack` establishes the balanced final result; these are useful
proofs rather than a need to introduce a second balance framework.

Each of the four rotations needs an order/content statement quantified over
the four surrounding subtrees A,B,C,D and keys x,y,z. The preserved inorder
sequence is `entries A ++ [x] ++ entries B ++ [y] ++ entries C ++ [z] ++
entries D`. State ordered interval hypotheses and common black heights for
the fringes; derive balance and the local black-height preservation after
rotation. Use nonempty asymmetric fringes in checked instances. A three-key
example with every fringe empty cannot demonstrate that a subtree was not
lost or exchanged. [Book pp26–28, Fig3.5.]

### Observable differences from the dependency

Batteries' split balance functions implement the four relevant rotations,
but two other source differences must be handled:

- Its `ins` stores the newly supplied value on `cmp.eq`; book `ins` returns
  the existing equal subtree. With a faithful comparator on literal values,
  equality makes these values coincide. With a comparator on keys only,
  inserting a new payload with an existing key replaces the old payload in
  Batteries and retains it in the book. `Std.TransCmp` alone must not be
  mistaken for equality faithfulness. Existing `mem_insert` deliberately
  includes removal of the former comparator-equivalent representative.
- Public dependency `insert` blackens only when the old root was red. In
  particular, insertion into nil produces a red singleton, whereas the book
  produces a black singleton. `insert_setBlack` proves that blackening the
  dependency result equals blackening `ins`; a source adapter can use that
  connection, subject to the equality and balancing correspondence above.

Duplicate insertion into a valid black-rooted source tree preserves its tree
value. For a valid red-rooted input, even a duplicate is finally blackened,
so the blanket statement `insert x t = t` whenever x is present is false.
Pure value equality also does not establish zero allocation: the printed
routine can rebuild ancestors and its final root. Chapter2's abort-on-found
zero-allocation variant is not automatically this algorithm.

The dependency's `WF` has insert/erase closure constructors. Use its proved
`WF.out`/`WF_iff` to recover order and balance; do not cite those constructors
alone as the missing invariant argument. Its deletion helper `isBlack`
treats nil specially as red, whereas `isRed` and `Balanced.nil` use the normal
empty-black convention. The helper's name is not a suitable definition for
the source invariant. No red-black deletion algorithm is required by these
Chapter3 exercises. [Book Fig3.6; Batteries `Basic.lean`, `WF.lean`,
`Lemmas.lean`.]

### Search and cost

An erasure to the existing node-valued `BinaryTree` should preserve contents,
strict order, and depth. Then source membership can reuse
`OrderedTree.member_correct` and the actual two-`<`-test bound
`memberRun_bound ≤ 2 * height`. Combined with the red-black depth theorem,
this yields at most `4 * (size+1).log2` element `<` tests. Empty inspection,
color reads, and constructor work are not included in that existing measure;
a total-work bound requires its declared additional charges.

Insertion follows one search path and performs bounded local balancing and
root recoloring work per visited node, so a measured recurrence should give
a constant times depth plus a constant. A single dependency three-way `cmp`
call and the book's one-or-two `<` tests are different cost observations;
semantic equality does not identify their exact counts. The source's general
logarithmic-operation claim is worst-case, not an amortized sequence result.
[Book pp24–28.]

### Exercises3.9 and 3.10

**Linear sorted construction.** The target for `fromOrdList` is a valid
red-black tree with inorder enumeration exactly the input sorted, duplicate-free
list, size equal to its length, and actual work bounded by C(n+1). A promising
proof form is a size-directed list consumer returning a tree and unconsumed
suffix, with a consumed-prefix theorem and a color/black-height invariant.
One initial length traversal is compatible with linear time; repeated
sublist lengths, `take`/`drop`, or list indexing need their own accounting and
can yield O(n log n). Repeated insertion and the dependency's `ofList` fold
do not prove this exercise. A concrete coloring/construction algorithm still
has to be chosen and proved; no proposed nearly-complete-tree recipe is
accepted by this note. Required cases include 0,1,2,3 and lengths around
2^k−1, 2^k, 2^k+1. The source precondition is sorted with no duplicates, so
support for duplicate inputs is not an unstated requirement. [Book p28.]

**Split balance.** Exercise3.10a requires both value correspondence and a
statement about which color tests execute. Left recursive insertion should
use only the left red-red cases, and right recursive insertion only the
right cases. The dependency's `balance1`/`balance2` are useful concrete
implementations, but a source baseline and a measured test-erasure relation
are still needed. Do not infer the optimization from equal output trees.
[Book pp28–29.]

**No tests off the path.** Exercise3.10b removes the remaining unnecessary
grandchild test. Track the actual color-read events and require their node
identities to lie on the original search path, with an explicit convention
for the newly created leaf. Directions or known colors may be carried back
from the recursive call; recoloring a node is not itself reading its color.
Rotation changes positions, so membership in the *current* positional path
is not automatically membership in the original search path. Prove event
erasure to the insertion result, validity/content, and the logarithmic work
bound. A theorem that the optimized output is equal to baseline insertion
does not establish the no-off-path requirement. [Book p29.]

## 4. Existing interfaces and proofs to reuse

Code was inspected at conaled HEAD
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`, Batteries
`66e469188fe07963e5cf666c7d4433f45b8131c5`, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
AGENTS, domain/architectural-quality guidance, GLOSSARY, and ADRs0001,0002,0010
were read. No pinned-environment command or compiler was run for this note.

| Existing location | Reusable declarations or contract | Remaining connection |
| --- | --- | --- |
| `Applications/Search/ExactPriority.lean` | `PriorityInterface.ExactLaws`, `ExactQueue`, `exactLeftist`, `exactList`, `ExactQueue.keyed` | Exact occurrences and minimum removal already exist. Source separate peek/meld/failure and resource capabilities need checked adapters, not an unrelated heap hierarchy. |
| `Applications/Search/AbstractSet.lean` | `Ops`, `Laws`, `representation`, `Laws.insertSquare`, insertion-word fusion and membership | Colored sets should realize this same set observation under explicit comparator faithfulness. |
| `Applications/Search/OrderedTree/Basic.lean` | `Contains`, `entries`, `OrderedBy`, `member_correct`, `memberRun_bound` | Colored erasure preserves the independent order/content/height observations; existing comparisons count only element `<` tests. |
| Batteries `Data/BinomialHeap/{Basic,Lemmas}.lean` | `HeapNode`, `Heap`; `WF.merge`, `WF.deleteMin`, `HeapNode.WF.toHeap`, `rank_eq`, `realSize_eq`, `size_eq`, `realSize_merge`, `realSize_deleteMin`, `findMin_val`, `deleteMin_fst` | Useful unannotated carrier and structural proofs. Still need occurrence permutations, global minimum, binary-bit/forest-count and actual-cost proofs, plus the source relation that respects the tied-meld counterexample. |
| Batteries `Recycling/RBTree/{Basic,WF,Depth,Lemmas}.lean` | `Ordered`, `Balanced`, `RedRed`; order/balance insertion lemmas; `balance1_toList`, `balance2_toList`, `setBlack_toList`; `Balanced.depth_bound`, `WF.depth_bound` | Source baseline, equality/root-color adapter, full fringe cases, linear builder and measured color-test variants. Use these modules directly rather than deprecated forwarding imports. |
| `Applications/Resources/{Measured,Growth,BinaryCounter}.lean` | `Measured`, `bind`, `bind_erases`, `reweight_bound`, `erasureSquare`, `isBigO_of_nat_bound`; existing carry reasoning | Instrument the selected source recurrences and prove their erasure and arithmetic projection before transporting costs. A semantic adapter alone transports no running-time bound. |
| `Applications/Search/SharedTree/{Basic,Observation}.lean` | Immutable store, fresh allocation, `Represents.mono`, `allocate_extends`, `allocate_retains`, observation squares | Old-version observations can be retained under extensions. Any new rotation/link allocation or fringe-sharing claim needs its actual root-address relation; unrotated `Path.Rebuilds` does not cover rotations automatically. |

The binomial dependency's `HeapNode` is a child/sibling *forest* encoding:
its rank-r internal node structure has 2^r−1 occurrences, while the separate
top root makes a source tree of size 2^r. Reusing its size lemma as if
`HeapNode` were already the complete source tree would be off by one.

For persistence, distinguish pure retained values from a measured graph
claim. Four fringe values preserved by a rotation do not by themselves prove
that the resulting implementation retained their original cell addresses.
Use a common extending store for meld operands and prove actual root/fringe
correspondence before claiming allocation counts or physical sharing. This
is a source-model obligation, not a claim about Lean's runtime allocator.

## 5. Meaningful cases for later checked specializations

Each future case should instantiate a public general contract, rather than
prove an isolated reformulation of its expected output.

| Family | Cases and the issue they expose |
| --- | --- |
| Heap interface | Empty failure, singleton exhaustion, identical duplicate occurrences, distinct payloads with tied priorities; count occurrences across insertion, meld and deletion. |
| Binomial shape | Ranks0–3; size21/ranks0,2,4; reject unequal-rank `link` and incoming-rank-too-large `insTree` hypotheses rather than proving a false unrestricted lemma. |
| Binomial carry/cost | Sizes2^k−1 and a rank gap that stops immediately; mixed forest ranks; one high-rank tree whose deletion reverses many children despite forest length one. |
| Tied selection | Earlier tied roots with different descendants; rank[1] versus rank[0] to refute global left-heap bias; rank[0,1] versus rank[0] to expose backend/source meld difference. |
| Unannotated realization | Erase/reannotate rank0 and nontrivial descending children; exact reversal order; comparison/contents correspondence without falsely treating derived ranks as caches. |
| Explicit minimum | Empty with nonempty meld, both nonempty, insertion below/above/tied with cache, singleton deletion, refill from repeated and tied payloads, underlying cache-excluded contents. |
| Red-black rotations | LL, LR, RL, RR, each with nonempty ordered fringes and a checked black-height instance. |
| Root/equality behavior | Empty insertion; old red versus black root; duplicate insertion; equal keys with different payloads as a comparator-faithfulness counterexample. |
| Search and depth | Empty, black singleton, red singleton, missing values on both sides, and a balanced alternating-color path; connect actual comparison counts to size. |
| Sorted builder | Empty and small lengths, then boundaries around powers of two; exact inorder input and linear work, not just set membership. |
| Color-test variants | Both descent directions and all four rotation orientations; explicit trace that would detect the off-path sibling/grandchild reads. |
| Persistence | Retain an old version while rotating or melding into a new one; any claimed fringe sharing checked through actual addresses. |

This record identifies feasible proof routes and concrete false equivalences.
It neither starts Chapter3 implementation nor advances its source-coverage,
review, or acceptance status.
