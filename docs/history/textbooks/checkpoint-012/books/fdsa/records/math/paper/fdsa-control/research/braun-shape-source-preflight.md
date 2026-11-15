# Braun shape commonality — bounded source preflight

Date: 2026-11-03 UTC. Ticket: `FDSA-XT09`.

**Report-only preparation.** No implementation scope, base, worktree, API
freeze, chapter activation or acceptance is selected by this note. Chapter 1
attempt 3 remains the sole authorized gate; this task does not inspect its
outputs or control it. The initial Chapter 2 integration prefix remains
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`. All existing shared drafts remain
unaccepted, and all original chapter obligations retain their scope.

## 1. Finding and smallest useful boundary

A small **pure structural** shared component is justified by the actual
sources. Chapter 11 arrays and Chapter 16 priority queues use the same
recursive Braun predicate on the same node-labelled, empty-leaf tree carrier.
Both need its child-size decomposition and its implication to almost
completeness; the resulting logarithmic height is a common input to their
separate operation analyses. This is actual commonality, not an analogy
between unrelated balancing algorithms.

The smallest useful candidate is the exact Braun predicate and constructor
laws, label-map invariance, erased-label shape uniqueness by node count,
the almost-complete constructor arithmetic, and Braun's almost-complete and
height consequences through the saved common shape layer. The uniqueness
statement is the explicit Chapter 11 companion support C11-019; it compares
shapes, not array or priority-queue contents. It is a small structural
statement beside the common predicate, not a new representation framework.

The local **symmetric** size-balance constructor lemma is useful proof
support. Exposing a second recursive `wbalanced` predicate and its global
corollary is a separate scope choice; C11-018 stays mandatory whether it is
handled in a selected shared unit or later in Chapter 11. Neither the index
characterization nor array/heap algorithms are required merely to state or
use this structural component. No new carrier, checker, resource model,
cached-size implementation or general balancing framework is warranted.

The earlier XT02 shape scope deliberately deferred Braun and weight balance.
This report investigates that retained gap rather than treating the previous
shape draft as already proving it. A decision to author any new source still
belongs to root after all bounded preparation is assessed and the existing
freeze/checkpoint/release conditions are met.

## 2. What was read and exact provenance

The complete XT09 ticket was read first, and this report path was checked
absent. Both complete source inventories were read: Chapter 11 has 135 rows
and Chapter 16 has 48. Primary reads included all of `Braun_Tree.thy`,
`Tree_Real.thy`, and `Priority_Queue_Braun.thy`; the relevant original Chapter
11 text including all eight exercises; the complete three-page Chapter 16;
and the actual basic/flexible array operations and invariants in
`Array_Braun.thy` lines 1–239. Its fast-constructor timing declarations at
494–508 and the corresponding Appendix B tariff rows were also checked.
No whole-book re-inventory, new source retrieval or paper campaign was made.

| Retained source | Identity and precise use |
|---|---|
| Official manuscript | July 27, 2026, <https://fdsa-book.net/functional_data_structures_algorithms.pdf>; local PDF 1,742,029 bytes, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. Main passages: Chapter 11 pp.128–130, 134 and Exercises 11.1–11.8 pp.146–147; Chapter 16 pp.191–193. |
| `Braun_Tree.thy` | `src/HOL/Data_Structures/Braun_Tree.thy` at Isabelle mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`; local `book-source/Braun_Tree.thy`, 6,544 bytes/183 lines, SHA-256 `c6821391fce3c471e20d733d93cee8e7ba6d942edc87d51cf897817efac29db1`. Predicate 12–18; Unit-shape uniqueness 20–31; almost-completeness 35–40; index characterization 47–181. |
| `Tree_Real.thy` | `src/HOL/Library/Tree_Real.thy` at the same mirror pin; 4,280 bytes/114 lines, SHA-256 `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6`. Almost-complete floor/ceiling heights 29–58; one-larger constructor 61–82; symmetry and symmetric constructor 84–104; recursive symmetric balance 106–112. |
| `Tree.thy` | `src/HOL/Library/Tree.thy` at the same pin; 17,104 bytes/489 lines, SHA-256 `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`. Carrier/metrics/predicates 10–65; height optimum for independently typed trees 333–335. |
| `Array_Braun.thy` | `src/HOL/Data_Structures/Array_Braun.thy` at the same pin; 26,980 bytes/713 lines, SHA-256 `eea8db081e474392bc75e817c15c42333996f093ef4361c7fc016da388c4ed9f`. Basic operations/list observation 14–30; parity bounds 46–49; preservation and array contract 71–166; flexible operations/preservation 171–232. |
| Braun priority-queue archive | <https://isa-afp.org/release/afp-Priority_Queue_Braun-2026-10-26.tar.gz>, 10,112 bytes, SHA-256 `e6f6b1a8f08b001fd08d39adda0fb2f5ef5581e2294273bf54b03fe13497a72b`. Entry <https://isa-afp.org/entries/Priority_Queue_Braun.html> names Tobias Nipkow, September 4, 2014, BSD license. The reading-copy entry HTML has SHA-256 `3b042b6c407a78a1de96772f08269ca5aa603267c8820abd68c5100d15b8a074`. |
| `Priority_Queue_Braun.thy` | Extracted local `book-source/Priority_Queue_Braun.thy`, 10,740 bytes/292 lines, SHA-256 `2737d31cd0c32ac2d74bf46829faf6e9f740696d2c3b3f3c6cdea075a89e9f6e`. Direct power bound 22–36; operations/validity 41–227; timing declarations and bounds 232–290. |
| Pinned Lean carrier | Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Mathlib/Data/Tree/Basic.lean`, 6,679 bytes/188 lines, SHA-256 `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d`. Actual carrier/map/metrics were read; it has the required node-labelled `BinaryTree`, not a Braun invariant. |

The mirror sources can be addressed by the immutable prefix
<https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/>
and the paths above. Both this mirror pin and the dated AFP archive postdate
the July manuscript; they identify inspected formal companions, not an
asserted manuscript-generating revision. The evolving book URL alone is not
an immutable source identity. Reading copies remain under `book-source/`.

`Braun_Tree`, `Tree_Real` and `Tree` credit Tobias Nipkow. `Array_Braun`
credits Nipkow with contributions by Thomas Sewell, and the index converse
in `Braun_Tree` specifically credits Sewell. The chapter's attribution to
Braun/Rem, Hoogerwoord, Okasaki, and Nipkow/Sewell is bibliographic context,
not a request to port each cited paper. The priority-queue companion credits
Paulson's implementation based on code supplied by Okasaki; its other archive
variants are not silently selected by this task.

The applicable Isabelle BSD notice is `book-source/ISABELLE-COPYRIGHT`,
1,673 bytes, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
AFP's BSD notice is `book-source/AFP-LICENSE`, 1,842 bytes, SHA-256
`9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`,
corresponding to <https://isa-afp.org/LICENSE>. Any adaptation must preserve
the applicable full notice and attribution. The inspected Mathlib carrier
has its Apache-2.0 notice and credits Mario Carneiro and Wojciech Nawrocki.
This original report does not redistribute the whole manuscript.

## 3. The invariant, and four different meanings of balance

Use `E` for the empty tree and `N l a r` for a source node. Lean's existing
constructor is `BinaryTree.node a l r`, with the label first. Let `n(t)` be
`numNodes`, `L(t)=n(t)+1` be `numLeaves`, `h(t)` be maximum external-leaf
height and `m(t)` be minimum external-leaf height. Empty has
`n=0`, `L=1`, and `h=m=0`. These are the source/XT02 conventions, not a
leaf-labelled random-access-tree size or cached rank.

The literal source predicate is:

```
B(E) = True
B(N l a r) ↔ B(l) ∧ B(r) ∧ (n(l)=n(r) ∨ n(l)=n(r)+1).
```

The equivalent local inequalities are `n(r) ≤ n(l) ≤ n(r)+1`.
The recursive child predicates are essential; checking only the root's
two sizes is not Braun validity. Labels are never inspected.

The following conditions must stay distinct:

| Condition | Exact meaning | What it does not imply |
|---|---|---|
| Braun | The left-equal-or-one-larger size condition at **every** node. | No heap order, sorted inorder, payload equality, cached-size correctness or cost theorem follows by definition. |
| Symmetric local size balance | At one node, `abs(Int(n l)-Int(n r)) ≤ 1`, equivalently both `n l ≤ n r+1` and `n r ≤ n l+1`. | It does not require the larger child to be left, or require any condition inside the children. A single truncated Nat subtraction is not an equivalent absolute difference. |
| Recursive symmetric balance | The preceding symmetric condition at every node; source `Tree.wbalanced` at 63–65. | It implies almost completeness, but not Braun left bias or contiguous Braun indices. This is not Chapter 10's general weight-balanced-tree parameterized invariant. |
| Almost complete | `h-m≤1`, equivalently `h≤m+1` using `m≤h`: all external leaves occur on one or two adjacent levels. | No left-packing condition, sibling-size bound, Braun predicate or index contiguity is included. Height balance alone is also a different condition. |

Braun left bias is **not ordinary breadth-first left packing**. For example,
the five-node tree whose two root children are both left-only two-node trees
is Braun: the root has sizes `2/2` and each child has sizes `1/0`.
Its ordinary heap-path positions are `{1,2,3,4,6}`, whereas its source
low-bit Braun indices are `{1,2,3,4,5}`. Treating these index conventions as
identical would turn the correct shape invariant into the wrong array model.

## 4. Exact common structural claims and their original IDs

| Original obligation | Exact source claim and domain | Bounded structural use |
|---|---|---|
| C11-008; C16-001's shape component | `B E` and the exact node equivalence/inequality form. `Braun_Tree` 12–18; book pp.129 and 191. | One common predicate on the existing carrier; no payload order/equality or cache premise. |
| C11-014 | Almost-complete children with `n l=n r+1` form an almost-complete parent, for any root label. Lemma 11.1 p.129; `Tree_Real` 61–82. | Pure constructor support; it does not assume the children are Braun. |
| C11-015 | The displayed parent max/min-height formulas and the adjacent-power interval used in Lemma 11.1. | Preserve the source floor/ceiling meaning and positive empty-leaf count. Equivalent Nat log/clog formulas need their existing real-rounding bridge. |
| C11-016; later C16-042 | `B t → AlmostComplete t`, Lemma 11.2 pp.129–130; `Braun_Tree` 35–40. | Common link from the exact recursive size invariant to saved shape mathematics. Both equal and one-larger cases are required. |
| C11-017; C16-042's height input | `h t=ceil(log₂(n(t)+1))`, `m t=floor(log₂(n(t)+1))`, and minimum possible maximum height for that node count. | Reuse common almost-complete log and optimum results after the predicate bridge. Comparisons may involve different label types. No operation-time conclusion follows without its actual recurrence bound. |
| C11-018 | Symmetric recursive sibling-size balance also implies almost completeness. Book p.130, `Tree_Real` 87–112. | The local symmetric constructor is natural shared proof support. A public recursive symmetric predicate/global corollary remains a separate scope choice, not a silent waiver of the source claim. |
| C11-019 | Two Braun trees with Unit labels and equal node counts are equal. `Braun_Tree.braun_unique`, 20–31. | For arbitrary independently typed payloads, equality is of their label-erased shapes, not their raw trees or list observations. |

### Constructor arithmetic, including the smallest trees

For the one-larger case put `k=L(r)≥1`. Then `L(l)=k+1`. The exact
almost-complete height formulas and monotonicity give:

```
h(N l a r) = Nat.clog 2 (k+1) + 1
m(N l a r) = Nat.log 2 k + 1.
```

For `i=Nat.log 2 k`, positivity gives `2^i≤k<2^(i+1)`; integer succession
gives `2^i<k+1≤2^(i+1)`. Consequently `clog 2 (k+1)=i+1` and the parent
has maximum/minimum heights `i+2` and `i+1`. The strict and non-strict ends
are intentional. In particular, `r=E` gives `k=1`, a singleton left child,
and parent heights `2` and `1`, not a logarithm of zero.

For equal child sizes, their positive leaf counts, maximum heights and
minimum heights agree by the almost-complete formulas. Adding the root
preserves the existing height gap. Swapping children gives the other
one-larger case. The three cases prove the symmetric local constructor
lemma; structural induction gives both recursive implications under their
respective node hypotheses. No balancing algorithm is being executed.

The Braun consequences then use `L=n+1`. At `E`, both rounded logarithms
are zero because `L=1`. A positive-size precondition is unnecessary for
these exact equalities. Height optimum is the source statement for
`t : BinaryTree α` and `s : BinaryTree β`:
if `B t` and `n(t)≤n(s)`, then `h(t)≤h(s)`. It does not require `s` to be
Braun, or either payload type to have equality/order/inhabitation. The
equal-size case expresses the prose's minimum-height assertion. Here
“minimum possible height” concerns the maximum height `h`, not the separate
minimum external-leaf observation `m`.

### Label erasure and uniqueness

The actual Mathlib map at `Basic.lean` 79–81 changes each node label and
retains both child positions. Since node counts do not change, a Braun
predicate should satisfy `B(t.map f) ↔ B t` for **any** supplied map, including
noninjective maps and independently typed codomains. No payload comparison
or inhabitation is justified. Erasure to `Unit` is just such a map, so a
second tree carrier or a new shape quotient is unnecessary.

The source uniqueness proof uses the node-count equation and Braun child
sizes to identify the two left counts and the two right counts, then applies
induction. For a nonempty parent of size `N`, those sizes are `N/2` and
`(N-1)/2`; these are useful arithmetic facts, not a proposed constructor.
Thus two Braun trees of the same node count have equal Unit-erased shapes.
The original Unit-valued equality is retained as its direct specialization.

Two singleton trees carrying different labels already refute a stronger
raw-equality or array-observation claim. An arbitrary tree over `Empty` can
only be `E`, so all structural base statements remain meaningful without
inventing a payload default. Existence of a Braun tree of every size over
an arbitrary possibly empty payload type is **not** a consequence or a
required new theorem here; later constructors take an actual element/list.

## 5. The actual array and priority-queue clients

### Arrays: shape plus an independent size cache and index-order observation

`Array_Braun` directly imports `Braun_Tree`. Its array interpretation at
147–153 uses `(t,len)` with validity `B t ∧ len=n(t)`, while its list
observation ignores the stored cache. Braun alone says nothing about that
cache's correctness. Lookup/update use the source's one-based internal
indices, with a zero-based public wrapper.

Its list observation is literally `list E=[]` and
`list(N l a r)=a :: splice(list l,list r)` at 28–30. It is not inorder,
ordinary preorder or ordinary breadth-first order. For the complete
seven-node tree labelled by Braun indices, left child 2 has children 4/6
and right child 3 has children 5/7. The source list is `[1,2,3,4,5,6,7]`,
whereas ordinary breadth-first order is `[1,2,3,4,6,5,7]` and inorder is
`[4,2,6,1,5,3,7]`. Shape alone does not identify these observations.

The actual supporting source lemmas include parity bounds
`div2_in_bounds` (46–49), valid-index size/Braun preservation (71–84),
and high-end extension/`adds` preservation (128–142). Flexible `add_lo`
(171–173) recurses into the old right child and swaps; `merge`/`del_lo`
(175–181) have their own reconstruction. These are actual algorithm
obligations, not consequences of just defining the shape predicate.

C11-009–013 retain the positive low-bit path, the exact index-set recurrence,
raw positivity/finiteness/cardinality, and both directions of the Braun
contiguity characterization. The book's remark that the converse is not
proved in the exposition does not remove it: `Braun_Tree` 150–181 supplies
the retained companion proof. A structural unit need not implement this
set or indexing API, but must leave those rows explicitly open.

### Priority queues: the same shape plus independent heap order

`Priority_Queue_Braun` imports the identical theory at line 8. Its actual
interpretation at 206–210 is valid when `B t ∧ heap t`. The source minimum
is the root (41–45); root-as-least requires heap order and nonemptiness,
not Braun validity. The Braun tree with root 1 and a single left child 0
is not a min-heap. The same tree is a perfectly permissible raw array shape.

Heap insertion (51–54) always recurses into the old right child, swaps
children, and may replace the root according to strict `<`. `braun_insert`
and `heap_insert` are proved separately (65–69). They are not the same
payload operation as array `add_lo`, even though their shape arithmetic
is related.

The nonempty `del_left` at 77–79 recurses into the old left child but
rebuilds `N r x l'`, **swapping** the children. It is not XT08's ordinary
BST leftmost extractor, which rebuilds the residual left child on the left.
Its raw multiset/size and heap/Braun preservation statements (81–109) must
be proved for this actual recurrence. The shared shape predicate gives
usable premises, not an operation equality or an inorder-preservation claim.

The sift laws at 135–153 require Braun validity of the **assembled parent**.
Two separately Braun children do not supply the sibling-size condition.
The wildcard base cases can discard an invalid right child: for example
`sift_down E a (N E b E)` returns only the singleton `a`. Braun validity of
the intended parent forces that child empty. A second base pattern similarly
uses the size bound when the right child is empty. The actual deletion
domain bridge reconstructs `B(N r y l')` using the size decrement and both
child invariants (source proof 273–275; C16-026).

C16-015/021/023/026/027 and the shape-dependent sift bounds are concrete
later clients of these structural facts. They do not prove themselves from
the generic predicate. Source `get_min E` and `del_left E` remain
underspecified HOL calls requiring the existing optional or proof-domain
Lean policy. No `Inhabited α` should be added to the shape layer to make
those separate operations total. Heap payload order, duplicates and exact
one-occurrence deletion remain with the existing exact-occurrence queue
interface and the Chapter 14/16 obligations. Chapter 16 supplies no merge.

## 6. Height facts are not operation or checker costs

No timing declaration for `braun` occurs in the inspected Braun theory.
A logical size predicate is not an efficient executable validity checker,
and using `numNodes` in its statement does not establish a constant-time
stored size read. A shared shape result only supplies the height-to-size
step **after** an actual operation/value/count correspondence is proved.

Chapter 11 p.134 states logarithmic lookup/update and slower construction/
conversion bounds, but the inspected array theory does not generate time
functions for those basic operations. Their reconstructed recurrences and
domains remain C11-044–050 and C11-065. Later `nodes`/`brauns` do have
explicit source timing at 494–508, including the stipulated zero tariff
for exponentiation; the separate fast conversion and Exercise 11.8 models
also retain their own conventions. None is inherited merely from equal
shape or equal abstract list value.

Chapter 16 does generate the actual helper time functions:

| Source observation | Exact domain and boundary |
|---|---|
| `T_insert ≤ h+1`, source 232–236; C16-032/033; B-035 | One selected recursive insertion in the old right child; empty insertion costs 1. The raw height bound does not require Braun or heap. |
| `T_del_left ≤ h`, source 238–241; C16-034/035; B-037 | Nonempty input; base is a node with empty left child and costs 1. There is no specified empty payload-returning call. |
| `T_sift_down ≤ max(h l,h r)+1`, source 243–252; C16-036/037; B-038 | Requires the assembled parent Braun shape. The root candidate can differ from the label used to state the shape premise. Comparisons are not separately charged. |
| `T_del_min ≤ 2*h`, source 254–290; C16-039–042; B-036 | Trivial empty/empty-left branches cost 0; the nontrivial branch pays the actual extraction plus sift on its actual result, with no extra wrapper tick. |

Only after those correspondences can Braun height specialize the two main
bounds to `ceil(log₂(n+1))+1` and `2*ceil(log₂(n+1))`. These are worst-case
upper bounds in the declared source model, not matching lower bounds for
every operation, machine-time results, or costs of verifying the invariant.
The zero/trivial branches must remain, including empty `n=0`.

Two already-retained source corrections matter here: the p.134 complete-tree
node count is `2^h-1`, while `2^h` is the empty-leaf count (C11-048/135);
and p.193's final weaker `2h+1` display does not itself finish Lemma 16.1.
The companion makes the required `2*max+1≤2*h` step at 284–287, as retained
in C16-044/045. No new source defect or inventory edit is needed for either.

## 7. Independent exercise routes and nonconverses remain explicit

**Exercise 11.1 / C11-122 is not discharged by Braun→almost-complete.**
The book expressly asks for a direct inductive proof
`B t → 2^(h t) ≤ 2*n(t)+1`, followed by the rounded-log height formula,
without first establishing almost completeness. An exact primary route
already exists in `Priority_Queue_Braun.thy` 22–36: `height_size_braun`
is proved directly by induction/cases, independently of almost completeness.
It is source evidence, not a checked Lean result in this task. A future
port of that independent argument can reuse ordinary capacity/logarithm
facts; deriving the same inequality from the AC theorem would not satisfy
the requested route.

Exercises 11.2 and 11.3 separately require the left-spine equality and
the **oriented** child-height condition. These are not consequences of
symmetric balance alone: a root with only a right singleton is symmetrically
size balanced and almost complete, but its left-spine length is 1 while
its height is 2. Exercise 11.3's source hint specifically uses the
almost-complete/optimal-height facts to derive the left-equal-or-one-larger
height relation from Braun size bias. Exercise 11.4 must be connected to
the actual prefix-consuming `Balance.bal` recurrence; that constructor's
inorder observation is not automatically Braun array order.

All remaining exercises retain their original work: 11.5's bit-list lookup
and unconditional update correspondence; 11.6's auxiliary-free deletion
and unconditional equality; 11.7's **naive** initializer correctness; and
11.8's separately declared zero-base time functions and quadratic-height
bound. C11-123–132 and all operation/constructor/converter/representation
rows remain open unless separately implemented and verified. Chapter 16
has no numbered exercises, but all its algorithms, domains, correctness
and quantitative assertions remain mandatory.

Useful small structural boundaries, requiring no enumeration, are:

- `E`: Braun and almost complete, `n=0`, `L=1`, both heights/logarithms 0.
- A root with only a **right** singleton: symmetric recursive balance and
  almost completeness hold, but Braun fails; its Braun index set is
  `{1,3}`, not `{1,2}`. Symmetry does not preserve the left-biased predicate.
- A root with a complete three-node left child and a singleton right child:
  `n=5`, `h=3`, `m=2`, so it is almost complete and height optimal, but its
  sibling-size gap is 2. Almost completeness and optimal height do not
  imply either recursive size-balance condition.
- Compare that tree with the five-node Braun shape from §3. Equal counts
  and equal `h,m` do not imply equal shapes when the Braun premise is
  missing. The Braun uniqueness theorem needs both inputs valid.
- Different labels on the same singleton give identical erased shapes and
  all identical structural measurements, but different array observations.
  Noninjective label erasure preserves and reflects Braun validity;
  it does not certify payload equality or heap order.

These are mathematical boundary calculations for future connected examples,
not a new indexing implementation, compiled proof, or exhaustive test result.
The independent case report owns its selected examples and exact expectations.

## 8. Scope handoff and preserved records

The source evidence supports considering a bounded Braun structural layer
over existing `BinaryTree` and the saved tree-shape observations. The API
assessment owns actual retained-draft interfaces and any proof-economy choice.
The source boundary is exact: preserve the left-biased recursive predicate,
all empty cases, mapping across arbitrary payloads, Unit-erased uniqueness,
the required constructor assumptions and rounded logarithms. Do not infer
indexing, cache correctness, heap order, actual residual algorithms or costs
from shape alone.

The previous XT02 requirements exclude Braun/weight balance and algorithms
at lines 224–229, while explicitly retaining all original obligations.
The earlier source preflight at 201–238 records this same future predicate
bridge and the one-larger proof route. Neither record is edited here. No
claim is made that the shared drafts are integrated or accepted, and no
particular new wrapper/framework becomes mandatory through this proposal.

The complete 135 Chapter 11 rows, all eight exercises, the complete 48
Chapter 16 rows, their Appendix B costs, and all earlier chapter obligations
remain required. In particular, the index converse, full array-order
observation, cache invariant, basic/flexible operations, simple/fast/shared
constructors, both conversions, heap payload rules, partial domains and
source-specific running-time proofs remain in their owning scope.

| Control/reading input | Exact identity |
|---|---|
| `fdsa-control/tickets/FDSA-XT09.md` | 2,921 bytes/48 lines; SHA-256 `66a33e78146023b718ee7a999b10be612f6b47efb5e9ea76f6c6f83379c620a5`. |
| `research/chapter11-obligations.md` | 51,829 bytes/386 lines; SHA-256 `ec4a0763833c45d4ff3cd0a06b90cb3fd270a245b61bab2c52608066554213fc`. |
| `research/chapter16-obligations.md` | 19,617 bytes/166 lines; SHA-256 `180865d8315609bd24687b5ce0c2cbf7e75995769ac10db74e621cc693585108`. |
| `research/tree-shape-source-preflight.md` | 17,795 bytes/319 lines; SHA-256 `c7a69ed3220d94ea333af4974aabf7ed4531368b9323c12867d5d4987a6a47f8`. |
| `reviews/tree-shape-requirements.md` | 11,890 bytes/233 lines; SHA-256 `50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91`. |
| `research/appendix-b-obligations.md` | 31,759 bytes/311 lines; SHA-256 `8bf1101e774269ead99ccb23d7de237f0a208cc9a3d2d0522a4ab464ed6981e6`. |
| `book-source/chapter11.txt` | 36,093 bytes/717 lines; SHA-256 `02af7f0f1d70193fcbb6b7504aad9e1e6e6581b1414f363a2519ee30ef7b747f`. |
| `book-source/chapter16.txt` | 5,055 bytes/100 lines; SHA-256 `14744b7e7ab8f2bcb7e6f34e6f7502f256fdda3665beb1fb312a031a334aafc3`. |

In the table, bare `research/` and `reviews/` paths are under
`/workspace/scratch/845aa1048b05/fdsa-control`; source reading copies and
the existing `conaled` dependencies are under the same workspace root.
Ordinary hashes identify inspected files only. No prior record or Lean source
was edited, no worktree/ref/index/cache/active-output action was performed,
and no compiler, checker, project hash helper, remote action or new review
loop was started. This sole report is preparation for root's assessment.
