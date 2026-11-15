# Chapter 14: Priority Queues — source obligations and reuse

Prepared 2026-11-02. Local chapter handle: `FDSA-014`.

**State: queued; source preparation only.** This inventory covers printed
pp. 179–182 of the pinned July 27, 2026 book, including Figures 14.1–14.2
and Exercises 14.1–14.4. It does not activate the chapter, change Lean or
acceptance state, run a build, or initiate another review loop.

## Source evidence and pins

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 14 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. PDF pages 185–188. |
| Isabelle revision | <https://github.com/isabelle-prover/mirror-isabelle> at `f86f290225eebcc52c1ae7dba2e098f405f51c21`. This shared support revision postdates the manuscript and is not asserted to be its build revision. |
| `Priority_Queue_Specs.thy` | `src/HOL/Data_Structures/Priority_Queue_Specs.thy`, 1,654 bytes; SHA-256 `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a`. Book link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Priority_Queue_Specs.html>. Authors Tobias Nipkow and Peter Lammich. |
| `Heaps.thy` | `src/HOL/Data_Structures/Heaps.thy`, 2,946 bytes; SHA-256 `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe`. Section link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Heaps.html>. Author Tobias Nipkow. |
| `Tree_Multiset.thy` | `src/HOL/Library/Tree_Multiset.thy`, 1,735 bytes; SHA-256 `90524399a3894d8646c21377429a096345a0ddede243d966f8dd141853228508`. Supplies the multiset observation and its set/cardinality/traversal bridges. |
| `Tree.thy` | `src/HOL/Library/Tree.thy`, SHA-256 `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`; shared Chapter 4 carrier, inorder and heap predicate. |
| License | BSD-3-Clause at the same Isabelle revision; `ISABELLE-COPYRIGHT` SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Preserve relevant notices for later translated source. |
| Lean reuse | conaled inspected baseline `1aabd512284fe86254278ac631eda061d311050b`, relevant pre-existing APIs from checkout `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. |

Pinned raw Isabelle URLs are
`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/`
followed by the revision, `/`, and the path above. Both directly linked
theories and the multiset support file were read. The directly linked files
have no `sorry`, `oops`, `axiomatization` or `admit` token in the scoped scan;
no Isabelle rebuild was performed. `Heaps.thy` proves abstract heap-to-queue
interpretations; it does not supply the chapter's four exercise solutions or
the displayed naive merge implementation. Reading copies are research inputs,
not manuscript deliverables.

## Domain interpretation and existing contracts

Write `E` for an empty tree, `N l a r` for a labelled node, `M(t)` for its
multiset of labels, `S(t)` for its element set, `n(t)` for internal-node count,
and `ell(t)=n(t)+1` for empty-leaf count. These follow Chapter 4; in Lean the
reused `BinaryTree.node` constructor takes its label first.

The source ADT observes **occurrences**, so insertion preserves duplicates and
deletion removes exactly one occurrence of a minimum. Set membership alone,
or a keyed queue that may replace another entry, does not satisfy this ADT.
The source simplifies payloads to ordered elements. Keep the existing general
item/priority separation and recover this source view by specialization.

`get_min` on an empty queue is unspecified. A total Lean operation returning
an arbitrary payload cannot serve all payload types: an empty queue still
exists when the payload type is empty. Use an optional minimum or a nonempty
domain proof, as fixed in `fdsa-control/DECISIONS.md`; do not introduce a global
`Inhabited` constraint. The abstract deletion laws only apply on nonempty
valid queues, although the displayed concrete heap deletion deliberately
maps the empty tree to itself.

| Existing interface | Exact fit and limitation |
|---|---|
| `Search.PriorityInterface.Operations`, `ExactLaws`, `ExactQueue` | Existing separation of operations, occurrence observation, validity and laws. `add_exact` proves permutation of all inserted plus old entries; `remove_spec` proves one-occurrence deletion, residual validity and minimum priority; `remove_none` characterizes empty observation. These are the appropriate shared contracts. |
| `ExactQueue.keyed` and `PriorityInterface.Queue` | The exact contract already yields the weaker keyed interface. The converse is false in general because keyed insertion permits replacement. Do not use the keyed contract as evidence for source multiset insertion. |
| `exactLeftist` | Existing realization using `LeftistQueue` with exact occurrences. For element-only source semantics specialize items to `Unit` and priorities to the source element type; observe `entries.map Prod.snd`. No payload order/equality is needed. |
| Merge interface | Neither current `Operations` nor `ExactQueue` contains merge. Supply the actual merge operation and two compatibility laws against the existing observation/invariant, as a small extension when needed. Avoid a parallel queue framework mirroring the Isabelle locale hierarchy. |
| `List.Perm.map`, `Multiset.coe_eq_coe`, `Multiset.coe_add`, `Multiset.mem_coe` | Connect the existing permutation observation to the source multiset laws. These bridges preserve repeated occurrences. `Multiset.erase_cons_head`/subtraction can express deletion when decidable equality is available; the underlying permutation decomposition needs no such extra capability. |
| `Finset.min'`, `min'_mem`, `min'_le`, `isLeast_min'` | Nonempty finite-support minimum under a linear order. They supply the `Min_mset` observation bridge, not a new queue algorithm. The selector's assumptions need not propagate into structural occurrence laws. |
| `exactList`, `listRemove` | Existing occurrence-correct queue, but it sorts at removal. It does not solve Exercise 14.1's constant-time minimum/removal requirement. |
| `List.orderedInsert`, `perm_orderedInsert`, `Pairwise.orderedInsert` | Exact sorted-list insertion for Exercise 14.1. The algorithm/permutation result needs a decidable relation; sortedness adds the relation's totality/transitivity. |
| `Applications.Sorting.mergeBy`, `mergeBy_perm`, `mergeBy_sorted` | Existing sorted-list merge and its exact occurrence/order contracts. Executable comparison uses `LE` plus `DecidableLE` on keys; sortedness adds `Std.IsLinearPreorder`. Source elements use the identity key. |
| `List.head?`, `List.tail`, explicit cons match | Constant structural access/deletion for the sorted-list realization. A direct root match is likewise needed for heap minimum access; projecting `LeftistQueue.deleteQ` evaluates a merge and is not a constant-time observation. |
| `BinaryTree α` in Mathlib `Data/Tree/Basic.lean` | Exact ordinary heap carrier; reuse node/leaf counts and `numLeaves_eq_numNodes_succ`. Reuse Chapter 4's inorder and its bridges when available, rather than another traversal API. |
| `LeftistQueue.Heap`, `All`, `all_iff`, `root_all` | Already separate heap order from cached-rank validity. An ordinary-tree representation bridge can reuse the content/minimum reasoning without inventing rankedness on plain heaps. |
| `LeftistQueue.toListQ`, `toListQ_perm`, `toListQ_sorted` | Root followed by merging sorted child lists; exact occurrence theorem and sortedness under `Heap` alone. No `Ranked` premise is needed. Ordinary-tree reuse requires a checked shape/observation bridge; a measured quadratic bound is still absent. |
| Batteries binary/binomial/pairing heaps | Different representations/algorithms. Their availability does not discharge the source's naive merge, sorted-list cost requirement, or inorder-preserving heap construction. Do not substitute them only because the word “heap” matches. |

## Figures 14.1–14.2: abstract priority-queue laws

The figure displays seven base laws. The pinned `Priority_Queue_Specs.thy`
adds `is_empty` and its law, giving eight; this source extension is recorded
explicitly rather than miscounted as a missing figure line.

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C14-001 | Ordered element type, queue carrier, `empty`, singleton `insert`, `del_min`, `get_min`, abstraction `mset`, and separate validity invariant. | Instantiate the existing exact queue interface, with singleton `add`; supply a minimum observation/domain adapter and separately named deletion view. |
| C14-002 | `Min_mset m` is the minimum of the multiset's finite support, for nonempty `m`. | `Finset.min'` support bridge or equivalent `IsLeast` specification. Multiplicity does not change the minimum, but remains significant for deletion. |
| C14-003 | `mset empty=0`. | `ExactQueue.empty_entries` plus the multiset observation bridge. |
| C14-004 | `invar empty`. | `ExactQueue.empty_valid`. |
| C14-005 | Valid `q` implies `mset(insert x q)=mset q+{x}`. | Singleton specialization of `add_exact`, using commutativity of multiset addition. Keep duplicates. |
| C14-006 | Valid `q` implies valid insertion. | `add_valid`. |
| C14-007 | Valid, nonempty `q` implies `mset(del_min q)=mset q−{get_min q}`. | `remove_spec` and the minimum/deletion adapter agreement; remove one occurrence. A separate peek and remove must agree on the selected value or at least the source element in the linear-order specialization. |
| C14-008 | Valid, nonempty `q` implies valid deletion. | `remove_spec`; empty deletion is not constrained by this abstract source law. |
| C14-009 | Valid, nonempty `q` implies `get_min q=Min_mset(mset q)`. | Membership and lower-bound components of `remove_spec` determine the least element under a linear order. Direct peek implementation needs its own agreement theorem. |
| C14-010 | Merge operation combines two queues; valid inputs imply `mset(merge q1 q2)=mset q1+mset q2`. | Existing exact contract lacks merge; prove occurrence compatibility for the supplied operation. No disjointness premise. |
| C14-011 | Valid merge inputs give a valid merged queue. | Separate invariant preservation, not a consequence of multiset equality. |
| C14-012 | Companion theory extension: `is_empty q` agrees with empty abstraction when `q` is valid. | `remove_none` supports semantic emptiness; direct structural `nullQ`/list emptiness implements it cheaply. The source figure does not include this operation. |
| C14-013 | General item/priority queues specialize to the source's element-only queues. | Existing independent payload/priority universes and `PQ Unit α` specialize without ordering the payload. Do not impose key uniqueness or stable tie selection absent from the source ADT. |

## Exercise 14.1: sorted-list mergeable queue, p. 180

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C14-014 | Construct a list representation with sortedness invariant, empty list, ordered insertion, merge of two sorted lists, head minimum and tail deletion. | Reuse `List.orderedInsert`, `Applications.Sorting.mergeBy`, `head?`, `tail`; no second list implementation. |
| C14-015 | Verify all source base and merge laws for that representation. | Existing insertion/merge permutation and sortedness theorems; pairwise-cons gives head minimality. Convert permutation to multiset equality only at the source observation boundary. |
| C14-016 | Minimum access and minimum deletion run in constant time. | One list-constructor match suffices in an explicitly stated structural-call model. No traversal or sorting belongs in either operation. `exactList` fails this requirement because `listRemove` invokes `mergeSort`. |
| C14-017 | Empty and duplicate-filled inputs are supported; deletion removes only one minimum. | Checked examples should include `[1,1,3] → [1,3]`, empty optional minimum, and merging overlapping multisets. No `Nodup` invariant. |

## 14.1 Heap interpretation and naive merge: pp. 180–181

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C14-018 | `heap E=True`; `heap(N l a r)` means both children heap-ordered and `a≤x` for every label in either child. | `Tree.heap`; translate on shared `BinaryTree`, or prove the ordinary/cached-tree predicate bridge to `LeftistQueue.Heap`. An immediate-child-only formulation requires a transitivity proof of equivalence. |
| C14-019 | `M(E)=0`; `M(N l a r)={a}+M(l)+M(r)`. | `Tree_Multiset.mset_tree`; can observe existing inorder/preorder list as a multiset and prove this recurrence. No equality/order capability is needed for the observation. |
| C14-020 | Set support of `M(t)` equals `S(t)`. | `set_mset_tree`, `mset_iff_set_tree`; avoids maintaining unrelated set and multiset abstractions. |
| C14-021 | Heap representation instantiates the ADT with invariant `heap` and observation `M`. | `Heaps.Heap` supplies the general interpretation given insertion/deletion content and validity laws. Additional balance invariants belong to later implementations, not the definition of a heap. |
| C14-022 | `empty=E`; nonempty `get_min(N l a r)=a`. | Direct match/valid-domain root observation; source empty minimum remains unspecified. |
| C14-023 | The nonempty heap root is a minimum of all stored labels. | Derive membership from C14-019 and lower-bound from C14-018; `Heaps.Heap`'s queue interpretation contains the source support proof. |
| C14-024 | Given a correct heap merge, `insert x t=merge (N E x E) t`. | `Heaps.Heap_Merge.insert`; preserve the side of the singleton argument when relating actual source implementations. |
| C14-025 | `del_min E=E`; `del_min(N l a r)=merge l r`. | `Heaps.Heap_Merge.del_min`; this concrete empty behavior is stronger than the abstract nonempty law. |
| C14-026 | Content and invariant laws for heap merge imply correctness of the displayed insertion/deletion operations, hence the mergeable queue interpretation. | `Heap_Merge` establishes `Heap` then its `PQM` sublocale; use existing exact queue laws as the Lean target instead of copying locale scaffolding. |
| C14-027 | Naive merge returns the other tree if either input is empty. For roots `a1,a2`, it keeps root/left child of the smaller root and merges along that tree's right child; ties choose the first root. | Exact p. 181 algorithm. Ordinary node construction is essential: `LeftistQueue.combineQ` uses rank-aware `fork` and can swap children, so it is a different operation. |
| C14-028 | Naive merge terminates because the sum of input node counts decreases in each recursive branch. | Same proof measure as later leftist merge, without its rank invariant. |
| C14-029 | The naive implementation can produce maximally unbalanced heaps. | A constructive family is ascending naturals inserted into the empty queue: every left child is empty and height equals node count. This is a checked-example/proof target for the qualitative claim, not an automatic logarithmic cost theorem. |

## Exercises 14.2–14.4: p. 181

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C14-030 | Exercise 14.2: naive merge preserves the sum of input occurrence multisets. | Induction on actual merge; no heap-order premise is needed for the stronger content result. Existing `combineQ_entries` is a proof pattern, not correspondence for the different algorithm. |
| C14-031 | Exercise 14.2: naive merge of heaps is a heap. | Requires transitive/total comparison as supplied by the source linear order. Prove root lower bounds using both input heap predicates and the chosen branch. |
| C14-032 | Exercise 14.2: insertion and deletion from C14-024–025 satisfy all priority-queue laws; together with C14-030–031 obtain the mergeable ADT. | Use the generic heap interpretation after proving this merge's two laws. Empty deletion, duplicate minima and tie direction deserve concrete clients. |
| C14-033 | Exercise 14.3: define heap-to-list enumeration. | Existing `toListQ` uses root followed by standard merge of recursively produced child lists; reuse after an ordinary-tree shape bridge or share the recursion narrowly. Repeated extraction is another valid solution, but is not forced by the exercise. |
| C14-034 | Exercise 14.3: enumeration has multiset `M(t)` for every input tree. | `toListQ_perm` supplies exact value reuse on the existing carrier, without heap or rankedness. Preserve this unconditional content theorem. |
| C14-035 | Exercise 14.3: `heap t` implies the enumeration is sorted. | `toListQ_sorted` requires only heap order. No leftist/Braun invariant is justified. |
| C14-036 | Exercise 14.3: prove a quadratic upper bound in `ell(t)`, allowing explicit constants. | Measure the actual chosen enumeration. For the root-plus-merge implementation, one call per enumeration invocation plus merge invocation (including empty bases) admits the proposed bound `T(t)≤(n(t)+1)^2`. This is a missing cost theorem, not provided by `toListQ_perm`. |
| C14-037 | Exercise 14.4: for every list `xs`, there exists a heap whose inorder is exactly `xs`. | This is an inorder-preserving Cartesian-tree construction, not sorting the input first. Empty and repeated labels are included. No matching construction was found in the inspected current APIs. |
| C14-038 | Exercise 14.4: if `xs` has no duplicate labels, that heap is unique as a labelled ordered tree. | Linear-order antisymmetry identifies the unique minimum/root; its unique position in `xs` determines left/right inorder slices; induct on their lengths. A preorder alone is insufficient. |
| C14-039 | Exercise 14.4: define executable `heap_of xs` and prove its inorder equals `xs` and its heap invariant. | A concrete simple route is the right-spine append constructor described below. The exercise imposes no linear-time requirement on this constructor. |
| C14-040 | Distinctness in uniqueness is substantive. | Two trees `N E a (N E a E)` and `N (N E a E) a E` both have inorder `[a,a]` and are heaps. Include this boundary example instead of weakening the theorem to an unsupported unconditional uniqueness claim. |

## Concrete remaining proof plans and metric boundaries

For Exercise 14.3, a measured root-plus-merge implementation can use

```text
T(E) = 1
T(N l a r) = T(l) + T(r) + TM(list l,list r) + 1
TM(xs,ys) ≤ length xs + length ys + 1.
```

The multiset theorem gives output length equal to node count. If the child
counts are `p,q`, induction reduces the proposed square bound to

```text
(p+1)^2 + (q+1)^2 + (p+q+1) + 1 ≤ (p+q+2)^2,
```

whose difference is `2*p*q+p+q≥0`. At an empty tree the count is 1; at a
singleton it is 4. This fixes a concrete interpretation of the exercise's
allowed constants without changing its asymptotic statement. It does not
assign this cost to a compiler implementation by extensional equality.

One constructive route for Exercise 14.4 appends an element to the inorder:

```text
appendHeap x E = N E x E
appendHeap x (N l a r) =
  if a≤x then N l a (appendHeap x r) else N (N l a r) x E.
```

Prove `inorder(appendHeap x t)=inorder t ++ [x]` and heap preservation,
then fold this operation from the left over `xs`, starting with `E`.
The second branch is valid because `x<a` and the old heap root is a lower
bound for its descendants. This is a proposed exercise solution, not a new
implemented declaration. The uniqueness proof is a separate theorem about
all trees satisfying the specification, not only a deterministic function.

No false mathematical claim was found in the chapter's displayed contracts
or exercises. Material transcription hazards are the extra `is_empty` law
in the companion theory, the nonempty minimum/deletion premises, set versus
occurrence semantics, the plain-node versus rank-swapping merge, and the
existence-versus-uniqueness distinction for duplicate labels. The chapter notes'
discussion of `decrease_key` and Priority Search Trees is historical/contextual;
it does not specify another required operation in this chapter's ADT.

Place the source-compatible queue observation/merge bridge beside the existing
`Applications/Search` priority interfaces, the ordinary heap and Cartesian
tree operations beside the shared binary-tree domain, and measured enumeration
beside the existing `Applications/Resources` operations. Retain current
Huffman/search clients as examples of the general exact occurrence contract.
No broader queue hierarchy, new collection carrier or cost transport inferred
from output equality is warranted by these obligations.
