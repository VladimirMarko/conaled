# Local #1015 — VFA Binom: requirements and reuse plan

**Planning only, 2026-11-02. Implementation remains blocked until #1014 Priqueue is accepted.**
The immediate chapter sequence is Trie → Priqueue → Binom → Decide. Earlier
Perm, multiplicity, Selection, Extract, and resource results are reuse
dependencies, not permission to bypass chapter completion. This file changes
no Lean source, proof, compiler output, dependency, configuration, cache,
checkout, tracker, source inventory, or GitHub state. No chapter is accepted.
All proposed theorem names, file splits, and adapters must be reconciled with
the actually accepted predecessor APIs when implementation begins.

## 1. Source identity, full coverage, and required reading

The complete inspected chapter is VFA 2.1
[Binom](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Binom.html),
`reference/vfa/vfa/Binom.v`: **400 lines, 13,042 bytes**, SHA-256
`f73f18cac4c3a6a38a0e83d4194429eb7ab684ee68068a88025610a13d5c31ed`.
The release cover is dated `2026-08-24 10:11`; this chapter's footer is
`2026-08-24 09:43`. Those distinct timestamps are intentional. The verified
versioned archive is <https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz>,
SHA-256 `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
Preserve the MIT attribution and `../source/SOURCE-RECOVERY.md` procedure;
downloaded research copies are not checkpoint deliverables under ADR 0001.

The unchanged `../source/Binom.inventory.json` contains **44 declaration
records, 21 exercises, one module, and one pedagogical command**. Its source
statuses are 22 definitions, 20 admitted declarations, one source-proved
declaration, and one grading stub. The 21 exercises include ten optional
exercises and no advanced exercises. All are required here. In particular,
`priqueue_elems` is an empty inductive placeholder despite its lexical
“definition” status, and `binom_measurement` has no named declaration. Neither
may disappear from coverage because of those inventory classifications.

Read AGENTS, architectural/domain guidance, GLOSSARY, the applicable ADRs
0001/0002/0010 and language direction, README environment/build/audit rules,
`../REQUIREMENTS.md`, the full chapter and inventory, the priority-queue,
resource/execution, and computational-assumption notes, and the relevant
frozen Extract/Priqueue plans. Actual provider definitions and theorem types
listed below were inspected; historical reuse notes were not treated as
current API evidence. The inspected checkout is
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, with Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and Batteries
`66e469188fe07963e5cf666c7d4433f45b8131c5`. This is a planning baseline,
not an accepted Binom implementation.

Both required readings at source lines 11–19 were retrieved from their exact
primary URLs and all extracted page text was read. The normal web reader
returned HTTP 403, while a bounded direct read-only HTTP request succeeded
with HTTP 200. The bytes were processed in memory, with no PDF copy added to
the workspace or deliverables. Record these identities for future retrieval:

| Reading | Retrieved identity | Consequential context retained |
| --- | --- | --- |
| Andrew W. Appel, *Binomial Queues* (2016), <https://www.cs.princeton.edu/~appel/Binom.pdf> | 20 pages; 820,707 bytes; SHA-256 `b5e6e8f3e7115ed4e7faffc629ac18f777fd21b77ffb5b061819e276f9d78b69` | Slides 10–19 explain first-child/next-sibling trees, dense optional slots, linking, and root-spine work. The slide wording using strict heap dominance is corrected to the source's non-strict bound, which admits duplicate keys. Its logarithmic-size prose needs the slot conditions in section 8. |
| Robert Sedgewick, *Algorithms*, third edition in Java, Parts 1–4 (2002), §9.7, <https://www.cs.princeton.edu/~appel/BQ.pdf> | 11 pages, printed 406–416; 236,099 bytes; SHA-256 `300abc44d593f97ed609dab095f3b4db08c956d21d0f2f129dafbef9e3e73d69` | Definition 9.4 uses non-strict left-heap order. Pages 409, 413–414 distinguish resized arrays from fixed capacity controlled by historical maximum size. Property 9.8 motivates the insertion comparison accounting below. Imperative linking, tie choices, array resizing, and the three-occupied merge case are not substituted for VFA's actual recursions. |

These are contextual readings required by this VFA chapter. The separately
numbered Sedgewick exercises and its imperative API extensions are not extra
VFA exercise records. This plan covers the chapter's algorithms, every VFA
exercise, and the relevant resource claims; it does not claim to formalize
Sedgewick's entire section or its Java implementation.

## 2. Integration and inspected reuse

A small `Applications/Search/BinomialQueue.lean` family is the proposed home
for the source algorithms, predicates, and source-law realization. Put their
measured recursions and bounds beside existing `Applications/Resources`
modules, and connected applications in `Examples`. These paths are proposals,
not files created here. Avoid a book-specific parallel hierarchy or a second
queue/comparator framework. Keep operations, finite observations, predicates,
correctness laws, cost observations, and runtime assumptions separate.

### Shared carrier and key comparison

Reuse `BinaryTree K` and ordinary `List`; in the source specialization K is
Nat. Its constructors have precisely the needed order: `BinaryTree.node value
left right` and `BinaryTree.nil` correspond to `Node key left right` and
`Leaf`. Use current BinaryTree names rather than deprecated Tree aliases.
No new generic tree datatype, list datatype, heap class, or rank cache is
needed. Preserve malformed raw trees and their source fallback branches;
the valid subtype belongs at the public queue adapter, not inside the raw
source carrier.

Factor the actual computational branches once through an explicit executable
strict-greater Boolean, then specialize to Nat and the accepted Extract
runtime carrier. Structural equations and abstraction proofs need no order
laws. Validity and maximum bounds need a lawful total preorder and a Boolean
law equivalent to `greater x y = true ↔ ¬ x ≤ y` (the strict part in reversed
argument order). Ordinary Nat order supplies this law; the accepted signed
comparison realization supplies the corresponding key order. Use the existing
order structures and the accepted comparator seam, with no newly invented
order class. A full LinearOrder is an available specialization, not a required
premise of every structural lemma.

Exact generic deletion must preserve **chosen-occurrence provenance**. The
source maximum scan retains the first root in the maximal equivalence class;
the deletion scan removes that same literal root. A lawful total preorder
therefore suffices when that provenance is proved. A weak lemma about an
arbitrary threshold m plus inequalities alone would not identify which of two
distinct comparator-equivalent keys was removed. Do not infer their equality,
or impose antisymmetry on the full source algorithm merely to repair that
weaker helper. Nat antisymmetry and Extract's injective decoder remain useful
specialized facts, but they are not replacements for the source scan proof.

### Source PRIQUEUE and ExactQueue

Consume the **accepted #1014** source-facing operations and separate eleven
law obligations, retaining `Abs : Q → List Nat → Prop` and `Valid` separately.
The frozen #1014 plan records that seam; it is not itself an accepted API.
Binom's Abs is permutation-closed, whereas Priqueue's concrete list Abs is
identity. Those are legitimate distinct relations with the same occurrence
semantics. Do not force the list relation to accept every permutation.

Use the accepted adapter to
`Search.PriorityInterface.ExactQueue Unit (OrderDual Nat)`. For Binom its
carrier is `{q // priq q}`; closure proofs lift the unchanged operations.
Choose the explicit finite observation described in section 4, and prove
`Abs q (observe q)`. `Valid := True` on this subtype is justified. It is not
justified on the raw forest: the source's malformed smash fallback can lose
occurrences. In particular, existing `ExactLaws.add_exact` and `remove_none`
are unconditional on their carrier, while source operation laws are guarded.

Encode k as `((), OrderDual.toDual k)`. Batch add reuses the accepted #1014
adapter's fold of source insert (its current plan uses a right fold), with a
singleton batch exactly source insertion. The source line-68 demonstration
is separately a **left fold**, and its tree shape must not be identified with
a different batch order. Removal encodes the returned key without rebuilding
the residual forest. Source residual bounds plus permutation and reflexivity
yield the existing contract's bound on every original entry. Preserve all
multiplicities, including repeated maxima and zero.

`PriorityInterface.Operations` has no merge. Keep native source merge as a
separate operation with valid-input closure and the exact observation law
`observe (merge p q) ~ observe p ++ observe q`. Never implement the source
merge by enumerating and reinserting entries. A reusable client must consume
both the shared queue laws and this native merge law. A full priority search
queue that replaces same-key entries is a weaker observation and cannot
supply this source contract.

### Providers actually inspected

Paths below are relative to `conaled`; Mathlib/Batteries paths live in their
pinned package checkouts. Proposed predecessor APIs are explicitly marked.

| Provider and actual API | Reuse and boundary |
| --- | --- |
| Mathlib `Data/Tree/Basic.lean`: `BinaryTree`, `map`, `numNodes`, `height` | Exact generic carrier and independent size/height observations. Their generic height bound does not establish binomial rank/shape. Prove the source-specific rank equations. |
| Mathlib `Data/Tree/Traversable.lean` and `BinaryTree.traverse` | Existing traversal/map structure was inspected before proposing a finite contents observation. A small chapter observation using the existing recursor suffices; no new generic traversal framework is needed. |
| `Search.PriorityInterface.Operations`, `ExactLaws`, `ExactQueue`, `ExactQueue.keyed` | Existing occurrence-preserving queue interface and one-way forgetting to the weaker keyed contract. Check the unconditional insertion/None fields and original-entry bound. |
| **Accepted #1014 source relation contract and adapter, names deferred** | Supply the concrete Binom validity, witnesses, and all eleven laws. Reuse its Unit/OrderDual conversion and shared maximum-queue clients; keep native merge separate. |
| `exactList`, `listRemove`, `listRemove_none`, `listRemove_spec`; `ExactPriority.lean` | An independently lawful occurrence model, using sorting at deletion. Its correctness is useful for observations, but its algorithm and costs differ from both VFA list and Binom queues. |
| `LeftistQueue.combineQ_entries`, `combineQ_valid`, `insertQ_entries`, `deleteQ_spec`; `exactLeftist` | An existing exact native-meld implementation for common clients. Leftist rank is not binomial rank, and none of these proofs replaces carry/join/unzip. |
| Mathlib `Order/OrderDual.lean`: `toDual`, `ofDual`, `toDual_le_toDual`, dual decisions | Minimum in the supplied interface becomes maximum Nat explicitly. No arithmetic negation, bounded-key subtraction, or deprecated order swap is needed. |
| Mathlib `Multiset/Defs.lean`: `coe_eq_coe`, `coe_card` | List.Perm is exactly finite-multiset equality; list length is multiplicity-sensitive cardinality. |
| Mathlib `Multiset/Count.lean`: `coe_count`, `count_cons`, `count_cons_self`, `ext` | Exact duplicate accounting; count statements use the appropriate lawful equality instance. No Finset/membership replacement. |
| Mathlib `Multiset/AddSub.lean`: `coe_add`, `count_add`, `card_add`, `erase_cons_head`, `cons_erase` | Meld adds multiplicities; successful deletion erases one copy. These are observations, not substitute queue implementations. |
| `Relational.RelRep`, `RelSquare`, `product`, `compose`; `SquareKit/Relations.lean` | Package the proved source relation and insertion/merge preservation if consumed by a connected client. Restrict the carrier or include validity in the relation so invalid operations do not acquire unconditional laws. Do not assume every relation has a chosen decoder. |
| `Squares.Rep`, `Square`, `compose`, `Rep.after`, `vertical`; `SquareKit.ListFusion.foldl_reachable`/`foldr_reachable` | Package the independently proved multiset decode or representation-map equations and compose matching boundaries. A law in Prop erases; an arbitrary semantic value stored in Type is not automatically erased. |
| `Resources.Measured`, `bind_erases`, `erasureSquare`, `reweight_bind`, `reweight_bound` | Instrument actual source recursion and transport separate counters/tariffs. Erasure is a required value proof, not a cost or runtime-equivalence theorem. |
| `Resources.run`, `run_state`, `run_invariant`, `run_value_fusion`; `run_potential_exact`, `run_constant_charge` | Compose the actual state trajectory and potential accounting. Their unguarded step hypotheses require a valid subtype or another proved globally lawful step domain. |
| `Resources.BinaryCounter.value`, `inc`, `Canonical`, `ones`, `leadingOnes`, `flipCost_eq_leadingOnes_add_one`, `flipCost_potential` | Reuse through the proved forest-occupancy bridge. Binom link comparisons equal leadingOnes; the provider's flipCost includes the final write and is one larger. Neither count is automatically machine time. |
| Mathlib `Nat.size_le`, `lt_size`, `size_pos`, `size_le_size`; `Nat.le_log_iff_pow_le`, `le_log_of_pow_le`, `log_eq_of_pow_le_of_lt_pow` | Derive bit-length/log consequences from proved rank/size and slot conditions. Keep zero, base>1, and nonzero log premises explicit. |
| `Resources.isBigO_of_nat_bound` | Package already proved numeric bounds as ordinary real-cast Big-O; it does not supply input-size hypotheses or primitive costs. |
| `Resources.TreeFlattening.appendWithCost_exact` | A generic list-append copy-count helper, available if a contents/client proof needs it. The surrounding Bracketing leaf/fork tree is a different carrier and its flattening theorem does not implement this queue. |
| **Accepted #1011 signed comparison realization, names deferred**; core `Int64.toInt.inj`, `toInt_inj`, `lt_iff_toInt_lt`, `le_iff_toInt_le`, `decLt`, `decLe`, `toInt_ofNat_of_lt`, `toInt_ofInt_of_le` | Reuse the executable signed comparator and proved range/decoding law for the measurement variant. A finite Int64 is neither unbounded Nat nor the source's 63-bit model. |
| Core `mkStdGen`, `randNat`, `IO.setRandSeed`, `IO.rand`, `IO.monoNanosNow`; existing `scripts/benchmark-order-certificate.py` | Existing reproducible generation, elapsed-time observation, and bounded evidence pattern. Random bounds are inclusive; the clock is monotonic elapsed nanoseconds. Do not copy that harness's old worker settings or change acceptance ownership. |

### Existing Batteries binomial heap: useful evidence, different program

The pinned Batteries implementation was inspected directly, including
`Batteries.BinomialHeap.Imp.HeapNode`, `Heap`, `combine`, `Heap.merge`,
`HeapNode.toHeap`, `Heap.headD`, `Heap.findMin`, `Heap.deleteMin`, and their
WF/size lemmas. It uses a sparse forest with explicit increasing ranks;
source Binom uses dense slots including Leaf. Its sibling rank traversal and
`toHeap` accumulator also differ from VFA's CPS unzip. Its `findMin` retains
the selected node/context, and its comment explicitly handles non-antisymmetric
comparisons; that is useful guidance for the source provenance proof.

`HeapNode.WF le a n` has exactly the relevant child/sibling shape: child
recursion changes the bound to the child root, and sibling recursion retains
the old bound. Its edge condition is `∀ [Batteries.TotalBLE le], le a b`.
Without an actual TotalBLE instance that condition does not certify the
intended order. For a maximum interpretation use a proved lawful **non-strict**
comparator such as `decide (b ≤ a)`. Strict greater is not total and is not a
valid substitute instance. With the non-strict comparator, Batteries combine
chooses the first equal root while source smash chooses the second. Sparse
forest deletion/merge also has different observable shapes and recursions.

Existing `HeapNode.WF.realSize_eq` proves `realSize + 1 = 2^n`;
`Heap.WF.size_eq` identifies cached-rank size with realSize. Basic also has
`Heap.WF.merge`, `HeapNode.WF.rank_eq`, `HeapNode.WF.toHeap`,
`Heap.WF.deleteMin`, `Heap.realSize_merge`, `HeapNode.realSize_toHeap`, and
`Heap.realSize_deleteMin`. These may discharge a source lemma **only after**
a concrete tree/rank/contents bridge with its hypotheses is proved. The
current plan reuses BinaryTree directly and proves the small source-specific
predicates; it does not introduce an otherwise unused sparse conversion merely
to cite a theorem. The inspected files provide no source List.Perm contents,
maximum-occurrence, or measured-work theorem. Their logarithmic complexity
comments cannot certify dense all-Leaf scans. Do not replace the source
algorithms with the Batteries public valid-subtype API.

## 3. Exact source equations, representation, and termination

The following are mathematical acceptance descriptions, not Lean proof drafts.
Every raw fallback and pattern priority is part of source behavior. Ordinary
structural recursion suffices: carry/find/deleteAux recurse on list tails;
join recurses on both tails with the first list decreasing and delegates its
base to carry; unzip recurses on the right/sibling subtree. No fuel, opaque
termination axiom, imperative array, or hidden cleanup step is required.

### Operations at lines 30–136

- `key = Nat`, raw `tree = BinaryTree Nat`, `priqueue = List tree`, and
  `empty = []`.
- For proper outer forms `t = Node x a Leaf` and `u = Node y b Leaf`, smash
  compares **x > y**. On true it returns `Node x (Node y b a) Leaf`; on false
  it returns `Node y (Node x a b) Leaf`. Equality therefore selects the
  second root. Any other outer shapes return Leaf, even if they contain keys.
- Carry's ordered cases are: `([],Leaf) ↦ []`; `([],t≠Leaf) ↦ [t]`;
  `(Leaf::qs,t) ↦ t::qs`; `(u::qs,Leaf) ↦ u::qs` after the Leaf-head case;
  otherwise `Leaf :: carry qs (smash t u)`. Keep `smash t u` argument order.
- Insertion of x is `carry q (Node x Leaf Leaf)`, with no preliminary scan,
  trimming, rank calculation, or decoding.
- Join first uses `carry q c` when p is empty and `carry p c` when q is
  empty. When both heads exist, the complete occupancy table below applies;
  all recursive calls use the two tails at the next slot rank.
- `unzip (Node x a b) cont` recurses on **b** with the continuation
  `qs ↦ Node x a Leaf :: cont qs`; `unzip Leaf cont = cont []`.
  Thus it reverses the sibling spine into increasing slot ranks while
  retaining each left subtree. Establish the arbitrary-continuation equation
  `unzip t cont = unzip t id ++ cont []`. The generally false equation
  `cont (unzip t id)` is not an acceptable replacement.
- `heap_delete_max (Node x a Leaf) = unzip a id`; every other shape,
  including Leaf, returns []. That fallback is intentionally observable.
- `find_max' current [] = current`; it skips Leaf and updates current at an
  occupied root x exactly when **x > current**. Ties retain current.
  `find_max [] = none`; it skips Leaf and initializes from the first Node
  root, then calls `find_max'` on the remaining forest. It does not examine
  descendant keys, and zero is an ordinary key, not an emptiness sentinel.
- Deletion auxiliary skips a Leaf and prepends Leaf to its first result.
  At `Node x a Leaf`, it recurses and restores that root if **m > x**;
  otherwise it returns `(Leaf::tail, heap_delete_max (Node x a Leaf))`.
  It stops at the first root not strictly smaller than m. Empty input or an
  encountered Node with nonempty right subtree returns `([],[])`; retain
  that bogus branch and any prefix reconstruction. Correctness must rule it
  out through validity and scan provenance.
- Delete-max first calls find_max. None stays None. For Some m, obtain
  `(p',q') = delete_max_aux m q`, then return
  `some (m, join p' q' Leaf)`. Native merge is `join p q Leaf`.

| p head | q head | incoming c | emitted head | next carry |
| --- | --- | --- | --- | --- |
| Leaf | Leaf | Leaf | Leaf | Leaf |
| Leaf | Leaf | occupied | c | Leaf |
| Leaf | occupied q₀ | Leaf | q₀ | Leaf |
| Leaf | occupied q₀ | occupied | Leaf | smash c q₀ |
| occupied p₀ | Leaf | Leaf | p₀ | Leaf |
| occupied p₀ | Leaf | occupied | Leaf | smash c p₀ |
| occupied p₀ | occupied q₀ | Leaf | Leaf | smash p₀ q₀ |
| occupied p₀ | occupied q₀ | occupied | c | smash p₀ q₀ |

In particular, the last case emits the **incoming carry**, linking the two
operand heads. An alternative association can preserve contents and rank but
still change this algorithm. Preserve all eight cases and both base cases.

### Shape, rank, and left-heap order at lines 141–170

`pow2heap' 0 m Leaf` is true. At rank zero a Node is false, and at a positive
rank Leaf is false. At `n+1` a Node k l r satisfies the predicate exactly when
`k ≤ m`, `pow2heap' n k l`, and `pow2heap' n m r`. The left child is governed
by k, while the right sibling retains m. This is a perfect binary shape of
height n+1 with left-heap order and an external bound. It is stronger than
just saying every key is ≤ m, and it is different from an ordinary binary
max heap that bounds both children by k.

`pow2heap n t` requires `t = Node m a Leaf` and `pow2heap' n m a`.
It has **2^n stored keys**, with an empty outer right subtree. Its BinaryTree
height is n+1, while the inner complete tree has height n and 2^n−1 keys.
Prove these exact equations, preferably as `numNodes a + 1 = 2^n` before
using truncated subtraction. Retain non-strict bounds: equal keys are valid.
A shape/order decomposition may be proved locally if useful, without creating
a second shared heap-invariant hierarchy.

`priq' i q` means each slot j of q is Leaf or a rank-(i+j) pow2heap.
The tail advances the rank by one **even at a Leaf**. `priq = priq' 0`.
There is no nonempty-last-slot condition and no rank field stored in a tree.
Arbitrary trailing Leaf slots, including a wholly empty padded forest, are
valid. Keep the base index in carry/join lemmas; their carry has the same
rank as the first slots. The child forest returned by heap deletion begins
at rank zero, regardless of the removed tree's original position.

## 4. Complete occurrence semantics and deletion proof obligations

### Relations and concrete witnesses

Preserve the source inductive tree relation. Leaf relates to []; a Node v l r
relates to **any** b with `b ~ v :: bl ++ br`, given the two child relations.
Source permutation orientation is b to the constructed list. Complete the
forest exercise with an analogous nil/cons inductive definition: nil relates
to []; a cons t qs relates to any b with `b ~ bt ++ bq`, given tree relation
t bt and forest relation qs bq. Constructor names can be idiomatic Lean, but
these rules and their nonvacuity must be proved or definitionally present.
The empty placeholder itself is not a usable relation.

Define an explicit finite observation on the existing carrier, using its
recursor: tree contents are [] at Leaf and `v :: contents l ++ contents r`
at Node; forest contents concatenate those tree lists. These are mathematical
observations, not runtime prepasses inserted into queue operations. Prove:

- `tree_elems t xs ↔ xs ~ contents t` for every raw tree, and the analogous
  forest equivalence for every raw forest. This proves both directions,
  including every permutation witness, not merely one enumeration witness.
- Witness existence, permutation closure, and uniqueness up to permutation
  for both relations on all raw states. Retain the source validity-guarded
  wrappers for abs_perm and can_relate, even when the stronger theorem exists.
- Contents length equals the existing BinaryTree.numNodes sum. Multiset
  decoding is exactly the quotient of contents, using `Multiset.coe_eq_coe`.
  Counts and cardinalities preserve duplicates; no finite-set quotient occurs.
- `Abs q []` holds exactly when every slot is Leaf. This is independent of
  q being the literal empty list. Find-max None and delete-max None admit
  that same characterization even on raw forests; preserve the source's
  guarded equivalence as a wrapper.

Prove source preservation laws with their exact hypotheses and orders:
smash observes `bt ++ bu`; carry observes `eq ++ et`; insertion observes
`k :: al`; join observes `ce ++ pe ++ qe`; native merge supplies an Abs
witness for `pl ++ ql` and hence the source theorem for **any** output
witness al. Contents preservation for raw malformed smash is false, so the
source rank/shape assumptions remain visible. Some simpler semantic lemmas
may need only proper outer shapes, but source wrappers retain their stated
premises. Empty validity and a real empty abstraction witness rule out vacuous
realizations, while closure makes all executable client states valid.

### A useful proof boundary for all deletion exercises

The five-star exercises need the full operation chain, not an extremum-only
claim. Establish the following intermediate obligations before the final
source PRIQUEUE fields:

1. A valid pow2heap root bounds all its contents; a valid forest's roots
   therefore suffice to determine a maximum. Raw root scans need no tree
   validity to describe their selected root, but bounds on descendants do.
2. Give find_max'/find_max a literal first-maximum provenance specification.
   For a successful valid scan returning m, expose
   `q = prefix ++ Node m child Leaf :: suffix`, every occupied root in
   prefix strictly smaller than m, and every root in suffix ≤ m. The returned
   m is a real stored occurrence. Preserve tie retention, including generic
   distinct keys equivalent in a total preorder. An inequality-only spec
   cannot replace this provenance in the generic deletion proof.
3. Prove unzip's continuation equation, contents correspondence, and the
   following ranked child-forest result. Removing the root from a rank-r
   pow2heap produces r occupied slots at ranks 0,…,r−1, valid under priq' 0,
   with the root omitted exactly once, total mass 2^r−1, and all remaining
   keys ≤ the old root. The physical sibling spine runs in descending rank;
   the returned list is in ascending rank. Do not treat the left subtree
   itself as a valid top-level forest or infer a cost theorem from this value law.
4. Under the provenance in item 2, delete_max_aux returns exactly the original
   prefix, then a Leaf at the selected slot, then the untouched suffix as
   its first component; its second component is that selected tree's child
   forest. Thus the original forest and first residual have the same slot
   length and same base rank. If this helper is generalized to priq' i,
   the removed absolute rank is i+prefix.length, while the child forest
   still begins at zero. Do not give both outputs base rank i.
5. Prove validity of both outputs at their correct ranks and an occurrence
   equation: original contents permute to m cons the concatenation of both
   residual contents. The prefix conditions ensure that the auxiliary never
   drops an unrelated comparator-equivalent root or reaches its bogus branch.
6. Use join validity and contents laws at base zero to produce the exact
   successful result: valid q', `pl ~ m :: ql`, and `∀ a ∈ ql, a ≤ m` for
   every source abstraction witness. Derive membership of m in pl, a bound
   on every original key, exactly one occurrence removed, and mass(q')+1 =
   mass(q). The residual upper bound is non-strict and duplicates may remain.
7. Prove both directions of the source None equivalence. Successful deletion
   of a nonempty abstraction must have a real residual witness, supplied by
   totality plus validity; a theorem conditional on an impossible Abs is
   insufficient. Padding explains why semantic emptiness is not q=[].

Expose a complete eleven-law source realization and the exact-queue adapter.
The source's final claim of implementing PRIQUEUE at lines 381–385 becomes
true only after every admitted field and the relation exercise have been
completed. The supplied source merge_priq proof does not eliminate its
admitted join_valid dependency.

## 5. All 44 inventoried declaration records

The source status column is provenance, not an implementation status. Every
row is an acceptance obligation; no row is marked accepted by this plan.
The target description names its semantic obligation rather than inventing
public names before predecessor integration.

| Source record | Statement lines / source status | Required Lean disposition |
| --- | --- | --- |
| `Binom.BinomQueue.key@30` | 30; definition | Nat specialization of the reusable key carrier; retain the exact source type and its executable strict comparison. |
| `Binom.BinomQueue.tree@32` | 32–34; definition | Reuse BinaryTree with Node(value,left,right)/Leaf correspondence, including malformed raw values; no duplicate generic datatype. |
| `Binom.BinomQueue.priqueue@44` | 44; definition | Ordinary dense List tree; slot positions denote ranks, including holes. |
| `Binom.BinomQueue.empty@46` | 46; definition | Exactly [], with independent empty validity and abstraction laws. |
| `Binom.BinomQueue.smash@48` | 48–54; definition | Both strict-greater branches, second-root tie choice, exact child placements, and Leaf fallback; section 3. |
| `Binom.BinomQueue.carry@56` | 56–63; definition | All five ordered cases and smash t u argument order, structurally recursive on the input tail. |
| `Binom.BinomQueue.insert@65` | 65–66; definition | Exactly carry q (Node x Leaf Leaf); no normalization or sparse conversion. |
| `Binom.BinomQueue.join@80` | 80–90; definition | Both carry base cases and all eight occupancy cases, including emitting c when all three slots are occupied. |
| `Binom.BinomQueue.unzip@92` | 92–96; definition | Literal right-spine CPS recursion and arbitrary-continuation equation; retain reversed rank order. |
| `Binom.BinomQueue.heap_delete_max@98` | 98–102; definition | Unzip the left subtree with id only for Node _ _ Leaf; [] for every other outer shape. |
| `Binom.BinomQueue.find_max'@104` | 104–109; definition | Accumulator root scan with strict replacement and tie retention; bound and literal provenance lemmas. |
| `Binom.BinomQueue.find_max@111` | 111–116; definition | Skip Leaf, initialize from first Node, preserve None versus Some 0, and prove selected-root provenance. |
| `Binom.BinomQueue.delete_max_aux@118` | 118–127; definition | First qualifying root, exact prefix/slot reconstruction, children at base rank zero, and raw bogus branch. |
| `Binom.BinomQueue.delete_max@129` | 129–134; definition | Exact find → auxiliary → join chain; Some/None equations and complete source laws. |
| `Binom.BinomQueue.merge@136` | 136; definition | Native join p q Leaf; retain a separate merge operation beside ExactQueue. |
| `Binom.BinomQueue.pow2heap'@143` | 143–150; definition | All zero/successor shape cases, changed left-child bound and unchanged sibling bound; perfect shape, non-strict order, size/height consequences. |
| `Binom.BinomQueue.pow2heap@154` | 154–158; definition | Proper outer Node m child Leaf and rank-n inner predicate; exactly 2^n keys and height n+1. |
| `Binom.BinomQueue.priq'@162` | 162–166; definition | Rank-indexed dense-slot validity, incrementing rank at every slot and permitting arbitrary trailing Leaf. |
| `Binom.BinomQueue.priq@170` | 170; definition | Exact base-zero specialization of priq'; do not add normalization to its definition. |
| `Binom.BinomQueue.empty_priq@182` | 182; source_admission | Prove priq empty; constructive nonvacuity of the valid carrier. |
| `Binom.BinomQueue.smash_valid@187` | 187–188; source_admission | Two rank-n pow2heaps produce a rank-(n+1) pow2heap, with non-strict maximum order and exact tie behavior. |
| `Binom.BinomQueue.carry_valid@193` | 193–195; source_admission | For every n, valid rank-n forest and Leaf-or-rank-n carry give a valid rank-n output; keep generalized n. |
| `Binom.BinomQueue.insert_priq@200` | 200; source_admission | Every valid source forest remains valid after insertion of any Nat key; exercise name is insert_valid. |
| `Binom.BinomQueue.join_valid@207` | 207; source_admission | For every n, both input forests valid at n and Leaf-or-rank-n c imply valid join at n. |
| `Binom.BinomQueue.merge_priq@211` | 211; proved_in_source | Reuse proved join_valid at n=0 and c=Leaf; source proof is present but relies on that admitted source lemma. |
| `Binom.BinomQueue.delete_max_Some_priq@217` | 217–218; source_admission | Successful source delete on valid p yields valid q, via both auxiliary outputs and join; no skipped five-star obligation. |
| `Binom.BinomQueue.tree_elems@228` | 228–234; definition | Retain the two inductive rules, arbitrary permutation witnesses and repetitions; prove contents equivalence on all raw trees. |
| `Binom.BinomQueue.priqueue_elems@247` | 247–249; definition | Complete the empty inductive exercise with nil/cons plus permutation rules and prove totality, closure and witness uniqueness. |
| `Binom.BinomQueue.manual_grade_for_priqueue_elems@251` | 251; grading_metadata | Grading metadata only; explicitly discharged by the completed relation exercise, with no mathematical grading stub added to Lean. |
| `Binom.BinomQueue.Abs@254` | 254; definition | Alias the completed forest relation, separate from priq and from the chosen observation function. |
| `Binom.BinomQueue.tree_elems_ext@263` | 263–264; source_admission | ∀ t e1 e2, e1~e2 → tree_elems t e1 → tree_elems t e2, with no validity premise. |
| `Binom.BinomQueue.tree_perm@269` | 269–270; source_admission | Two tree witnesses for the same raw t imply e1~e2; preserve multiplicity. |
| `Binom.BinomQueue.priqueue_elems_ext@279` | 279–280; source_admission | ∀ q e1 e2, e1~e2 → forest relation q e1 → forest relation q e2, without validity. |
| `Binom.BinomQueue.abs_perm@285` | 285–286; source_admission | Source wrapper: priq p plus Abs p al and Abs p bl imply al~bl; a stronger raw theorem may supply it. |
| `Binom.BinomQueue.tree_can_relate@292` | 292; source_admission | Every raw tree has a concrete finite relation witness, including malformed trees. |
| `Binom.BinomQueue.can_relate@296` | 296; source_admission | Every valid p has an Abs witness; use the stronger raw concrete-witness theorem if available. |
| `Binom.BinomQueue.empty_relate@304` | 304; source_admission | Abs empty []; supply an actual constructor/witness, not an assumed interface field. |
| `Binom.BinomQueue.smash_elems@313` | 313–316; source_admission | Given both rank-n heaps and witnesses bt,bu, prove tree_elems (smash t u) (bt++bu). |
| `Binom.BinomQueue.carry_elems@326` | 326–331; source_admission | Given priq' n q, Leaf-or-rank-n t and witnesses eq,et, prove the carried forest relates to eq++et. |
| `Binom.BinomQueue.insert_relate@336` | 336–337; source_admission | Given priq p and Abs p al, insertion k relates to k::al; exercise name is insert_elems. |
| `Binom.BinomQueue.join_elems@342` | 342–351; source_admission | Given both rank-n forests, Leaf-or-rank-n c and witnesses pe,qe,ce, join relates to ce++pe++qe. |
| `Binom.BinomQueue.merge_relate@356` | 356–360; source_admission | For valid p,q and witnesses pl,ql,al of inputs and actual output, prove al~pl++ql; also construct the direct concatenated output witness. |
| `Binom.BinomQueue.delete_max_None_relate@366` | 366–367; source_admission | For valid p, Abs p [] iff delete_max p=None, in the source orientation; stronger raw emptiness characterization may supply it. |
| `Binom.BinomQueue.delete_max_Some_relate@372` | 372–377; source_admission | For valid p, Abs p pl, actual delete p=Some(k,q), and Abs q ql, prove pl~k::ql and every residual key≤k; preserve exactly one occurrence. |

## 6. All 21 exercises, including the unnumbered implementation work

All exercises are standard; the ten tagged optional exercises remain required
by `../REQUIREMENTS.md`. The source has no advanced exercise in this chapter.
Stars describe the source's pedagogical difficulty and do not weaken gates.

| Exercise | Source range / stars / tag | Required result |
| --- | --- | --- |
| `empty_priq` | 181–184; 1 star; required | Valid empty forest. |
| `smash_valid` | 186–190; 2 stars; required | Exact next-rank shape and heap-bound preservation. |
| `carry_valid` | 192–197; 3 stars; required | Generalized rank-indexed carry preservation. |
| `insert_valid` | 199–202; 2 stars; optional | The insert_priq theorem for the actual singleton carry. |
| `join_valid` | 204–209; 3 stars; optional | All join branches and both base cases; general rank n. |
| `delete_max_Some_priq` | 216–220; 5 stars; optional | Complete successful-deletion validity, including child-forest ranks and auxiliary fallbacks. |
| `priqueue_elems` | 236–252; 3 stars; required | A nonempty, permutation-closed inductive relation, with actual witnesses; grading stub is administrative only. |
| `tree_elems_ext` | 259–266; 2 stars; required | Permutation closure on any raw tree. |
| `tree_perm` | 268–272; 2 stars; required | Witness uniqueness up to permutation on any raw tree. |
| `priqueue_elems_ext` | 274–282; 2 stars; required | Permutation closure on any raw forest. |
| `abs_perm` | 284–289; 2 stars; required | Exact source validity-guarded wrapper and stronger raw result where useful. |
| `can_relate` | 291–299; 2 stars; required | Both tree_can_relate and can_relate, supplied by concrete contents witnesses. |
| `empty_relate` | 303–307; 1 star; required | The actual empty abstraction witness. |
| `smash_elems` | 309–318; 3 stars; required | Full concatenated multiplicity proof through both comparison branches. |
| `carry_elems` | 325–333; 4 stars; optional | Ranked carry plus concatenated witnesses, including Leaf carry. |
| `insert_elems` | 335–339; 2 stars; optional | The insert_relate theorem for one extra occurrence. |
| `join_elems` | 341–353; 4 stars; optional | Carry/input occurrence sum in the exact ce++pe++qe source orientation. |
| `merge_relate` | 355–363; 2 stars; optional | Output-witness permutation and direct output witness for native merge. |
| `delete_max_None_relate` | 365–369; 5 stars; optional | Both directions, including arbitrary all-Leaf padding. |
| `delete_max_Some_relate` | 371–379; 5 stars; optional | Actual maximum occurrence removal and residual upper bound; retain repeated maxima. |
| `binom_measurement` | 391–398; 5 stars; optional | An executed, reproducible random-input comparison between the source Binom and source Priqueue integer realizations; section 9. No named declaration exists in the inventory. |

## 7. Module, command, source prose, and language adaptation

| Source location | Required disposition |
| --- | --- |
| 3–8, opening performance claim | Prove constant modeled empty and source operation bounds in stored slot count; derive live-size or historical-size logarithms only with section 8's explicit conditions. Keep comparison tariffs and runtime observations separate. |
| 11–19, required reading | Retain both primary references and retrieved identities from section 1. Preserve the child's/sibling's distinct roles, non-strict order, and dense-versus-resized representation distinction. |
| 24–26, imports | Import accepted Lean dependencies and ordinary definitions. Strings.String serves grading metadata, not a missing mathematical dependency. No Rocq import or grading framework is required. |
| **28, the single module `BinomQueue <: PRIQUEUE`; ending 386** | Instantiate the accepted source-facing operations and all eleven proved laws, then connect ExactQueue through its valid carrier and concrete witness adapter. Module syntax is adapted to Lean namespaces/parameters and actual law records; no global axioms or module emulator. |
| 36–42, power-of-two slots | Prove rank i means exactly 2^i keys at slot i, and retain Leaf holes. A list index is a rank slot, not a compact occupied-tree index. |
| **68, the single `Eval compute` command; output 69–78** | Preserve the exact left-fold input/order and expected forest below with a kernel-checked example plus a separately labelled executable evaluation when implementing. It is not sufficient to check its multiset or just its maximum. |
| 141–170, explanatory predicates | Preserve perfect binary shape, the external bound and left-heap order, correct rank offsets, and arbitrary trailing holes. Source “depth n” means rank n for the outer power-of-two heap; BinaryTree.height is n+1. |
| 178–220, validity proofs and guidance | Prove every admitted claim, including optional deletion validity. The induction suggestion is pedagogical; a sound Lean induction with matching hypotheses is sufficient. |
| 225–254, abstraction relation explanation | Both tree and forest accept every permutation of their keys, retaining repetitions. Complete the missing forest constructors; manual_grade_for_priqueue_elems does not require a Lean algorithm. |
| 257–299, relation sanity checks | Provide totality, closure, and uniqueness; proof reuse through the contents equivalence replaces cut-and-paste proof advice without weakening statements. |
| 302–379, operation/optional proofs | Complete all occurrence preservation and maximum deletion obligations, with the original assumptions and permutation orientations. Warnings about long proofs do not reduce scope. |
| 381–386, final implementation claim | Claim a PRIQUEUE realization only once every field has a checked concrete proof and the relation is nonvacuous. Source Admitted declarations are not permitted Lean dependencies. |
| 389–398, measurement | Adapt source operations to the accepted signed Lean runtime carrier, run random-input comparisons with the source list queue, preserve raw results and conditions. Ordinary Lean compilation/execution replaces Coq-to-ML extraction as explained in accepted Extract. |
| 400, footer | Preserve chapter identity and its 09:43 timestamp separately from the release cover's 10:11 time. |

The line-68 left fold inserts `[3,1,4,1,5,9,2,3,5]` in that order from empty.
Its source output has four slots: `Node 5 Leaf Leaf`, then two Leaf slots,
then the rank-three tree
`Node 9 (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
(Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf))) Leaf`.
Check this exact shape together with rank validity, nine occurrences, and
maximum 9. This catches argument-order, tie-association, fold-direction, and
slot-orientation changes that an occurrence-only assertion would miss.

## 8. Measured work, rank accounting, and corrected complexity

All results in this section are **future checked obligations**, not measured
or proved results produced by this plan. Use the existing Resources pairs,
sequencing, workload executor, and potential laws. Each measured definition
must erase to its actual source operation, including raw fallback branches.
Counter recurrences must be justified by the program and kept distinct from
semantic traversal functions used only as observations.

### Primitive model and source counts

Keep comparison calls separate from structural events. For structural work,
state the costs of case/function entries, list cons and Node constructions,
closure construction/application in unzip, and constant pair/Option work.
A finite product of Nat counters and explicit nonnegative tariffs is enough;
no new resource algebra or execution machine is required. Constructor counts
mean syntactic construction events in this model, not physical allocation,
pointer identity, stack usage, garbage collection, or optimized native code.

Let L be the stored length of a base-zero valid forest, O its number of
occupied slots, and M=max(Lp,Lq) for binary merge. A comparison tariff may
depend on its actual two keys. Under a uniform bound C on all comparisons in
a run, reweight comparison counts by C; do not assert constant comparison
cost from a reflection theorem. The source's unary-Nat comment is a source
representation caveat, not an assertion about native Lean Nat. Any unary or
bit-cost refinement must connect the exact strict-greater implementation to
its measured comparison model; the earlier lockstep ≤ theorem is not that
bridge by itself.

| Operation / observation | Exact or bounded obligation under the declared model |
| --- | --- |
| Empty | No tree/list scan and no comparisons; a fixed entry/construction charge. Semantic emptiness tests are different from construction of []. |
| Proper smash | Exactly one key comparison and two Node construction expressions; no descendant traversal. Invalid outer shapes return Leaf without a comparison. |
| Carry with a valid non-Leaf rank-matched carry | Let r be the number of initial occupied slots before the first Leaf or end. Exactly r links/comparisons and r+1 carry invocations, including the terminal placement. It constructs r+1 list cons cells in the syntactic model and two Nodes per link. General carry, including Leaf, has bounded work in L+1; carry q Leaf has the same value as q. |
| Insert | The preceding carry with an additional singleton Node construction. Comparisons are exactly r≤L; modeled list cons count r+1 and Node count 2r+1. This is the actual source path, not a full forest scan. |
| Join / merge | At most min(Lp,Lq) paired-head steps, then one carry on the remaining suffix. Total join-plus-carry invocations ≤M+2; at most M links/comparisons and at most M+1 list cons constructions. Tree construction is two per link. Prove both base cases and all eight carry patterns; zero links does not imply zero slot work. |
| find_max and find_max' | The combined full scan makes exactly L+1 invocations including its terminal case. It compares roots only. find_max uses 0 comparisons when O=0, otherwise O−1; find_max' with an already supplied candidate uses O comparisons. No early maximum permits skipping the remaining slots. |
| unzip | If the right/sibling spine has r Nodes, there are r+1 recursive invocations, r constructed closures, r detached-root Nodes, and r list cons expressions. For the actual id continuation, count all r added continuation applications and the final id application. Arbitrary supplied continuation cost remains an explicit extra cost; its value is applied at [] in the continuation equation. |
| heap_delete_max | A valid rank-r heap produces r slots by the above sibling traversal and does no key comparisons. The malformed/Leaf fallback performs no subtree traversal. |
| delete_max_aux | With valid successful provenance and selected slot j at base zero, exactly j+1 auxiliary invocations, at most j+1 comparisons, and j+1 reconstructed first-output cons expressions. Also charge at most j+1 Node expressions for restored occupied prefix roots and the selected tree passed to heap_delete_max. The detached child forest has length j and is produced by unzip; account for its cost as well. A generalized base-i helper instead detaches rank i+j. |
| delete_max | None still pays the full find_max scan. Success combines that scan, the auxiliary prefix, a rank-j unzip with j<L, and a join whose inputs have lengths L and j. Derive comparisons ≤3L and a concrete constant multiple of L+1 for structural work under the chosen tariffs. Retain the exact phase counts rather than attaching a cost only to the final join. |

Counters for closure creation and application must follow source unzip's CPS
computation; changing it to a different reverse/append implementation requires
its own named bridge. Arbitrary continuation behavior cannot be silently
charged as constant. No physical persistence claim follows from the source
value retaining an old immutable forest. A constant-time saved-reference
observation requires a stated shared-pointer realization; mathematical
persistence itself is witnessed by reusing an unchanged earlier value in a
client.

### Exact mass and slot equations

Define occupancy(q) by mapping Leaf to false and Node to true, and let
mass(q) be the sum of the existing BinaryTree.numNodes observations. Prove
under priq' i:

- Each occupied position j contributes exactly `2^(i+j)` to mass, and each
  Leaf contributes zero. Equivalently,
  `mass(q) = 2^i * Resources.BinaryCounter.value (occupancy q)`.
- At base zero, `mass(q) < 2^q.length`; hence `Nat.size (mass q) ≤ q.length`.
  This direction alone does not bound q.length by live mass.
- At base zero, if q is empty or its final slot is occupied, occupancy satisfies
  the existing BinaryCounter.Canonical predicate and `q.length = Nat.size (mass q)`.
  Under the same base-zero premise, for nonempty q prove
  `2^(L−1) ≤ mass(q) < 2^L` and derive `L = Nat.log 2 (mass q) + 1`
  with all nonzero premises explicit.
- Valid insertion adds one to mass; valid native merge adds both masses;
  valid successful deletion removes exactly one. These follow from occurrence
  laws and do not establish any execution cost independently.

Prove the source **padding counterexample** for every L:
`replicate L Leaf` is valid, has zero mass, and find_max returns None after
L+1 counted scan invocations. Thus no bound depending only on current mass
can bound that scan for all valid representations. The elementary reachable
case `delete_max [Node k Leaf Leaf] = some (k,[Leaf])` shows that source
deletion does not preserve “empty or final occupied slot”. No implicit trim
or replacement by the sparse Batteries carrier is permitted.

For a positive source-specific historical bound, prove the following slot
length facts from the actual recurrences and valid mass laws. They are also
useful independently of asymptotics:

- Raw carry never shortens its input and increases its length by at most one.
  Raw join has length between max of its input lengths and that maximum plus
  one. Growth beyond the old maximum is accompanied by a final occupied slot.
- For valid base-zero q,
  `length(insert k q) = max (length q) (Nat.size (mass q + 1))`.
- For valid p and q,
  `length(merge p q) = max (max (length p) (length q))
  (Nat.size (mass p + mass q))`.
- Valid successful deletion preserves stored length **exactly**. Its first
  auxiliary forest has the original length L; its child forest has length
  j<L. Join cannot shorten them. Any growth to L+1 would put an occupied
  rank-L tree in a valid output whose mass is strictly below 2^L, contradicting
  the original forest mass bound and one-element deletion law.

Consequently, for any fixed H, the invariant `length q ≤ Nat.size H` is
preserved by insertion when its resulting live mass is ≤H, by merge when
both inputs satisfy the invariant and their combined mass is ≤H, and by
successful deletion. Empty satisfies it. Prove this closure and lift it to
finite actual workloads; stored persistent inputs to merge must satisfy the
same hypothesis. With padded initial states use an explicit initial slot
bound B and `max B (Nat.size H)` instead. This yields logarithmic work in a
proved **historical capacity H**, including runs that shrink back to zero.
It does not yield logarithmic work in the current mass of every state.

A further connected family can build a queue of mass 2^r from empty, then
drain it completely. The slot-length laws retain r+1 Leaf slots at the end;
subsequent empty deletions still scan them. Prove this family through actual
operations and their laws if using reachability to illustrate the obstruction.
A separately named trimming variant could have a different contract, but no
such variant is required to disguise or replace these source facts.

For normalized **input** forests, the operation bounds and exact size relation
supply the usual logarithmic live-size upper bounds, with 1+L or Nat.size
handling empty inputs. Source deletion need not return a normalized result,
so state this as an input condition, not as a closed invariant of all source
operations. For arbitrary valid forests state O(L+1) or the historical bound.
Only after these explicit inequalities use `Resources.isBigO_of_nat_bound`.

### Repeated insertion and the required-reading comparison claim

Prove a source bridge rather than relabeling binary-counter theorems. For a
valid forest, `occupancy(insert k q) = BinaryCounter.inc (occupancy q)`,
including noncanonical padded inputs. The source link/comparison count is
`BinaryCounter.leadingOnes (occupancy q)`. It is **not** the provider's
terminal-write-inclusive flipCost: prove the one-less relation through
`flipCost_eq_leadingOnes_add_one` and the actual measured source insertion.

Let Φ(q) = BinaryCounter.ones(occupancy q). Using flipCost_potential and that
bridge, establish the exact per-insertion law
`comparisons + Φ(after) = Φ(before) + 1`.
Use the actual valid-state measured step and `Resources.run_potential_exact`
to obtain, for N successive insertions,
`total comparisons + Φ(final) = Φ(initial) + N`.
From empty, N=0 costs zero; for N>0 the final mass N and occupancy value imply
Φ(final)>0, hence total comparisons **< N**. This is the conditional source
comparison result corresponding to Sedgewick Property 9.8, separately from
the chapter's per-operation worst-case bounds. Initial potential remains
visible for a nonempty initial queue. The comparable structural insertion
work is linear in N plus initial potential after its branch counts are proved.

The potential pays for one sequential trajectory. Repeating insertions from
the same retained version does not let separate branches spend its initial
credit for free. Native comparison tariffs, payload representation, physical
sharing, compilation, stack behavior, and measured elapsed time remain
separate from this finite comparison-count theorem.

## 9. The complete binom_measurement adaptation

This optional five-star exercise is mandatory for chapter completion. It
requires an **executed** bounded experiment, not just code, a prediction of
which representation wins, or an unrun benchmark plan. Reuse the accepted
Extract execution pattern and the accepted Priqueue source realization.
No new benchmark framework or dependency/toolchain change is mandated.

1. Factor the source branch structure once through the supplied comparison
   operation. Deliver a source Nat specialization plus a native signed
   `Int64` specialization using the accepted Extract law/decoder. Retain the
   exact carry/join/tie/aux behavior and a proved structural map/operation
   bridge; do not substitute Batteries, leftist, sorted-list removal, or a
   hand-written unverified “fast” benchmark implementation.
2. State that Int64 is a **64-bit Lean runtime realization** with decoded range
   `−2^63 ≤ x < 2^63`, distinct from Extract's explicitly modelled signed
   BitVec63 range. For the Nat-correspondence workload generate keys in
   `0 ≤ k < 2^63`, check conversions, and use `Int64.toInt_ofNat_of_lt`.
   General signed examples can additionally exercise negative/zero/positive
   and both endpoints through the accepted Int realization. No arithmetic
   overflow law is needed for queue keys, which are only compared; generation,
   conversion, counters, and checksums must not silently rely on unproved
   wrapping-to-unbounded arithmetic. Never use unsigned comparisons as the
   signed order or claim that finite words represent every Nat/Int.
3. Provide an ordinary Lean executable/client with a standalone main, explicit
   seed/size/range/scenario options, nonzero failure on incorrect output, and
   reproducible Nix/direnv build/run commands. Follow the accepted Extract
   direct-run and compiled-executable pattern. Record which modes actually
   ran; do not call an uninspected runner “interpreted” or invent a compiler
   correctness claim from successful execution.
4. Generate one explicit seeded workload and feed **identical keys and
   operation schedules** to source Binom and source Priqueue. Use the existing
   mkStdGen/randNat or explicitly seeded serialized IO generator. randNat's
   bounds are inclusive: for a desired [0,R) range use [0,R−1] only when R>0;
   handle zero-length/range configurations explicitly. Retain the generated
   workload or its seed, generator/version, size, range, and digest. This is
   deterministic reproduction, not a formal proof of a uniform distribution
   or of agreement with the OCaml generator.
5. Include randomized insert-and-drain runs and randomized mixed operations,
   with a native merge scenario because merge is a chapter operation. Preserve
   duplicate-rich inputs and repeated maxima. Include bounded empty,
   singleton, all-equal, ascending/descending, and growth-then-drain padded
   cases to make correctness and slot behavior observable. Separate these
   deterministic checks from any random performance claim.
6. Validate the complete observed deletion sequence and remaining occurrence
   model against an independent finite list/multiset oracle. Every Some
   removes exactly one maximum occurrence, every None means no remaining
   occurrences, and every merge adds both multiplicities. Residual tree/list
   shapes may differ across implementations; compare the shared observations,
   then check source-specific examples separately. Preserve old versions in
   a bounded persistence client and confirm their observations stay unchanged.
7. Put input generation, conversion, oracle work, validation, printing, and
   optional structural instrumentation **outside** an operation-only timer.
   If a separate end-to-end time is reported, label its actual scope. Time
   corresponding build, drain, merge, or mixed phases fairly and state which
   costs each includes. Collect/report output checksums or counts so computed
   results are observed, but retain exact correctness checks rather than
   treating a checksum alone as evidence of correctness.
8. Use bounded smoke sizes and explicit resource limits for required runs.
   Record warmup policy, repetitions, execution order, elapsed timer/unit,
   host/target information where available, compiler/dependency versions,
   candidate/source hashes, complete commands, seed/workload identities,
   exits, correctness results, raw timings, and any timeout/resource failure.
   The inspected IO.monoNanosNow measures monotonic elapsed nanoseconds;
   do not label it source OCaml Sys.time process-CPU time. Serialize resource-
   sensitive runs under the coordinator's environment constraints.
9. Preserve driver source, raw evidence, inputs or reproducing recipe, and an
   interpretation of the completed observations in the local ticket and
   durability checkpoint. Report measured differences without inventing a
   speedup, extrapolating unfinished sizes, or deriving asymptotic truth from
   a finite timing curve. The proved operation-count theorems and empirical
   results are separate deliverables, and both remain required.

Mathlib/Lean logical comparison theorems justify the specialization's values;
Int64.decLt/decLe have native runtime overrides, which remain part of normal
execution trust. Proof terms in Prop may erase, but a mathematical observer
or decoder stored in Type is not erased merely because it is named Abs or
packaged in a square. Inspect the executable dependency path, so neither
contents flattening nor a proof-only decoder accidentally becomes runtime
work. No external compiler, FFI model, random timing assumption, or global
comparison axiom may enter a kernel theorem.

## 10. Connected examples, statement review, and chapter gate

Use public operations and independent expected observations; examples are
future implementation obligations, not computations performed in this plan.

| Case | Required connection |
| --- | --- |
| Exact source demonstration | The left-fold forest in section 7, its ranks, all nine occurrences, and maximum 9. |
| Rank endpoints and equal keys | Rank zero singleton; linked rank-one/rank-two examples; exact node count/height; duplicate keys remain valid. |
| Left-child versus right-sibling order | `Node 10 (Node 3 (Node 1 Leaf Leaf) (Node 8 Leaf Leaf)) Leaf` is a valid rank-two source heap although the inner root 3 is smaller than its right sibling 8. This distinguishes the intended invariant from an ordinary binary max heap. |
| Equal-root smash shape | Link `Node 5 (Node 1 Leaf Leaf) Leaf` and `Node 5 (Node 2 Leaf Leaf) Leaf`; assert the exact second-root branch and child placements, as well as the occurrence/validity laws. |
| Join occupancy | Exercise all eight occupied/Leaf/carry combinations and both empty-input bases, especially the three-occupied case that emits c. |
| Nontrivial unzip continuation | A sibling spine of length at least two with distinguishable subtree values and a nonidentity continuation; assert increasing-rank output and the general `unzip t id ++ cont []` equation. |
| Empty versus zero | Empty and arbitrary all-Leaf forests delete to None; a valid key 0 deletes to Some(0,residual). The residual of a singleton is [Leaf]. |
| Duplicate maxima and meld | Insert/meld forests with several copies of 7 and smaller keys; each delete removes one 7, with exact remaining counts and valid ranks. Use the source-law bundle and ExactQueue conversion together. |
| First maximal occurrence | A generic tagged-key total-preorder instance with distinct keys of equal priority tests the scan provenance and exact occurrence removal. Do not infer equality of equivalent tags or assert residual stability. |
| Every deletion phase | Select a maximum at the first, middle, and final occupied rank, with Leaf holes before it; verify auxiliary prefix, zero-based child ranks, join, one-element loss, and maximum bounds. |
| Malformed raw states | A Node with a nonempty right subtree triggers smash/heap-delete/aux fallbacks. Show the raw equations and why occurrence laws cannot discard their validity premises. |
| Padding and reachability | Replicate L Leaf for arbitrary L, singleton deletion padding, and a growth/drain family connected to stored-length and measured-scan theorems. |
| Insertion potential | No carry, one carry, and a long occupied prefix; check the comparison count against leadingOnes and the terminal-write difference from BinaryCounter.flipCost. Connect a finite build to the exact potential identity. |
| Shared queue client | A real build → native meld → two removals client runs through the accepted source law/ExactQueue adapter and compares its maximum/multiplicity observations with the source list queue, using separate merge laws. |
| Signed runtime adaptation | Range-checked Nat inputs, signed negative/zero/positive examples and endpoints, plus duplicate-rich executed random workloads with complete correctness evidence. |

Statement review must inspect the actual elaborated types and definitions:
constructor order, strict comparison argument direction and ties, generalized
rank/base-index hypotheses, complete shape versus left-heap order, raw versus
valid domains, exact permutation orientation, relation totality and closure,
chosen-root provenance, all-raw versus subtype ExactLaws, one-occurrence
removal, input/history size conditions, actual instrumented erasure, and
runtime conversion/measurement scope. Inspect all source admissions and the
empty inductive placeholder, not only headline theorem names. The completed
relations and concrete valid witnesses must make each interface nonvacuous.

After #1014 is accepted, use the established chapter implementation/review
loop. First inspect its final public APIs and the accepted comparison and
multiplicity seams; then integrate the shared carrier and exact raw equations,
rank/order predicates, relation witnesses and preservation laws, full deletion
proofs, source/ExactQueue adapters, measured counts and conditional resource
results, connected cases, and the executed measurement exercise. Reuse earlier
accepted proofs through actual bridges; do not duplicate generic abstractions
or introduce a second implementation under an unrelated name.

Completion requires an isolated clean committed candidate through Nix/direnv,
full integrated build and exhaustive proof audit, `./check.sh --candidate HEAD`,
independent Standards and Spec review on the same candidate, and immediate
`./check.sh --verify-candidate HEAD` before acceptance. Follow README fresh-mode
requirements when applicable and the coordinator's live build/cache ownership.
Only propext, Classical.choice, and Quot.sound are permitted audit dependencies;
no admissions, new application axioms, user-written unsafe definitions, or
native-decision proof shortcuts. A bounded executable observation is not a
kernel proof or a substitute for the integrated gate. Failed access/build/run
leaves the corresponding obligation pending.

Record exact source-to-Lean targets and theorem/measurement evidence in local
tickets only after they exist. Preserve implementation, Git history, coverage,
review findings, commands/logs, and continuation instructions in the next
coordinator-created durability checkpoint; expose/upload it immediately under
the user's standing authorization. This planning file does not mutate that
tracker, start a new implementation loop, or accept a later chapter.

## 11. Exact identities of inspected planning inputs and providers

Workspace paths begin `reference/` or `work-state/`; project paths begin
`conaled/`. Core paths below are relative to the installed pinned Lean source
root `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean`, read directly
without invoking a compiler. Reading hashes pin the inspected bytes; no API
is claimed elaborated or tested by this planning task. The two external PDF
identities are recorded separately in section 1.

| File | SHA-256 |
| --- | --- |
| `reference/vfa/vfa/Binom.v` | `f73f18cac4c3a6a38a0e83d4194429eb7ab684ee68068a88025610a13d5c31ed` |
| `reference/vfa/vfa/Priqueue.v` | `e4dc740bf2c3f338dedae3e6544a8d94d58fd80f810472610122b9ccc4866b9d` |
| `work-state/source/Binom.inventory.json` | `a353316c6502b49edd90d11b98171ecd396db60f940bfc17a77b5247bd2c1680` |
| `work-state/REQUIREMENTS.md` | `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84` |
| `work-state/source/PRIORITY-QUEUE-REUSE.md` | `1dc0ab40596354df759ca43ca0764809af9d60f222552b60ecdb05ced8ed5595` |
| `work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `work-state/source/COMPUTATIONAL-ASSUMPTIONS.md` | `eb4e8eb1cc4d04f6fe536e87622c4943d6af160b555e7ae4266979484f3eca30` |
| `work-state/source/SOURCE-COVERAGE.md` | `3e321539d04df047924788e6fb1d7a000cc4defc8e8336f1bba6536ac7698e6b` |
| `work-state/specs/1011-Extract.md` | `eccc61e739b5a3ccc0e496ad13828a93b76ec925f3bd80047b799c833a9846ff` |
| `work-state/specs/1014-Priqueue.md` | `0028ed8013db98fb62e365eb31153ab5030d027bc9a3b9d06f7e8fbb43a42c7d` |
| `conaled/Applications/Search/ExactPriority.lean` | `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879` |
| `conaled/Applications/Search/PriorityInterface.lean` | `8c1b6d6a08c8d0be52efe211affa7032d02b52e383e8bbdd4a4af82b22ee18a6` |
| `conaled/Applications/Search/LeftistQueue.lean` | `14a0d1130e04e2576dea2abb452823b5504cdbac9dbc1010f15a2f327c6bc378` |
| `conaled/Squares.lean` | `2556c4c895a747bc0092239b5dc5b220e8a6d4d6cf8a6f9fe66ab96fa2462dc7` |
| `conaled/SquareKit/Relations.lean` | `33d07aa8ea8df37a6264df39193ac3485254726c8a6859703f1e689c78ac6c03` |
| `conaled/SquareKit/ListFusion.lean` | `5ade8a9736d46b558e548aa7b1e8c60c6110f674c22deecb0038dc302b7b0164` |
| `conaled/Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `conaled/Applications/Resources/Workload.lean` | `5db2ef8f7a504b33b4dfbb26ed39de1a194fa59568ba16702f3ba2359b46b4f5` |
| `conaled/Applications/Resources/Potential.lean` | `680ea6df1c0271094a93b089a6fa2e7e8826a4da12937889ed5ecff8fc59cabe` |
| `conaled/Applications/Resources/Growth.lean` | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
| `conaled/Applications/Resources/BinaryCounter.lean` | `d990e0e8d9b09fff3f774180fa2396558f2d1abcf7e6231be648f5bd66f6f9c0` |
| `conaled/Applications/Resources/TreeFlattening/Core.lean` | `e9d7610efc7120ca846412f8b951c0c59a6cdfd840af0432222fba95cfed9ce2` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Tree/Basic.lean` | `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Tree/Traversable.lean` | `56ccdaf6c88cdb9a2228527214b591c5db15e0fe86a5c2111a361a34cd7764ac` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Multiset/Defs.lean` | `09b5004aedbde97d9fc6f3ad40510eb2d120c7485088c30cf2e2f72e81d72334` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Multiset/Count.lean` | `79d856913f87026ffc066d5aa0a73164f83cdaa5a17773af824b6d4e1368cce0` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean` | `1fd0c73c2dc4c3a2ff08e32939490e1b710e283c83cbaf73166eddc07a0f9f1e` |
| `conaled/.lake/packages/mathlib/Mathlib/Order/OrderDual.lean` | `fe55a7686c08d14e66788072bd69b9551c319b311ea3979f4c166d67808a122d` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Nat/Size.lean` | `ab4306e1e29d9b254dd41af7e206591130414598403577921c7877e9919c249b` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Nat/Log.lean` | `66bb65d1a1cabeb2ee3d8c88c55fd3cf6e48e910ea40322173d79e5ed66a0c3e` |
| `conaled/.lake/packages/batteries/Batteries/Data/BinomialHeap/Basic.lean` | `c2b986193375f5647e73c348f01fd16d5c3333007d6c938b1d3154269e539c6f` |
| `conaled/.lake/packages/batteries/Batteries/Data/BinomialHeap/Lemmas.lean` | `d6ca698684275bd4bcaf5ebf772e59c26963a025e660ab577f8fbb4f59e2b818` |
| `conaled/.lake/packages/batteries/Batteries/Classes/Order.lean` | `89aee0c4377e67c7dc6a505262837025d3bb1cb245bb13a369a60fc60689ed65` |
| `conaled/scripts/benchmark-order-certificate.py` | `faa59dc2d2e0c0e64ad44322c40ae9754577507fbf6d3c6e6b64aa5aefa8690f` |
| `conaled/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `conaled/lake-manifest.json` | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |
| Core `Init/Data/SInt/Basic.lean` | `4868b10bbef3740a4ddcaa5c8b7ccf18fd099bef301ddbc5ac8b1b8ce4e7b225` |
| Core `Init/Data/SInt/Lemmas.lean` | `7cd270efa21719a56cb69845ad59dacb1ebfa31be7b48dbfe01d25d22859cdac` |
| Core `Init/Data/Random.lean` | `10bc81cac764ae9d426e141954af5a3ba21f89acd9130b437db39e01059a6ec2` |
| Core `Init/System/IO.lean` | `409886ee25dd6ee5455dbb83269edbef98012dd22c5b6c45198b47514aeaca25` |

The map reconciles all 44 declaration IDs in source order, all 21 exercise
ranges including the no-declaration measurement task, the single module and
single Eval command, and the substantive prose/required readings. There are
40 local/core file identities in this section and two retrieved PDF identities
in section 1. Planning leaves every chapter acceptance gate open.
