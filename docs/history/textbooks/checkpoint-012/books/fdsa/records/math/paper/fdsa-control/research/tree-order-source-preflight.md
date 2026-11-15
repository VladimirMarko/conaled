# Shared ordered-tree observations: bounded source preflight

Recorded 2026-11-02. **Source preparation only: no implementation, Lean
validation, final review, chapter activation or acceptance.** The parent-owned
Chapter 1 full gate remains the sole task-local compiler/checker. This note
does not change its candidate, the initial Chapter 2 prefix, any frozen scope,
or an earlier finding. All shared tree drafts remain unaccepted.

## 1. Scope and inspected evidence

The possible unit is the common ordered observation of the existing
node-labelled `BinaryTree`: recursive subtree order bounds, their relationship
to strict inorder order, key uniqueness, and preservation through the existing
successful root rotations. It does not implement search, insert, delete,
balancing, a Set/Map interface, or resource execution.

The exact chapter numbering is material. Chapter 4 supplies the ordinary tree,
inorder and augmentation observations. **Chapter 5 is Binary Search Trees** and
prints the strict BST definition and its inorder equivalence. **Chapter 6 is
Abstract Data Types** and specializes trees to maps with semantic key/value
pairs. The companion `HOL-Library/Tree.thy` supports both earlier chapters;
its inclusion does not move the printed Chapter 5 claims into Chapter 4.

I read the complete local Chapter 5 and Chapter 6 inventories and extracted
chapter texts, the relevant Chapter 4 tree/augmentation and sorted-input
passages and inventory rows, complete `Tree_Set.thy`, `Tree_Map.thy`,
`Tree_Rotations.thy`, `Sorted_Less.thy`, `Tree2.thy`, `Isin2.thy`, `Cmp.thy`
and `Map_Specs.thy`, the relevant definitions and ordered-tree laws of
`Tree.thy`, and the first 125 lines of `AList_Upd_Del.thy`. The latter read
includes `sorted1`, first-match `map_of`, absence bounds and the update/delete
contracts needed to interpret this preflight; the later splay-specific laws
are not reassessed here.

I also read AGENTS, architectural-quality and domain guidance, the glossary,
ADRs 0001/0010, `DECISIONS.md`, both frozen XT01/XT06 requirements and handoffs,
and all of the saved `Trees.Observations`, `Trees.Rotations` and `Trees.Cached`
source. The relevant first 100 lines of `Trees.CachedRotations` were read to
check the actual erasure and reconstruction interfaces. No new independence
or validation claim is inferred from an earlier author's report.

Primary pins remain:

- Book: July 27, 2026 edition, official PDF
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256
  `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
- Isabelle mirror: `f86f290225eebcc52c1ae7dba2e098f405f51c21`. Ordinary
  tree source is `src/HOL/Library/Tree.thy`; the named set/map/rotation and
  strict-list sources are under `src/HOL/Data_Structures/`. Exact source URLs
  use the prefix
  <https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/>.
- The companion revision is not asserted to be the revision that built the
  evolving manuscript. Its BSD-3-Clause notice must be retained for source
  adaptations under the existing provenance convention.
- Mathlib pin remains `56a005855ea17e0b0958f73ec801ae140b0a1679`. No toolchain,
  manifest, warning policy, checker or cache change is proposed.

## 2. Exact primary claims and their source locations

Line numbers below refer to the pinned local text/source files. Page numbers
are the book's printed pages.

| Claim | Primary location | Consequence for the narrow unit |
| --- | --- | --- |
| Ordinary inorder preserves the ordered sequence of node labels, including duplicates | Chapter 4 pp.48–49, `chapter04.txt` 34–36; `Tree.thy` 76–78, 392–393, 415–425 | Reuse `Trees.inorder`, its length law and arbitrary map law. No set conversion can replace the ordered observation. |
| BST means every left-subtree label is smaller than the root, every right-subtree label larger, recursively at every node | Chapter 5 p.59, `chapter05.txt` 12–18; `Tree.thy` 89–96 | A recursive invariant must express whole-subtree bounds, not only immediate child-root comparisons. The printed concrete domain is a linear order. |
| Recursive and all-node-triple descriptions of BST agree | Exercise 5.1 p.60, `chapter05.txt` 35–40; C05-017 | This remains a separate exercise unless the unit explicitly adds the node-triple observation and its proof. A new ordered predicate alone does not discharge it. |
| BST iff strictly sorted inorder; tree contents equal the set of inorder labels | Chapter 5 p.64, `chapter05.txt` 179–188; `Tree.thy` 392–393 and 447–451 | This is the principal ordered-observation bridge. The manuscript explicitly distinguishes this strict order from Chapter 2's nonstrict order. |
| Strict list order can be expressed by adjacent comparisons or by comparing each element to all later elements | Chapter 5 p.64, `chapter05.txt` 183–188; `Sorted_Less.thy` 9–23 | `List.Pairwise (<)` is a faithful mathematical observation under the order laws. The adjacent/all-pairs equivalence uses transitivity and must not be generalized to arbitrary relations without it. |
| Root/suffix and prefix/root strict bounds characterize strict sorted lists | Chapter 5 p.66, equations (5.1)–(5.4), (5.7)–(5.8), `chapter05.txt` 243–253; `Sorted_Less.thy` 25–44; `List_Ins_Del.thy` 11–17 | Standard list pairwise/append/cons laws should supply shared proof structure. The insertion/deletion distribution equations (5.5)–(5.6) remain algorithm-specific. |
| Ordinary BST search agrees with inorder membership on strictly ordered input | Chapter 5 pp.61,63,65, `chapter05.txt` 72–75, 143–151, 209–213; `Tree_Set.thy` 15–21, 68–69 | This identifies a future consumer and its valid-state boundary; a predicate/rotation unit is not a search implementation or membership-correctness proof. |
| A legal root rotation preserves inorder and reverses by the opposite rotation on the matching shape | Chapter 5 pp.67,70, `chapter05.txt` 301–310, 381–384; `Tree_Rotations.thy` 78–82 | Reuse the actual XT06 optional operation and its success theorem. Strict BST preservation then follows through the ordered-observation bridge. |
| Augmented tree order/search can ignore non-key annotations | Chapter 4 pp.56–57, `chapter04.txt` 300–323; Chapter 5 p.71, `chapter05.txt` 435–444; `Tree2.thy` 18–28; `Isin2.thy` 12–24 | A projection/pullback relation provides the key-order view. The source equality-key search does not need cache validity; interval-overlap search is different. |
| Map nodes hold full semantic key/value pairs; order applies only to keys | Chapter 6 pp.81–83, `chapter06.txt` 164–192, 217–220; `Tree_Map.thy` 11–14, 33–43; `AList_Upd_Del.thy` 9 | Retain full pair inorder and use the strict key relation. Values need no order, equality decision or default. Do not replace semantic map values with cache annotations. |
| Map lookup agrees with first-match association-list lookup under strict key order | Chapter 6 p.83, `chapter06.txt` 205–220; `AList_Upd_Del.thy` 16–18; `Tree_Map.thy` 33–35 | Strict key order yields unique key occurrences. Actual lookup and the full Map laws remain separate later work. |
| Ordered-map refinement can retain an independent extra invariant | `Map_Specs.thy` 30–53, 55–73; C06-067 | BST/key order must stay distinct from balance or cache validity. No theorem may silently discard that extra condition. |

The pinned `Tree_Set.thy` uses the unqualified name `sorted`, but its imports
reach `Sorted_Less`, which hides ordinary HOL `sorted` and abbreviates
`sorted_wrt (<)`. Reading this occurrence as nondecreasing order would change
the source contract. `Tree.thy` itself separately states the weak-order
`bst_wrt (≤)` equivalence at 442–445 and strict BST equivalence at 447–451.

## 3. Existing local operations and the actual gap

The saved XT01 candidate is `64c6b777d828ecfe83234fc2aed94600a1f24297`; the
saved XT06 candidate is `28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2`, according
to their retained handoffs. This preflight inspected the actual files under
`conaled-tree-rotations`; it did not run Git or independently certify checkout
cleanliness. Exact byte identities are retained below.

`Trees.Observations` already has the universe-polymorphic ordinary fold,
`inorder_nil`, `inorder_node`, `inorder_length` and `inorder_map`. The node
equation is `inorder l ++ a :: inorder r`; constructor order is Mathlib's
`BinaryTree.node a l r`. There is no BST or strict-key predicate in that
module. This is an intentionally absent capability, not a defect in XT01's
frozen scope.

`Trees.Rotations` already has `rotateLeft?`, `rotateRight?`, exhaustive failure
shapes, successful inverses, `inorder_of_rotateLeft?` and
`inorder_of_rotateRight?`. The latter equalities preserve all occurrences and
their order without requiring any label order. Its label-map commuting laws
also permit noninjective maps. Those operation/observation laws should remain
unchanged when a stricter ordered-state invariant is introduced.

`Trees.Cached.erase` is `BinaryTree.map Prod.fst`; its `inorder_erase` law
relates erased inorder to mapping first projections over full pair inorder.
Its `Valid` predicate concerns stored summary correctness at every node.
`CachedRotations` reconstructs two roots and separately exposes erased
inorder and recursive cache validity. Thus ordered payload preservation can
be derived through the already retained erased observation; order does not
need to be included in the cache-validity definition.

The genuinely missing narrow connection is: give a source-faithful recursive
ordered-tree predicate, establish its stated relation to existing inorder,
specialize it to strict keys, and consume the already existing rotation
equalities. A new carrier, second inorder, comparator framework, generic
execution language or preservation record is unnecessary.

## 4. Proposed logical scope and precise hypotheses

The following describes mathematics, not frozen Lean names or an implemented
API. Use one relation parameter `R : α → α → Prop` over the existing carrier.

1. A source-style recursive `bstWrt R` has value `True` at the empty tree.
   At `node a l r`, require both subtree invariants, `R x a` for every label
   occurrence in `l`, and `R a y` for every label occurrence in `r`.
   Whole-subtree membership can be expressed through a shared tree-content
   observation or existing inorder membership with an explicit source bridge.
   A separate carrier or duplicate traversal is not needed merely to name it.
2. Establish `Pairwise R (inorder t) → bstWrt R t` for an arbitrary relation.
   The all-pairs property supplies the two child invariants and both root
   bounds without any transitivity, totality, decidability or irreflexivity.
3. Establish `bstWrt R t → Pairwise R (inorder t)` under transitivity of `R`.
   At each node, the missing cross-subtree fact follows from `R x a` and
   `R a y`. Combine the directions into an iff under this explicit premise.
   A reached-cross-bound version could be weaker, but is not required merely
   to port the book's strict-order result.
4. Recover the book specialization `R x y := x < y`, then the key version
   `R x y := key x < key y`. The strict relation of a preorder is transitive
   and irreflexive; a linear order is unnecessary for these observation laws
   even though the source search algorithms later use linear comparison.
5. Through the strict inorder observation, derive `Nodup` of the key list.
   No decidable equality on payloads or keys is needed simply to state and
   prove this proposition. Payloads with the same key cannot occur at two
   distinct list positions in a valid strict-key tree. The empty and singleton
   statements remain unconditional in the relation/order.
6. A relation pullback along a label map should connect a mapped tree with
   the original tree. In particular, key order on full semantic records is
   the ordinary order on the mapped key tree. A forward relation-preservation
   hypothesis gives forward transport; reflection requires the converse.
   Arbitrary noninjective label maps do not preserve a strict BST invariant.
7. If a successful root rotation returns `t'`, use its actual inorder
   equality to derive `Pairwise R (inorder t') ↔ Pairwise R (inorder t)`
   without any law on `R`. To conclude the corresponding **recursive**
   `bstWrt R` iff, use the transitive bridge. Strict/key BST preservation is
   the source specialization. Failure remains `none`; it does not create a
   tree whose invariant could be asserted.

The source's `bst_wrt_mono` at `Tree.thy` 436–437 is a useful lightweight
relation-weakening law: a pointwise implication from `R` to `S` transports the
recursive invariant on the same tree. It does not supply reflection or
establish that the two order predicates are equivalent.

### Essential arbitrary-relation boundary

Take `R a b := b = a + 1` on naturals and the three-node tree with root 1,
left singleton 0 and right singleton 2. Both root bounds hold, so the source
recursive `bstWrt R` holds. Its inorder is `[0,1,2]`, which is not `Pairwise R`
because `R 0 2` fails. Its legal left rotation has root 2 and the former root 1
with left child 0; the new root requires `R 0 2`, so the recursive invariant
fails there too. This is a hand-derived counterexample target, not a compiled
Lean example. It refutes both proposed unqualified generalizations at once.

### Strict versus weak order and uniqueness

For a partial order, strictly ordered lists are equivalently nondecreasing
lists with no duplicate elements. The analogous key statement uses `Nodup`
of the **mapped key list**, not merely `Nodup` of full records. A mere preorder
is insufficient for the converse: distinct but order-equivalent elements can
be nondecreasing and distinct without either being strictly below the other.
Keep antisymmetry if this optional bridge is exposed. The book's linear-order
specialization satisfies it. The primary strict observation and uniqueness
results do not need this optional bridge to exist.

For a completely generic recursive relation invariant, irreflexivity alone
does not replace transitivity: equal labels in different subtrees may escape
the absent cross-subtree condition. Derive occurrence uniqueness from the
proved all-pairs observation with its actual hypotheses.

## 5. Full semantic pairs, erasure and key transport

The same product carrier can support two distinct observations:

| Use | Ordered/semantic observation | What remains separate |
| --- | --- | --- |
| Cached ordinary tree | Order the logical payloads obtained with `Prod.fst`; cache values are annotations | `Trees.Cached.Valid` and summary correctness; malformed caches may still have correctly ordered erased payloads |
| Chapter 6 map tree | Retain the full `(key,value)` inorder for map semantics; order its mapped keys | Lookup/update/delete behavior and arbitrary semantic values |
| Keyed records | Retain each full record, with strict order pulled back through a supplied key function | Any order/equality/default assumption on the remaining fields |

In Chapter 4 the prose calls lookup-table values an augmentation too, and
offers the projected inorder observation. Chapter 6 explicitly uses a full
pair inorder as the intermediate map representation. This is a change of
chosen observation, not license to erase a map's semantic values. The pinned
`Tree_Map` imports `Tree_Set` and uses the generic full-label `Tree.inorder`;
it does not import `Tree2`'s projected inorder.

A key-preserving transformation of payloads can be noninjective on unused
payload fields and still preserve strict key validity. Its premise must say
the target key equals the source key (or give the corresponding strict-order
preservation law). By contrast, mapping every key to one fixed value destroys
strict ordering on a tree with at least two nodes. Neither fact contradicts
XT06's unconditional commutation of label mapping with the rotation operation.

## 6. Lookup and absence boundaries retained for later algorithms

The printed and companion search/lookup functions are total by structural
recursion: an empty set search returns false, and an empty map lookup returns
`none`. An absent-key lookup is a normal result, not an underspecified call.
Correctness for all queries follows only under the stated ordering invariant;
the query need not already be present. A future counterexample on a malformed
tree can show why one-branch search may miss a label stored on the wrong side.
This preflight does not add that algorithm or claim its theorem.

Strict key order is sufficient for the source first-match association-list
semantics to agree with the tree search. The list observation remains defined
on duplicate-key inputs, where the first binding wins. In particular,
`[(1,10),(1,20)]` contains distinct full pairs and can be increasing in a
lexicographic full-pair order, but its key list `[1,1]` is not strictly sorted.
Deleting only the first binding leaves value 20 at key 1; it does not implement
setting that key to `none`. This is the existing Chapter 6 hypothesis boundary,
not a new replacement specification.

`split_min` at `Tree_Set.thy` 35–37 has only a nonempty-tree defining equation;
its full-label inorder-head theorem at 76–79 explicitly retains nonemptiness.
Rotations likewise have only matching-shape source equations. These operations
remain explicit valid-domain/`Option` interfaces in Lean. No global
`Inhabited` payload should be introduced to complete their missing cases.
For map values of an empty type, `none` remains a valid lookup result and
the empty map tree remains valid; no semantic payload can be invented.

## 7. Connected case targets

These are independently derived expectations for the parent to combine with
its case/API preflights. They are not a new per-declaration quota, runtime test
suite, frozen scope or claim of checked examples.

| Case | Expected mathematical observation | Intended public connection |
| --- | --- | --- |
| Empty tree with arbitrary label type, including `Empty` | Empty inorder; any relation's recursive invariant and all-pairs observation hold | Constructor and observation laws; no default label |
| Singleton at an arbitrary supplied label | Singleton inorder; invariant holds without `R a a` | Show irreflexivity is not accidentally a constructor premise |
| Printed six-label tree, p.59: root 6; left root 3 with children 2,5; right root 9 with left child 8 | Inorder `[2,3,5,6,8,9]`, strict BST and six distinct keys | Recursive/inorder equivalence and key uniqueness; the printed diagram's actual shape |
| A legal root rotation of that tree | Same complete inorder and preserved strict BST; inverse recovers the original | Existing optional success/inverse and inorder equalities followed by the new bridge |
| Root 1 with a same-key child 1 | Weakly nondecreasing inorder `[1,1]`, false strict BST and failed key uniqueness | Strict-versus-weak hypothesis boundary; supports the existing p.54 correction without implementing the balancer |
| Distinct semantic records `(1,10)` and `(1,20)` in inorder | Full-record distinctness does not supply strict key order | Actual pulled-back key predicate and mapped-key `Nodup` conclusion |
| Successor relation on root 1 with leaves 0,2 | Recursive bounds true, all-pairs false; legal left rotation loses the recursive invariant | Necessity of a relation-law hypothesis in the generalized bridge/rotation theorem |
| Arbitrary key-preserving payload transformation | Strict key observation retained, with no order/equality requirement on payload fields | Actual label-map/pullback transport; a constant payload map is allowed |
| Constant map on all ordered keys | Rotation/map commutation still holds; strict BST fails for two or more nodes | Keep operation naturality distinct from invariant preservation |
| Cached tree with ordered erased payloads and deliberately wrong annotations | Erased order still holds while cache validity may fail | Independence of key/payload order and stored-summary validity; use existing cache fixtures where suitable |

The existing XT06 fixtures with repeated label 1 are useful for unordered
rotation/cost statements, but cannot serve as positive strict-BST fixtures.
Reusing them as valid BSTs would be a semantic error. Root can retain their
existing purpose while adding the small ordered source fixture above.

## 8. Source corrections and retained coverage boundaries

Two already recorded manuscript issues directly affect this interface:

- Chapter 4 p.54 (`chapter04.txt` 228–245) says a sorted input gives a BST.
  With Chapter 2's nondecreasing convention this needs distinctness, or an
  explicitly strict input order. The existing `[1,1]` counterexample and
  corrected future balancing corollary remain required. The generic balancer
  and inorder-preservation algorithms must continue to allow duplicates.
- Chapter 6 p.82 (`chapter06.txt` 189) points map deletion to §5.6.4's
  interval-cache split-min. The companion and types show that §5.2's generic
  full-label split-min is intended. Preserve the full successor pair. This
  source correction stays in the Chapter 6 record; ordered observations do
  not implement or validate deletion.

The p.65 ill-typed insertion-calculation endpoint and the refuted/oops
rotation-schedule assertion are already preserved in the Chapter 5 inventory.
Nothing in this preflight changes those dispositions or turns an aborted
Isabelle declaration into a theorem.

Potential support is limited to C05-001/025, the BST consequence of C05-043,
the strict-key observation portions of C06-044/049, and later consumers of
the same key invariant. The existing XT01 observations continue to support
the corresponding Chapter 4 inorder/map rows. A source-ready or subsequently
accepted shared unit is not completion of any of these whole chapters.

Still separate and mandatory: Exercise 5.1's all-node characterization;
Exercise 5.3's direct recursive set/BST proofs without the inorder detour;
all set/map operations and refinement clients; search and its height/expected
costs; deletion variants and their height bounds; union/splitting;
positioned rotations, listification, inverse schedules, counts and distance;
interval order, maximum attainment, overlap search and sweep correctness;
all balancing schemes; Chapter 6 interval-list algorithms, linear-work
proofs, abstract interface composition, and both modify-interface directions.
Merely choosing an inorder-based recursive-bound expression does not discharge
the different proof method explicitly requested by Exercise 5.3.

No physical runtime, constant-time comparison, logarithmic height, cache repair
or allocation claim follows from the proposed semantic invariant. No new
resource model is needed in this bounded unit.

## 9. Inspected identities and handoff

Hashes below are ordinary byte SHA-256 identities, not project integrity-helper
results. File identities pin the whole file; the read-scope descriptions above
distinguish complete reads from relevant sections.

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| `book-source/chapter04.txt` | 17,850 | `27459294fd07b0204edb265aba765aaf33ef1a281108e7eafc488ee3c4d3da6c` |
| `book-source/chapter05.txt` | 32,466 | `b00475b2893cf76a66a5c164a63ee99e065772fffa7ae56054359b278c5c4b1e` |
| `book-source/chapter06.txt` | 11,842 | `b50500309106a77b094aebbc807b5b6979feb72d03bb443f2fd2785ee5dc3681` |
| `book-source/Tree.thy` | 17,104 | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `book-source/Tree_Set.thy` | 3,801 | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` |
| `book-source/Tree_Map.thy` | 2,028 | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` |
| `book-source/Tree_Rotations.thy` | 4,870 | `745064392da1c3ebc450bdc75ddcdf5b22baa2b135014daee8001d9c09e75eea` |
| `book-source/Sorted_Less.thy` | 2,133 | `971199401fc20cd378ad3ca9c22c314bba146e44b5730dcc718a2b0f6f6a52d5` |
| `book-source/AList_Upd_Del.thy` | 6,194 | `42f603405ff3fec058ba284c76183924139c42711ec66edaf623bd5b0a921f9a` |
| `book-source/Tree2.thy` | 1,560 | `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e` |
| `book-source/Isin2.thy` | 686 | `f6b0c6574c8fa618b5d42f3045e9af32731afd80a061173d8bc09eae9808df0c` |
| `book-source/Cmp.thy` | 682 | `5539b207634456f4c359dc12cabf720018cbc62c2c67b6d99ad0b7e5ac5993e6` |
| `book-source/Map_Specs.thy` | 2,970 | `54e97e50dc6e44d4d5533b92a109b50e781520c99bd0c50637b42470493b3e5d` |
| `book-source/ISABELLE-COPYRIGHT` | 1,673 | `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d` |
| `research/chapter04-obligations.md` | 39,471 | `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4` |
| `research/chapter05-obligations.md` | 45,177 | `f512f6b3723e8e036e9292aab985e93d15b2bf49b1c2c6dff79b3e6911ffcaad` |
| `research/chapter06-obligations.md` | 36,661 | `078bb9759e7bfd9245cfff69443f7722ae4b49295da61f311689da874bb20146` |
| `reviews/binary-tree-cache-requirements.md` | 14,576 | `81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce` |
| `reviews/tree-rotation-requirements.md` | 15,484 | `b194b8888b812416520fe6cf4dc23793b5059a7f2a990246adea172606918fed` |
| `Applications/Trees/Observations.lean` in XT06 | 4,119 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Rotations.lean` in XT06 | 7,436 | `d9a9aef015fbe2c3ffcc638ea8b963784adaec4d88d9b500b5a5f148264407b3` |
| `Applications/Trees/Cached.lean` in XT06 | 5,668 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| `Applications/Trees/CachedRotations.lean` in XT06 | 7,146 | `42dfd73e40f34c4e92de1def37dd877127bba061126e4102cc3b483d6dd2b9fc` |

The `research/` and `reviews/` rows above are relative to `fdsa-control`.
Only this new report was written. No existing source, requirements, inventory,
ticket, ref, cache or verification evidence changed. No compiler, Lean/Lake
process, checker, project hash helper, Git command, remote write or final
review cycle ran. The parent should reconcile this source scope with its
independent API/case preparation before freezing any new implementation unit.
