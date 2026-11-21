# Unbalanced search trees: two deletions and two correctness routes

This component implements FDSA Chapter 5 obligations FDSA-5-1 to FDSA-5-41 in the
[complete chapter ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).
Its intended tracking item is CTB-107 under CTB-24. Qualification and the exact
accepted candidate belong to the checkpoint's review and validation records;
this source correspondence does not itself assert that those gates have run.
The other 53 Chapter 5 obligations and the remaining books remain required.
Receiving integration review, including the effects of branch divergence,
whole-library build and exhaustive receiving audit remain separate.

## Sources and interpretation

The primary source is *Functional Data Structures and Algorithms*, version
27 July 2026, Chapter 5 pp. 59–67, from the
[official PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf).
The retained primary-text reading and canonical ledger identify the exact
equations and exercises. The pinned Isabelle companion is
`isabelle-prover/mirror-isabelle` revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. The complete recovered bodies of
`Tree_Set.thy`, `List_Ins_Del.thy`, `Sorted_Less.thy`, `Set_Specs.thy`, and
`Cmp.thy`, together with the BSD-3-Clause `COPYRIGHT`, were read before source
implementation. Their exact identities and the independent paper cases are
retained in the checkpoint preparation evidence. No new PDF-binary or visual
reading is claimed here.

`Tree_Set` specifies successor replacement and join deletion separately. Its
`split_min` has a nonempty domain; the Lean raw operation makes failure explicit
with `Option`. The source `join` never compares labels despite its Isabelle
type annotation, so its raw Lean equations quantify arbitrary label types.
`join0`, the direct recursive correctness exercise, and the split-based union
solution are independent implementations of the ledger's exercise obligations;
they are not attributed to definitions absent from `Tree_Set`.

The list insertion is equality suppressing. It is not duplicate-retaining
`List.orderedInsert`. The source deletion scans each unequal head and removes
the first equality; it does not stop when a larger head is encountered. Its
checked `List.erase` bridge retains exactly that behavior. The source's
strict order is represented by `List.Pairwise (<)` and connected to standard
adjacent `List.IsChain`; the nonstrict-order bridge explicitly includes Nodup.

`Set_Specs.Set_by_Ordered` keeps an auxiliary invariant independently of
strictness of the observed list. The composition below retains that conjunction.
It does not assume that balance, a cache, or a flag can be recovered from inorder.

## Shared owners and public interfaces

The existing `BinaryTree`, `Trees.inorder`, `Trees.setTree`, and
`Search.OrderedTree.Contains`, `All`, `OrderedBy`, `Ordered`, `member`, and
`insert` remain the common representation and operations. The public statement
of `contains_iff_mem_setTree` is unchanged. Its proof reuses the existing
`contains_iff_mem_entries` and `Trees.mem_inorder_iff_mem_setTree` bridges.
The deletion correctness lemmas still prove their own `Contains`, `All`, and
ordering results structurally before the separate list-update/refinement
route. Existing insertion and search comparison tariffs are unchanged.

| Owner | Responsibility |
| --- | --- |
| `Applications/Trees/Leftmost.lean` | Order-free paired extraction, explicit nonempty adapter, old `removeFirst`/`insertFirst` recovery, successor replacement callback |
| `Applications/Trees/Join.lean` | The two literal joins, raw inorder/contents/size and predicate transport |
| `Applications/Trees/JoinHeight.lean` | Raw height bounds, complete-input equality, natural-zero and increase boundaries |
| `Applications/Search/OrderedTree/Deletion.lean` | Shared outer key search and both distinct callbacks; original unkeyed operations; raw source/compare equations and height |
| `Applications/Search/OrderedTree/DeletionCorrectness.lean` | Structural extraction/join ordering and complete-label keyed deletion semantics |
| `Applications/Search/OrderedTree/Nodes.lean` | Independent node triples through rooted `Trees.Subtree`, and all-node characterization |
| `Applications/Search/OrderedTree/Union.lean` | Actual pivot split and union recursive on its first tree |
| `Applications/Search/OrderedList/Basic.lean`, `Sorted.lean` | Source list algorithms, strict-list set contract, all eight sorted-list equations |
| `Applications/Search/AbstractSet/Deletion.lean`, `Refinement.lean` | Additive deletion algebra, mixed histories and one generic auxiliary-invariant composition |
| `Applications/Search/OrderedTree/DeletionInterface.lean`, `Refinement.lean` | Direct seven-law contracts and separate Figure 5.1/composed contracts for the same operations |
| `Applications/Search/OrderedMap/DeletionInterface.lean`, `Deletion.lean` | Additive finite-map capability and both valid keyed-tree realizations |

`AbstractSet.Ops`, `Laws`, and the existing insertion-word clients now permit
independent element and representation universes. Their original relational
square declarations explicitly retain the common-universe domain required by
the existing square foundation. `DeleteOps.toOps` recovers the original
insertion-only interface; both tree instances project exactly to `baselineOps`.
Finite-map `DeleteOps.toOps` and `DeleteLaws.toLaws` likewise recover the existing
bind-only operations, laws, and `bindAll` executor. No payload order or equality
decision is required.

## Mathematical proof dependencies and exact boundaries

### Extraction and joins

`Trees.extractLeftmost` returns `none` exactly at nil. Every nonempty tree has
a successful result, and `extractLeftmostNonempty` uses that proof to recover
the pair with `Option.get`; no default label or `Inhabited` instance is introduced.
Success proves `x :: inorder remainder = inorder input`. A separate structural
proof gives the set/Contains decomposition and all-label predicate transport.
The remainder height is bounded on every raw tree.

For `OrderedBy key`, extraction's central invariant is an ordered residual
whose every key is strictly greater than the extracted key. It implies
leastness and exact complete-label removal. A `Preorder` on keys suffices for
these helpers. Payloads need no structure, and keys need not be globally
injective. The original first-insertion relation and `removeFirst` are recovered;
the extracted pair still loses the original left-spine insertion position.

Both source joins recurse on the facing subtrees. `join` promotes a returned
middle root, whereas `join0` retains the original left root. Their raw contents
proofs are structural, independent of inorder. The ordered proof carries the
strict interval between the two original roots through the middle result,
then checks the exact reconstructed nodes. The empty-middle branch needs no
inorder or node-count inference. Ordering additionally requires ordered inputs
and a strict cross bound on every left/right key pair.

The replacement callback `joinLeftmost` extracts from the nonempty right input
and places that complete label above the original left child and right residual.
It has a right-empty identity. It need not have a left-empty identity: replacing
above a right subtree can change its shape. Its raw bound, like `join`, is
`height ≤ max(left.height,right.height)+1`, exactly the bound needed at a deleted
root. `join0` instead has the sum bound, attained on every pair of complete
inputs, including nil and unequal heights.

The accepted `SharedTree.completeValue` family is reused as a constant-label
complete witness. A separate `Examples.TreeJoin.orderedComplete k start`
family proves completeness, height k, strict order, key interval bounds and
node count `2^k−1` by induction. The shifted family at start 1 reproduces the
seven-node textbook example. Its root has height k+1; joining its two children
with `join0` yields an ordered tree of height 2k. The exact near-doubling equation
is `result.height+2 = 2*original.height`, and height increases iff `1<k`.
Neither actual deletion uses `join0`.

### Direct deletion correctness

`deleteWith` shares only the actual outer key-search recursion. `deleteBy`
uses `joinLeftmost`; `deleteJoinBy` uses `join`. The unkeyed `delete` and
`deleteJoin` specialize `key := id`, retaining their different tree outputs.
The standard lawful comparator reflection lemmas justify their LT/EQ/GT
presentation. `LinearOrder` is needed for the failed-comparisons equality
inference; helper ordering preservation remains at `Preorder` where possible.

The structural proof first derives raw contents containment from a callback's
contents union. That gives preservation of arbitrary `All` bounds. Ordering
preservation then uses those bounds in recursive branches and ordered cross-bound
preservation at equality. Finally the full-label theorem proves:

```text
Contains z (deleteBy key q t) ↔ Contains z t ∧ key z ≠ q
```

and the identical observation statement for `deleteJoinBy`, under `OrderedBy`.
The untouched child/root labels differ from the query by the original strict
bounds. The equality branch preserves exactly the two children and removes
the root key. No global key-injectivity assumption is added. The direct set
contracts reuse existing direct membership/insertion proofs and the structural
set bridge; they do not consume the later list-update or refinement results.
Raw height nonincrease is a separate structural induction without validity.

The independent node-triple observation uses rooted subtree membership.
`OrderedNodesBy` checks both bounds over all labels of the children of every
triple. Its equivalence with recursive `OrderedBy` needs only `LT`; it does
not borrow transitivity from the inorder characterization. Immediate-child
tests fail on the retained descendant-4-under-root-3 example.

Split's equal branch returns the two original children, excluding the pivot
from both outputs. Its exact contents are the input labels strictly below and
above the pivot, and both outputs remain ordered. Union recurses structurally
on its first input, splitting the second at each retained first root. Its
contents theorem actually permits an arbitrary first tree and an ordered second
tree; the invariant theorem requires both ordered. The two operand orders can
produce unequal trees with equal sets. No balancing or complexity bound is claimed.

### The separate list refinement route

All eight source sorting equations retain their exact premises. Insertion
distribution assumes only `Strict (xs ++ [a])`, with arbitrary suffix `ys`.
Deletion distribution assumes `Strict (xs ++ a :: ys)`; if the query is below
the pivot but absent from the prefix, suffix absence still has to be proved.
The first-match erase bridge handles that case without changing the algorithm.

`inorder_insert`, `inorder_delete`, `inorder_deleteJoin`, and `member_inorder`
assume only strict inorder. The one generic `inorder_deleteWith` theorem needs
only raw inorder concatenation from its equality callback. Its two instances
therefore concern the actual distinct algorithms. The membership clause uses
the existing strict-inorder-to-BST characterization. The resulting generic
`AbstractSet.Refinement` stores primitive commuting equations and auxiliary
preservation, then derives all four semantic and three validity laws from the
target contract. It does not assume source correctness among its fields.

The two unbalanced tree instances take auxiliary invariant True. A concrete
`(tree,flag)` realization retains `flag=true` independently, and its seven laws
come from the same construction. Equal inorder for `(A,true)` and `(A,false)`
does not imply equal validity. Inorder forgets shape; set observation further
forgets order and multiplicity. The original search-run comparison counts can
differ for equal inorders, so these are value refinements, not work refinements.

Mixed insertion/deletion words use the existing list fold and
`SquareKit.ListFusion.foldl_reachable`. Every word and every prefix preserves
validity, and the observed set is an independent set-update fold. The frozen
ten-update example diverges after root deletion, reaches height 3 after
reinsertion, reconverges after deleting 1, handles absent deletion, and ends
empty. Direct and composed contracts both supply actual clients.

### Keyed maps and universe clients

The map proof consumes complete surviving bindings from the structural keyed
theorem. The accepted lookup/enumeration correspondence and valid-state
`lookup_correct` then establish the independent whole-tree observer's erase
law. This downstream use of enumeration does not replace the direct set proof.
Both valid keyed-tree realizations implement the additive interface. An
unconditional raw path-observer law is false: deleting root 2 can expose an
unreachable child binding at key 5 in a malformed input. That counterexample
is retained for arbitrary payloads as well as optional values.

The abstract consumer proves
`lookup q (delete k (bind q value state)) = if q=k then none else some value`
with independent key, payload and carrier universes and no payload structure.
The examples instantiate Nat keys in Type 0, `ULift Nat` payloads in Type 1,
and valid keyed-tree states lifted to Type 2, for both deletion implementations.
Explicit down-projection equations recover all operations and the original
observer; the projected original `bindAll` theorem is used directly. The set
client similarly lifts a valid Nat-tree carrier to Type 1, recovers operations,
transports actual mixed executions, and consumes the mixed-history observer law.

## Complete canonical correspondence

Abbreviations in this table: OT = `Search.OrderedTree`, OL =
`Search.OrderedList`, AS = `Search.AbstractSet`, T = `Trees`. Existing declarations
are identified as reuse. Cases refer to the frozen independent groups, not
post-execution expectations. Each row's general theorem remains the obligation;
finite cases are supplementary evidence.

| Row | Exact source obligation and implemented declarations | Proof/client and cases |
| --- | --- | --- |
| FDSA-5-1 | Recursive strict BST and independent contents: existing OT.`OrderedBy`, `Ordered`, `All`, `Contains`; OT.`contains_iff_mem_setTree` | Same statement through the existing canonical bridges; malformed/descendant boundaries G01/G07/G08 |
| FDSA-5-2 | Empty/insert/delete/member interface: AS.`DeleteOps`, `DeleteLaws`, original `Ops` projection | Independent operations/observer/validity and universes; G01/G03/G17 |
| FDSA-5-3 | Three-way comparison reflection and elimination: standard `compare_lt_iff_lt`, `compare_eq_iff_eq`, `compare_gt_iff_gt`; OT.`member_node_compare`, `insert_node_compare`, `deleteWith_node_compare` | Exact actual-operation branches, original tariff retained; G01 |
| FDSA-5-4 | Raw empty/search recurrence: existing OT.`memberRun`, `member`; OT.`member_node_compare` | Direct existing `member_correct`; G01/G07 |
| FDSA-5-5 | Raw insertion and equality unchanged: existing OT.`insert`; OT.`insert_node_compare` | Existing raw `contains_insert` and `ordered_insert`; G01 |
| FDSA-5-6 | Nonempty leftmost traversal: T.`extractLeftmost`, its three node/nil equations, `extractLeftmost_exists`, `extractLeftmostNonempty_spec` | Option failure iff nil, no default label; G02 |
| FDSA-5-7 | Inorder head/residual, leastness and exact ordered removal: T.`extractLeftmost_inorder`, OT.`extractLeftmost_ordered`, `extractLeftmost_least`, `extractLeftmost_removal` | Independent raw structural contents/All proofs; old residual/insertion recovery; G02/G07 |
| FDSA-5-8 | Actual successor deletion: OT.`deleteBy`, `delete`, `deleteBy_node`, `deleteBy_eq_root_nil`, `deleteBy_eq_root_extract` | Equality callback uses only proved nonempty extraction calls; G03/G04/G07 |
| FDSA-5-9 | Literal two-branch source join: T.`join`, `join_nil_left`, `join_nil_right`, `join_node_node` | Both returned-middle branches retained; G04/G05 |
| FDSA-5-10 | Raw inorder join and consequences: T.`inorder_join`, `numNodes_join`, `setTree_join`; OT.`orderedBy_join` | Raw structural union and ordered strict cross bounds; G04/G05 |
| FDSA-5-11 | Actual join deletion and refinement: OT.`deleteJoinBy`, `deleteJoin`, `deleteJoinBy_node`, `inorder_deleteJoin`, `deleteJoinSetLaws`, `refinedDeleteJoinSetLaws` | Distinct shape, same exact valid observation; G03/G04/G14 |
| FDSA-5-12 | Literal simpler join: T.`join0`, nil identities and `join0_node_node` | Separate raw inorder/contents/size and OT.`orderedBy_join0`; G04/G05 |
| FDSA-5-13 | Raw deletion height nonincrease: T.`extractLeftmost_height_le`, `height_joinLeftmost_le`; OT.`height_deleteWith_le`, `height_delete_le`, `height_deleteJoin_le` | No BST premise, actual chosen callbacks; G02/G03/G07 |
| FDSA-5-14 | Four set semantics: OT.`deleteSetLaws`, `deleteJoinSetLaws` | Structural observer, exact removal; separate composed contracts below; G01/G03/G14 |
| FDSA-5-15 | Three validity laws for each client: OT.`deleteLaws`, `deleteJoinLaws`, `ordered_delete`, `ordered_deleteJoin` | Uses raw All preservation before exact semantics; G03/G14 |
| FDSA-5-16 | Arbitrary mixed updates and every prefix: AS.`Update`, `execute`, `DeleteLaws.execute_valid`, `prefix_valid`, `execute_observe`, `execute_from_empty` | Existing reachable fold fusion; actual direct/refined/lifted consumers G14/G17 |
| FDSA-5-17 | Independent node triples and both full-child bounds: OT.`nodes`, `nodes_node`, `OrderedNodesBy`, `orderedNodesBy_iff`, `orderedNodes_iff` | Rooted subtree induction, LT-only; child-root counterexample G08 |
| FDSA-5-18 | Exact join bound: T.`height_join_le` | All raw trees, additive constant 1; G04/G05 |
| FDSA-5-19 | Sum bound for simpler join: T.`height_join0_le` | All raw trees; G04/G05/G06 |
| FDSA-5-20 | Complete-input equality and near doubling: T.`height_join0_of_complete`, `join0_root_heights`, `join0_root_height_increases_iff` | Universal constant-label and ordered complete families, exact near doubling and 0–5 table in `Examples.TreeJoin`; G06 |
| FDSA-5-21 | Direct seven-law exercise: OT.`contains_deleteWith_subset`, `all_deleteWith`, `orderedBy_deleteWith`, `contains_deleteWith`, both direct set contracts | Recursive Contains/All/Ordered and structural helper contents, no list-refinement dependency; G01–G04/G14 |
| FDSA-5-22 | Actual terminating union: OT.`union`, `union_node` | Structural first-tree recursion, second input generalized; G13 |
| FDSA-5-23 | Strict pivot partition: OT.`split`, `split_subset`, `ordered_split`, `contains_split`, `split_bounds`, `setTree_split` | Exact below/above filters exclude equality; G13 |
| FDSA-5-24 | Union semantics and preservation: OT.`contains_union`, `setTree_union`, `ordered_union` | Set equality, ordered output, unequal shapes under operand exchange; G13 |
| FDSA-5-25 | Strict inorder and raw contents characterization: existing OT.`ordered_iff_inorder_pairwise`, `orderedBy_iff_inorder_pairwise`, raw contents bridge; OL.`strict_iff_adjacent`, `strict_iff_nodup_nonstrict` | Forward transitivity vs LT-only converse; strictness distinct from nonstrict sorting; G07/G08/G09/G15 |
| FDSA-5-26 | Equality-suppressing list insertion: OL.`insert` | Literal source recurrence on arbitrary lists; G09/G11 |
| FDSA-5-27 | First-match list deletion: OL.`delete`, `delete_eq_erase`, `delete_of_not_mem` | Scans past greater unequal heads; G09/G12 |
| FDSA-5-28 | Figure 5.1: existing T.`inorder_nil`; OT.`inorder_insert`, `inorder_delete`, `inorder_deleteJoin`, `member_inorder` | Strict inorder alone, exact operational equality; malformed counterexamples G07 and clients G14 |
| FDSA-5-29 | Equation 5.1 midpoint decomposition: OL.`strict_middle` | Pairwise append and transitivity; G10 |
| FDSA-5-30 | Equation 5.2 four-part decomposition: OL.`strict_four_parts` | Explicit `x :: (xs ++ y :: ys)` parsing and required x<y; G10 |
| FDSA-5-31 | Equation 5.3 tail consequence: OL.`strict_tail` | Only LT required; G10 |
| FDSA-5-32 | Equation 5.4 prefix consequence: OL.`strict_prefix` | Only LT required; G10 |
| FDSA-5-33 | Equation 5.5 insertion distribution: OL.`insert_distribution`, `_lt`, `_ge` | Only strict prefix through pivot, arbitrary suffix; positive and negative boundary G11 |
| FDSA-5-34 | Equation 5.6 deletion distribution: OL.`delete_distribution`, `_lt`, `_ge` | Whole-list strictness and absent-query case; weaker-premise counterexample G12 |
| FDSA-5-35 | Equation 5.7 all-members cons: OL.`strict_cons_iff` | Standard Pairwise cons, LT-only; G10 |
| FDSA-5-36 | Equation 5.8 all-members snoc: OL.`strict_snoc_iff` | Standard Pairwise append, LT-only; G10 |
| FDSA-5-37 | Arbitrary-list insertion union: OL.`mem_insert`, insertion field of OL.`laws` | No strictness premise in underlying theorem; unsorted duplicate case G09 |
| FDSA-5-38 | Strict-list deletion difference: OL.`mem_delete`, stronger uniqueness helper `mem_delete_of_nodup` | Raw duplicate counterexample retained; G09 |
| FDSA-5-39 | Insertion preserves strictness: OL.`strict_insert` | Actual source operation, existing Pairwise infrastructure; G09/G11 |
| FDSA-5-40 | Deletion preserves strictness: OL.`strict_delete` | Checked erase bridge and Pairwise erase; G09/G12 |
| FDSA-5-41 | One reusable composition: AS.`Refinement`, `Refinement.Valid`, `.laws`, `.execute`; OT.`inorderRefinement`, `inorderJoinRefinement`, both `refinedDelete...SetLaws` | Aux ∧ target validity, actual primitive commutation, both real algorithms; flag and mixed consumers G14/G15/G17 |

## Concrete-case ownership

| Frozen groups | Actual example declarations |
| --- | --- |
| G01 | `OrderedTreeDeletion.compare_cases`, `member_cases`, `insertion_cases` |
| G02 | `TreeJoin.extraction_cases`, `extraction_residual_heights`, `extraction_not_raw_least`, `extraction_not_raw_removal`, `old_first_insertion_recovery`, `empty_label_extraction` |
| G03 | `OrderedTreeDeletion.successor_deletion_cases`, `join_deletion_cases`, `deletion_shape_separation` |
| G04 | `TreeJoin.seven_node_shapes`, `seven_node_observations`, `seven_node_results_ordered`, `residual_right_child_survives` |
| G05 | `TreeJoin.raw_join_small`, `symbolic_join`, `symbolic_join0`, `repeated_label_joins`, `unequal_complete_join_shapes`; universal nil equations |
| G06 | `TreeJoin.completeValue_complete`, `completeValue_join0_heights`, `complete_table`, all `orderedComplete...` laws, `shifted_root`, `ordered_root_elimination_increases` |
| G07 | `OrderedTreeDeletion.malformed_search_deletion`, `duplicate_deletion`; `OrderedSetRefinement.malformed_refinement_boundaries` |
| G08 | `OrderedTreeDeletion.aTree_nodes`, `child_roots_are_insufficient`, `all_node_counterexample`, `all_node_positive` |
| G09 | `OrderedSetRefinement.list_insert_cases`, `list_delete_cases`, `strict_cases`; general raw insertion and unique deletion laws |
| G10 | `OrderedSetRefinement.midpoint_cases`, `four_part_cases`, `cons_snoc_boundaries`; all eight general equations |
| G11 | `OrderedSetRefinement.insertion_weak_prefix`, `insertion_weak_prefix_consumer`, `insertion_bad_prefix` |
| G12 | `OrderedSetRefinement.deletion_whole_cases`, `deletion_whole_consumer`, `deletion_weak_premise_fails` |
| G13 | `OrderedTreeDeletion.split_cases`, `split_outputs_ordered`, `union_cases`, `union_observations`, `union_result_ordered` |
| G14 | `OrderedSetRefinement.successor_prefix_shapes`, `join_prefix_shapes`, `mixed_prefix_observations`, `every_mixed_prefix_valid`, `every_mixed_word_meaning`, `every_mixed_word_refines` |
| G15 | `TreeJoin.extraction_loses_position`; `OrderedSetRefinement.shape_and_work_loss`, `set_order_loss`, `set_multiplicity_loss`, `flagRefinement`, `flagLaws`, `flag_separation` |
| G16 | `OrderedTreeDeletion.optionalMap_ordered`, `optional_lookup_cases`, `optional_delete_cases`, `optional_map_sizes`, `malformed_map_path_changes`, `malformed_map_arbitrary_payload` |
| G17 | `OrderedSetRefinement.liftedSetLaws`, `lifted_set_recovery`, `lifted_set_execution`, `lifted_set_mixed_meaning`, `lifted_set_prefix_ordered`, `lifted_set_word_finishes_empty`, `liftMapLaws`, `lifted_map_recovery`, `lifted_map_consumers`, `lifted_projected_bindAll` |

Example namespaces in the last table are prefixed by `Examples.`. The frozen
cases precede implementation. Source equations, complete declaration/member
inventories, actual elaborated statements, private guarded validation and both
review axes supply the remaining evidence; a count of rows or declarations is
not a mathematical qualification criterion.

The continuation remains FDSA-5-42 to FDSA-5-65 positioned rotations, FDSA-5-66 to FDSA-5-84 interval
trees, FDSA-5-85 to FDSA-5-90 balanced/sweep obligations, and FDSA-5-91 to FDSA-5-94 diameter,
verification complexity and the separate unit-visit expected-search model.
The latter is not the existing two-comparison `memberRun` tariff. No chapter
closure, complete-book closure, physical-sharing guarantee or receiving
acceptance follows merely from these first 41 rows.
