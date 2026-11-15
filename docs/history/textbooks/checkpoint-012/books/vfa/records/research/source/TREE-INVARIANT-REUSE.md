# Tree invariants and observations: bounded reuse investigation

2026-11-02. Planning evidence only; candidate `777bab9` remains under validation.
No chapter is accepted or started by this note. AGENTS, architectural/domain guidance,
GLOSSARY, and ADRs 0001/0010 were reread. Keep local domain proofs separate from
cross-domain examples; the evidence below does not call for a new tree hierarchy.

| Pinned VFA 2.1 source | SHA-256 |
| --- | --- |
| `SearchTree.v` | `44b9464a10e8c9e3222530f6f26be45bd44d1c0568deb1710417618706fae61d` |
| `Redblack.v` | `f44255ba3d0235f6efa401b72f2fcf9a9551a7ebc065912202d6f33494891ce2` |
| `Trie.v` | `a5af2b4db4c2cb639a8deb063e57909e11eb44ee763782ad0af9afbf45a78f3e` |

Sources are under `reference/vfa/vfa/`. Library paths below are relative to
`conaled/.lake/packages/`; project paths are relative to `conaled/`.
“Existing” means a definition or proved Lean declaration inspected in the pinned
source; no compiler was run or new import closure checked in this investigation.
The proposed adapters below remain unimplemented and unproved.
See `COMPUTATIONAL-ASSUMPTIONS.md` for abstract integer laws and binding/default
hazards; `POSITIVE-KEY-REUSE.md` owns positive-key and bit-order transport.

## Source seams and their actual hypotheses

| Seam | Source evidence and boundary |
| --- | --- |
| Raw search behavior | SearchTree 38–99 uses Nat keys, E/T, two strict comparisons, replacement on equality, and caller-supplied default. `lookup_insert_eq`/`neq` (296–341) and `bound_default` (364–367) do **not** assume BST: search and insertion follow the same path. Do not strengthen these source statements unnecessarily. |
| Ordering only | SearchTree `ForallT`/`BST` (160–181); Redblack analogues (237–250) constrain every subtree key, not merely child roots. Redblack orders decoded `Abs` keys and ignores color. `ForallT_insert` and Redblack `balanceP`/`insP` propagate arbitrary key/value predicates independently of ordering or balance. |
| Enumeration versus search | SearchTree `elements` (517–521) is raw inorder traversal. `elements_complete_spec` (577–581) needs bound=true but no BST; `elements_correct_spec` (596–600) needs BST. Its inverse statements (688–714) have correspondingly different hypotheses. Retain this asymmetry; a malformed raw tree can contain unreachable bindings. |
| Sortedness and duplicate keys | `sorted_elements` (745–755) and `elements_nodup_keys` (794–797) assume BST. Strict key ordering can support both the non-strict source sortedness result and key uniqueness. Payloads require no order, equality decision, or distinguished default. |
| Exact traversal equality | `fast_elements_tr_helper` (814–835) quantifies every accumulator and every raw tree. Redblack `elements_aux` (123–131) has the same accumulator recurrence after colors are erased. Neither equality needs BST/RB. Redblack 604–610 explicitly suggests reusing enumeration proofs from SearchTree. |
| Enumeration after update | SearchTree `kvs_insert` (886–894) replaces an existing equal-key pair; it does not just prepend or increase every list's length. `kvs_insert_split`/`kvs_insert_elements` (902–923) retain separator bounds/BST respectively. A bag-permutation insertion theorem alone misses replacement semantics. |
| Rotations and map behavior | Redblack `balance` (83–101) tests the two left-red patterns before right-red patterns; `ins` and `make_black` (103–118) are separate operations. `balance_BST` (398–404) and `balance_lookup` (501–511) require ordered subtrees and strict separator bounds, but no RB predicate. `lookup_ins_eq`/`neq` (528–547) need BST, unlike SearchTree. |
| Color and black height | Redblack `RB t parentColor n` (642–652) indexes the **parent** color and equal path black count. `NearlyRB` (669–677) is nonempty and permits a red-red violation only at the root. `ins_RB` (694–697) has two distinct conclusions; `insert_RB` (751–754) existentially permits a changed black height. These statements do not assume BST. |
| Shape bound | Redblack height/mindepth are exercise holes (777–786), with intended max/min path observations and bound `height ≤ 2*mindepth+1` for either parent color. Preserve that exact claim as well as any separate size/logarithm result; a depth-versus-size theorem alone does not prove the minimum-depth statement. |
| Trie path behavior | Trie 427–468 stores a value at every Node and a default alongside the tree. `look_ins_same`/`other` (557–566) hold on every raw trie; no ordering/balance predicate occurs. `is_trie` is a source hole (614–615), and no structural restriction is needed by these lookup equations. Choosing `True` remains a proposed justified completion, not a proved result here. |

The two SearchTree map observations also differ on malformed trees:
`Abs = map_of_list ∘ elements` (986–993) uses first-occurrence overwrite;
`Abs' = map_of_tree` (1154–1162, 1204–1223) uses a union that returns `None`
when both children bind a key. It is neither left-biased nor right-biased union.
Use BST/disjointness when transporting these observations, not unrestricted map equality.

## Direct existing ingredients

| Located API | Reuse and precise limitation |
| --- | --- |
| `mathlib/Mathlib/Data/Tree/Basic.lean`: `BinaryTree.nil/node`, `map`, `id_map`, `comp_map`, `height`, `numNodes`, `height_le_numNodes`, `numLeaves_eq_numNodes_succ` | Node stores its label internally, matching the three source shapes after packaging labels and reordering constructor arguments. `Tree` aliases are deprecated; use `BinaryTree`. These declarations give no BST or RB invariant. |
| `mathlib/Mathlib/Data/Tree/Get.lean`: `BinaryTree.get`, `getOrElse` | Exact Trie path cases: PosNum.one stops, bit0 goes left, bit1 goes right, nil returns none; `getOrElse` applies Option.getD. Proposed all-input bridge: source `look d p t = (encode t).getOrElse p d` after the positive-key adapter. No typeclass assumption on values or ordering is needed. Source path insertion and its default-filled intermediate nodes still need their own proof. |
| Same file: `BinaryTree.indexOf` | Executable comparator search using a `DecidableRel`; no correctness theorem for arbitrary malformed trees is supplied there. Searching a key/value label additionally needs a key projection/cut, so this is not an already-proved SearchTree implementation bridge. |
| `batteries/Batteries/Recycling/RBTree/Basic.lean`: `RBTree.RBNode.All`, `All.imp`, `Ordered`, `Balanced`, `foldr`, `toList`, `find?` | Raw colored nodes store a generic label; `(K × V)` with comparison on K avoids ordering payloads. `Ordered` uses `cmpLT`, which wraps a local `∀ [Std.TransCmp cmp]`; instantiate actual comparator laws and `cmpLT_iff` when relating it to source ordering, rather than accepting a vacuous conditional property. |
| `.../RBTree/Lemmas.lean`: `All_def`, `mem_toList`, `foldr_cons`, `toList_node`, `ordered_iff`, `Ordered.toList_sorted`, `setBlack_toList`, `balance1_toList`, `balance2_toList` | Exact inorder equations and All/list bridges permit shared ForallT/accumulator proofs. The balance-list equalities need no ordering or RB hypotheses. `ordered_iff` transports global tree ordering to Pairwise inorder; source comparator correspondence still has to be established. |
| Same file: `find?_some_mem`, `find?_some_eq_eq`, `Ordered.memP_iff_find?`, `Ordered.find?_some`, `Ordered.unique` | Forward successful-search membership is unconditional; converses require Ordered plus `Std.TransCmp`, and respectively `IsCut`/`IsStrictCut`. Comparator equality of key/value records means equal keys, not globally equal payloads. `Ordered.unique` derives equality for records actually in the same ordered tree. |
| `mathlib/Mathlib/Data/List/Nodup.lean`: `List.nodup_append'`, `List.Nodup.append` | Directly covers source `NoDup_append` once its explicit disjointness predicate is related to `List.Disjoint`. No element equality decision is needed. Key projections and strict-to-nonstrict order bridges remain explicit. |

## Red-black reuse requires two nontrivial adapters

The existing `RBTree.RBNode.Balanced t c n` indexes the **root** color,
and nil is black at height zero. Under a constructor-preserving encoding,
the proposed correspondences are source `RB t Red n` iff library Balanced
with root black, and source `RB t Black n` iff Balanced with some root color.
Source `NearlyRB` should correspond to library `RedRed True` **plus nonemptiness**:
library RedRed includes the empty balanced tree. These are proof obligations.

`batteries/Batteries/Recycling/RBTree/WF.lean` already proves
`Ordered.balance1`, `Ordered.balance2`, `balance1_All`, `balance2_All`,
`All.ins`, `Ordered.ins`, `Ordered.setBlack`, `Balanced.ins`, `Balanced.setBlack`,
`RedRed.balance1`, `RedRed.balance2`, and `WF_iff`.
Do not substitute the existing `ins`/`insert` without an operation adapter:
its black-node recursion balances only the changed side, and its `insert`
blackens only when the **input** root is red. On empty input, library insertion
returns a red singleton; VFA returns a black singleton. On arbitrary ordered
but RB-invalid inputs, source left-first balancing can also differ from the
side-specific library routine. The library's `balance2` also prioritizes the
right-right pattern over right-left, reversing VFA's choice if both match.
Valid insertion may exclude that overlap, but the exclusion needs proof.
`insert_setBlack` proves the library's own
post-blackening identity; it does not bridge source `ins` automatically.

`.../RBTree/Depth.lean` supplies `Balanced.depth_le`, `Balanced.le_size`,
`Balanced.depth_bound`, and `WF.depth_bound`; the latter bounds depth by
`2 * (size+1).log2`. Once the predicate/shape adapters are proved, these are
useful existing shape results. To discharge source `redblack_balanced`, retain
an independent minimum-depth lower bound from equal black heights; no such
source-specific bridge was found here. Neither shape theorem certifies runtime
cost, extraction, allocation, or garbage collection.
The old `Batteries/Data/RBMap/*` modules are deprecated reexports recommending
Std.TreeMap. The recycling implementation is a bounded proof reference/reuse
candidate; this note does not choose it as the public map implementation.

## Existing conaled seams and mismatches

- `Applications/Search/LeftistQueue.lean`: `Search.LeftistQueue.all_iff`,
  `Ranked`, `Heap`, `rank_paths`, `rank_size`, `rank_log` already separate contents,
  order, and shape. Leftist short/right-path rank is not red-black black height;
  its root-first entries are not sorted inorder. Do not transfer those facts by name.
- `Applications/Bracketing/Basic.lean`: `Bracketing.fringeAcc_eq` is the same
  accumulator proof pattern, but its trees have values only at leaves and no empty
  tree. `RandomAccess.Perfect`, `Cached`, `cached_size_erasure` in
  `Applications/Sequences/RandomAccess/{Basic,TreeBuild}.lean` constrain a different
  leaf-valued, cached-size representation. They are not source tree invariants.
- `Applications/Resources/TreeFlattening/Core.lean` supplies reusable
  `Resources.TreeFlattening.appendWithCost_exact`; its complete traversal counts
  are for Bracketing trees and cannot be copied onto internal-node enumeration.
- `Applications/Languages/WitnessTrie.lean` indexes finite observation depth and
  parse witnesses, with a child for every alphabet symbol. It is not the source
  sparse binary table. `Applications/Sorting/Stable.lean` gives `KeySorted` on
  records without ordering payloads; strict key uniqueness remains additional.
- `mathlib/Mathlib/Data/Ordmap/Invariants.lean`: `Ordnode.Sized`, `Balanced`,
  `Bounded`, `All.imp`, `all_iff_forall`, `foldr_cons_eq_toList`, `toList_node`,
  `Bounded.mono_left/right`, `Bounded.mem_lt/gt` are proved ingredients, but
  Ordnode is size-balanced with cached sizes, not red-black. Its bound propagation
  assumes only `Preorder`; it offers no automatic source operation equivalence.

## Minimal remaining proof ingredients

Prove observation/constructor erasures and arbitrary-accumulator traversal laws
without order assumptions. Require transitivity for separator propagation,
irreflexivity for key nodup, and a lawful executable key comparison for search
and update identification; do not impose payload order or decidable equality.
Keep RB shape proofs independent of key-order correctness, and BST proofs
independent of RB shape. Prove source balance's inorder preservation first,
then recover ForallT preservation and ordered lookup with their separate premises.
Preserve raw-tree statements alongside invariant-restricted converse statements.
Suggested later boundary cases: misplaced key, duplicate key, bound value equal
to the default, red-root singleton, unequal black heights, and Trie default-filled
paths. These are proposed checks, not completed proofs or chapter coverage.

Only this note was written; no compiler/build, cache, dependency, ticket, main,
or candidate source changed. All library inspection stayed inside this workspace.
