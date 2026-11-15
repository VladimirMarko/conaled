# Local #1009 — VFA SearchTree: requirements and reuse plan

**Planning only, 2026-11-02. Implementation is blocked until #1008 Maps is accepted.**
The chapter order remains Merge → Maps → SearchTree → ADT. This plan supplies
no algorithm implementation, Lean proof, compiler result, chapter acceptance,
tracker change, or candidate change. Its proposed names and interfaces must be
reconciled with the accepted predecessor APIs before implementation. Root owns
the current unrelated-to-this-plan validation process and all integration.

## Source identity and scope

- Complete inspected source: VFA 2.1, release cover `2026-08-24 10:11`,
  [SearchTree](https://softwarefoundations.cis.upenn.edu/vfa-2.1/SearchTree.html),
  `reference/vfa/vfa/SearchTree.v`: **1,325 lines, 44,738 bytes**, SHA-256
  `44b9464a10e8c9e3222530f6f26be45bd44d1c0568deb1710417618706fae61d`.
- `../source/SearchTree.inventory.json`, SHA-256
  `23dad4eb956d2e6acddf5a845e4ac32b10156da02069defb6a202c914af3331f`:
  **90 records, 35 exercises, 11 pedagogical commands**. The exercises include
  24 optional and 12 advanced, with eight in both categories. All are in scope.
  The records comprise 27 definitions, 18 source-proved declarations,
  41 source admissions to discharge, two Coq tactics, one grading stub, and one
  deliberately aborted false specification. The inventory is a lexical aid;
  this plan also follows the entire chapter prose.
- The archive and its recovery policy are in `../source/SOURCE-RECOVERY.md`:
  official versioned archive SHA-256
  `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
  Preserve the MIT attribution/license; exclude downloaded research copies
  from deliverables under ADR 0001.
- Inspected checkout: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, Lean 4.35.0,
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its enclosing Preface/Perm
  validation is still pending. Record the actual accepted Maps baseline later.
- Read AGENTS, architectural/domain guidance, GLOSSARY, ADRs 0001/0010,
  README build/audit policy, `../REQUIREMENTS.md`, the complete chapter,
  `../source/TREE-INVARIANT-REUSE.md`, `COMPUTATIONAL-ASSUMPTIONS.md`, and
  `RESOURCE-AND-EXECUTION-OBLIGATIONS.md`. Relevant staged table, unary-cost,
  and positive-key code was inspected. None of those drafts is chapter acceptance.

## Architecture and actual reuse

Prefer a small `Applications/Tables/SearchTree.lean` family adjoining the
proposed Maps functional-table module, with resource instrumentation separated
when it materially aids reuse. Put cross-domain compositions in `Examples`.
Names are provisional; the accepted Maps integration determines the final
module boundary. Reuse `BinaryTree (K × V)` rather than introducing another
isomorphic binary-tree carrier. A source constructor adapter presents
`T l k v r` as `.node (k,v) l r`; `E` is `.nil`. This preserves raw malformed
trees as well as valid trees, which the chapter explicitly needs.

Storage, traversal, and node predicates need no ordering, payload equality, or
default value. Search/insert require an executable strict key comparison;
their mathematical laws require a lawful strict total ordering, available from
the ordinary key `LinearOrder` specialization. Keep computations and the laws
they use separate. Do not require an order or `DecidableEq` on payloads.
Nat is the exact source specialization; source-facing theorems retain all raw
inputs where the source does. No new comparator, container, or square hierarchy
is justified by this chapter.

| Inspected existing declaration / source | Exact use and limitation |
| --- | --- |
| `BinaryTree.nil/node`, `map`, `id_map`, `comp_map`, `height`, `numNodes`, `height_le_numNodes`, `numLeaves_eq_numNodes_succ`; Mathlib `Data/Tree/Basic.lean` | Internal-node labels match source key/value nodes after the constructor adapter. `height nil=0`, `height(node)=max child heights+1`; `numNodes` counts internal nodes. These are reusable shape operations, not a BST invariant or search proof. Use `BinaryTree`, not deprecated `Tree` aliases. |
| `BinaryTree.indexOf`, `get`, `getOrElse`; Mathlib `Data/Tree/Get.lean` | `indexOf` uses `cmpUsing` on complete labels and returns an optional positive path; `get` follows that path and `getOrElse` forgets absence. These are not an already-proved key-projection lookup/insert implementation. Do not introduce a dummy payload or claim equivalence from the name alone. The small direct source search recurrence remains needed. |
| `Function.update`, `update_self`, `update_of_ne`, `update_apply`, `update_eq_self`, `update_idem`, `update_comm`; Mathlib `Logic/Function/Basic.lean` | Use accepted Maps operations and these actual laws. `update_of_ne` takes query ≠ write; `update_comm` takes distinct written keys and equates the two write orders. Prove the tree observation bridge and reuse the algebra instead of reproving a function-map library. |
| Staged `TablePreparation.Ops`, separate `Laws`, `observe`, `Laws.observe_set`, `ObservedEq`, `twoWrites_equivalent` | `Ops` has empty/get/set; validity is a separate `Laws` parameter. Source raw search equations permit `Valid := True`. BST-dependent enumeration/abstraction laws remain additional statements, not a reason to weaken raw laws. Reuse the draft only after its integration/review; Maps may leave it staged until this first concrete consumer. |
| Staged `lookup?`, `lookup_cons_update`, `withDefault`, `hasBinding`, `withDefault_update`, `binding_iff` | First matching association-list binding wins. `binding_iff` states `m q = some v ↔ hasBinding m q = true ∧ withDefault d m q = v`. This is the exact presence/default seam; it does not make total observations injective. |
| `List.Nodup.append`, `nodup_append'`; Mathlib `Data/List/Nodup.lean` | `Nodup l₁ → Nodup l₂ → Disjoint l₁ l₂ → Nodup (l₁++l₂)`. Relate the chapter's explicit membership-disjointness to `List.Disjoint`; no equality decision is needed. |
| `Applications.Sorting.KeySorted`; `Applications/Sorting/Stable.lean` | Pairwise non-strict key order without ordering payloads. Obtain the chapter's accepted `Sort.sorted` result by its already-proved adapter. Strict key order and key nodup remain separate stronger facts. |
| `List.Pairwise.eq_of_mem_iff`; Mathlib `Data/List/Sort.lean` | Under `Std.Antisymm r` and `Std.Irrefl r`, two Pairwise lists with identical membership are equal. Useful for canonical inorder enumeration with strict key relation and actual equal binding pairs. Non-strict key order is not antisymmetric on arbitrary key/value records. |
| `Resources.TreeFlattening.appendWithCost_exact`; `Applications/Resources/TreeFlattening/Core.lean` | For arbitrary lists, its actual recursive append returns `(xs++ys, xs.length)`. Reuse this count primitive; the enclosing Bracketing traversal has leaf-valued nonempty trees, so its complete traversal-cost theorems do not apply directly to SearchTree. |
| `Resources.Measured`, `bind`, `bind_erases`, `reweight`, `erasureSquare`; `Applications/Resources/Measured.lean` | Instrument the actual tree recurrences and prove value erasure. `Measured`/`bind` support independent universes; `erasureSquare` currently packages input/output/count in one universe. Keep generic erasure theorems and use compatible concrete packages, without silently constraining all payloads to Type 0. |
| `Resources.isBigO_of_nat_bound`; `Applications/Resources/Growth.lean` | Converts an explicit eventual Nat bound `f n ≤ C*g n` to the real-cast standard `Asymptotics.IsBigO`. It supplies no tree recurrence or logarithmic-height assumption. |
| Staged unary `unaryLERun_spec`, `equal_inputs_steps`, `no_difference_only_bound` | The inspected lockstep ≤ model has exact count `min n m+1`, including its terminal call. It is explicitly not identified with Coq `Nat.ltb` or native Lean Nat. Reuse the counterexample/qualified comparison model after integration, with a separate strict-comparison adapter if needed. |

Size-balanced Ordnode and red-black containers have different operations and
invariants. Substituting one would discard raw-source behavior and structural
counterexamples. The positive-key draft belongs to future binary-key adapters;
this chapter does not change Nat keys into shifted positive paths.

## Required operation equations and semantic boundaries

The following are **mathematical requirements**, not new Lean definitions.
Write `N(l,k,v,r)` for the constructor adapter and `E` for the empty tree.

| Operation | Required equations |
| --- | --- |
| `bound q E`, `lookup d q E` | Respectively `false` and `d`. |
| Search at `N(l,k,v,r)` | Test `q<k` first; if true recurse left. Otherwise test `k<q`; if true recurse right. Otherwise return `true` for bound and `v` for lookup. Retain short-circuit comparison order in measured runs. |
| `insert k v E` | `N(E,k,v,E)`. |
| Insert at `N(l,x,w,r)` | Test `k<x`, then `x<k`; rebuild only the chosen recursive branch. Equality branch is `N(l,k,v,r)`, replacing the existing value without adding a duplicate. |
| `ForallT P` | True on E; `P k v ∧ ForallT P l ∧ ForallT P r` at a node. It inspects every node, including unreachable malformed bindings. |
| `BST` | E is valid; a node has valid children, every left key strictly less than its root, and every right key strictly greater. Immediate-child comparisons alone are insufficient. |
| `elements` | `[]` on E; `elements l ++ [(k,v)] ++ elements r` at a node. Expose the source recurrence and its reassociated cons form. |
| `fast_elements_tr t acc` | E returns acc; a node returns `fast_elements_tr l ((k,v)::fast_elements_tr r acc)`. Prove the arbitrary-accumulator equation before specializing acc to `[]`. |
| `kvs_insert k v` | Empty list gives `[(k,v)]`; before a greater head insert the new pair; after a smaller head recurse; at equal key replace that head's value. It is not prepend and does not always increase length. |
| `map_of_list` / `Abs` | Empty list gives the none-valued map; a cons updates the recursive tail map with `some v`, so the **head wins**. `Abs t = map_of_list(elements t)`. |
| `find` / `map_bound` | `(m k).getD d` and `(m k).isSome`, reusing accepted Maps/default-observation definitions. |
| `union m₁ m₂` | none/none ↦ none, some/none or none/some ↦ that value, **some/some ↦ none**, even when the two values agree. This is symmetric collision removal, not left/right-biased union. |
| `map_of_tree` / `Abs'` | E gives empty; a node updates the collision-removing union of both child maps at the root key with `some v`. `Abs'` is this direct structural map. |

Preserve these distinctions in statements and checked cases:

1. Raw-tree empty/lookup-after-insert/bound-after-insert equations and the
   resulting lookup algebra need **no BST premise**. Search and insertion
   follow the same path even in malformed trees. `ForallT_insert` likewise
   preserves any predicate given its old-tree and new-binding premises.
2. Enumeration completeness needs `bound=true` and the lookup value, but no
   BST. Enumeration soundness, sortedness, key uniqueness and model-based
   correspondences need BST. Inverse completeness retains BST; inverse
   correctness and `bound_value` do not. Preserve `∃ v, ∀ d` in `bound_value`.
3. Pointwise/default-valued lookup equality forgets explicit presence and tree
   shape. Self-insertion can create a default-valued binding; distinct insert
   orders can give different roots. Structural shadowing **does** hold.
4. `Abs` and `Abs'` are defined for all raw trees. Prove their agreement on BSTs,
   not on every tree. Their finite images do not make the entire function space
   `K → Option V` finite or enumerable. For every tree, separately establish
   finite observed support from its finite node/list representation.
5. Prove primed empty/bound/lookup/insert correspondences directly through the
   structural abstraction and union laws, preserving the chapter's alternative
   proof route without using `elements` as the intermediate decoder. Then prove
   the harder `elements_relate'` coherence theorem. An alias to the first
   abstraction or a circular dependency on coherence misses that method.
6. Union update laws require absence at the written key on the other side;
   they do not require global disjointness. `map_of_list_app` instead requires
   disjoint **projected key sets** between lists, but no per-list nodup. Do not
   assume an unrestricted monoid union: with three overlapping bindings,
   parenthesization can change the surviving value.
7. The prose canonical-enumeration claim requires two valid trees with the
   same **partial-map bindings**, not merely the same one-default lookup.
   Prove `BST t → BST u → Abs t=Abs u → elements t=elements u`, using actual
   binding membership and strict sortedness/uniqueness. Different shapes may
   still have equal canonical enumerations.

## Complete 90-record map

Each row names the exact lexical source record. Target descriptions are
obligations for later accepted Lean declarations, not claims of implementation.
The source `SearchTree.` prefix is shown in every identifier to make coverage
checks unambiguous. Mathematical helper reuse is allowed when the exact type
and direction match.

| Source record | Intended obligation / adaptation |
| --- | --- |
| `SearchTree.key@38` | Nat source keys; generic ordered-key library specialization. |
| `SearchTree.tree@44` | Existing `BinaryTree (K×V)` plus E/T constructor correspondence, retaining arbitrary raw trees. |
| `SearchTree.ex_tree@59` | The exact tree with root 4→"four", left 2→"two", right 5→"five". |
| `SearchTree.empty_tree@64` | E-valued empty operation, with no payload inhabitance requirement. |
| `SearchTree.bound@69` | Boolean path-search recurrence above; do not define it by raw membership. |
| `SearchTree.lookup@80` | Caller-supplied-default path search with the same branch order as bound. |
| `SearchTree.insert@91` | Persistent path insertion/replacement recurrence, exact equality branch. |
| `SearchTree.Tests.bst_ex1@109` | Insert 4, then 2, then 5 into E yields exactly ex_tree. |
| `SearchTree.Tests.bst_ex2@113` | Lookup 5 with default "" in ex_tree is "five". |
| `SearchTree.Tests.bst_ex3@116` | Lookup absent 3 with default "" is "". |
| `SearchTree.Tests.bst_ex4@119` | bound 3 ex_tree is false. |
| `SearchTree.NotBst.t@141` | Root 4, misplaced left 5 and right 2, with the exact source strings. |
| `SearchTree.NotBst.not_bst_lookup_wrong@149` | Lookup 2 in that malformed tree does not produce "two". |
| `SearchTree.ForallT@160` | All-node key/value predicate and constructor equations, independent of search/order. |
| `SearchTree.BST@174` | Full-subtree strict separator invariant and inductive elimination/constructor interface. |
| `SearchTree.is_BST_ex@188` | ex_tree satisfies the actual invariant. |
| `SearchTree.not_BST_ex@195` | NotBst.t violates the actual invariant; exhibit offending subtree key. |
| `SearchTree.empty_tree_BST@206` | Valid empty for arbitrary payload type. |
| `SearchTree.ForallT_insert@220` | All-node P and P on the new pair imply P after insert, for every raw tree. |
| `SearchTree.insert_BST@229` | Insertion preserves BST; retain all-node helper use and nonvacuous valid constructors. |
| `SearchTree.lookup_empty@290` | Every key/default on E returns that default. |
| `SearchTree.lookup_insert_eq@296` | Lookup written key returns written value on every raw tree. |
| `SearchTree.bdestruct_guard@311` | Adapt proof automation to ordinary Lean comparison cases/decide reflection and arithmetic; no new tactic framework is required. |
| `SearchTree.bdall@320` | Explain the repeated-case simplification idiom in checked proofs; no runtime or theorem-content claim. |
| `SearchTree.lookup_insert_eq'@323` | Same mathematical statement as lookup_insert_eq; map to its accepted declaration with the alternative automation explanation. |
| `SearchTree.lookup_insert_neq@333` | Written k ≠ queried k' preserves lookup at k', with no BST. |
| `SearchTree.manual_grade_for_bound_correct@356` | Grading stub omitted; its substantive exercise requires all three bound laws: empty=false, just-inserted=true, distinct-key bound unchanged. |
| `SearchTree.bound_default@364` | bound=false implies lookup returns the caller's d on all raw trees; converse is false. |
| `SearchTree.lookup_insert_shadow@432` | Same-key latest-write wins at every query/default, derived through public raw lookup laws. |
| `SearchTree.lookup_insert_same@443` | Inserting the current lookup value preserves that default-valued observation at every query; no structural equality or presence claim. |
| `SearchTree.lookup_insert_permute@453` | Distinct written keys commute under every query/default observation, through public laws. |
| `SearchTree.insert_shadow_equality@475` | Same-key double insert collapses to a single latest insert as an equality of raw trees. |
| `SearchTree.insert_same_equality_breaks@493` | Existential counterexample: inserting a default-valued key into E changes its shape. |
| `SearchTree.insert_permute_equality_breaks@499` | Existential distinct-key counterexample: insert 0 and 1 in opposite orders into E; root shapes differ. |
| `SearchTree.elements@517` | Exact inorder list recurrence for arbitrary raw trees. |
| `SearchTree.elements_ex@523` | ex_tree enumerates [(2,"two"),(4,"four"),(5,"five")]. |
| `SearchTree.elements_complete_broken_spec@554` | Preserve the proposed false formula as a documented boundary and prove its negation via E/default, rather than accepting it. |
| `SearchTree.elements_complete_broken@567` | Pedagogical Abort; no theorem of the false statement. The checked empty-tree counterexample explains the failed attempt. |
| `SearchTree.elements_complete_spec@577` | bound=true and lookup=v imply pair membership, with no BST. |
| `SearchTree.elements_complete@587` | Discharge that all-raw-tree completeness proposition. |
| `SearchTree.elements_correct_spec@596` | BST and pair membership imply bound=true and lookup=v for every default. |
| `SearchTree.uncurry@626` | Reuse ordinary pair pattern matching/Function.uncurry; preserve P's separate key and value arguments. |
| `SearchTree.elements_preserves_forall@631` | ForallT P transports to every pair in elements; no BST. |
| `SearchTree.elements_preserves_relation@652` | Any R to distinguished key k' transports from ForallT to a member (k,v), yielding R k k'. |
| `SearchTree.elements_correct@667` | Discharge soundness using BST and all-node relation transport. |
| `SearchTree.elements_complete_inverse@688` | BST plus bound=false excludes every proposed value pair at that key. |
| `SearchTree.bound_value@703` | bound=true gives one value independent of every caller default: ∃v, ∀d, lookup d k t=v. |
| `SearchTree.elements_correct_inverse@710` | Absence of every (k,v) from enumeration implies bound=false on any raw tree. |
| `SearchTree.sorted_app@731` | Two accepted source-sorted Nat lists, all left values < x and all right values > x, give sorted(l₁++x::l₂); reuse existing list order interfaces. |
| `SearchTree.list_keys@745` | List.map Prod.fst; do not order payloads. |
| `SearchTree.sorted_elements@751` | BST gives source non-strict sortedness of projected keys, via a proved strict Pairwise result/accepted sorting adapter. |
| `SearchTree.disjoint@772` | Relate the explicit ∀x∈l₁, x∉l₂ predicate to List.Disjoint. |
| `SearchTree.NoDup_append@781` | Instantiate existing Nodup.append at exact disjointness premises. |
| `SearchTree.elements_nodup_keys@794` | BST gives nodup of projected keys, not just nodup of whole pairs. |
| `SearchTree.fast_elements_tr@814` | The exact nested right-result/left-accumulator recurrence, for arbitrary accumulator. |
| `SearchTree.fast_elements@821` | Specialization at empty accumulator. |
| `SearchTree.fast_elements_tr_helper@829` | For all raw trees/lists, fast accumulator result equals elements t ++ acc. |
| `SearchTree.fast_elements_eq_elements@835` | For all raw trees, the two enumerators agree. |
| `SearchTree.fast_elements_correct@846` | Recover soundness through the public equality and original soundness theorem; retain BST. |
| `SearchTree.elements_empty@874` | Empty inorder enumeration is []. |
| `SearchTree.kvs_insert@886` | Exact sorted-list-style insertion with same-key replacement, defined on all lists. |
| `SearchTree.kvs_insert_split@902` | Separator-bounded e₁/e₂ give the exact three-way equation around (k₀,v₀); no unmentioned per-list sorting premise. |
| `SearchTree.kvs_insert_elements@918` | For BST t, enumeration after tree insert equals kvs_insert on its enumeration. |
| `SearchTree.map_of_list@986` | Accepted partial-map empty/update folded tail-first so earlier list entries override later ones. Prove bridge to first-match lookup?. |
| `SearchTree.Abs@992` | Partial-map decoder through inorder enumeration, defined for all trees. |
| `SearchTree.find@1007` | Accepted withDefault/getD observation with caller d. |
| `SearchTree.map_bound@1015` | Accepted hasBinding/isSome observation. |
| `SearchTree.in_fst@1036` | Pair membership implies key membership in map fst; reuse List.mem_map witness. |
| `SearchTree.in_map_of_list@1043` | Projected-key Nodup plus pair membership yields exactly Some v at the key. Keep the Nodup hypothesis. |
| `SearchTree.not_in_map_of_list@1051` | Key absent from map fst gives None, without nodup. |
| `SearchTree.empty_relate@1057` | Abs E equals empty as a function. |
| `SearchTree.bound_relate@1065` | Under BST, map_bound k (Abs t)=bound k t, including explicit default-valued bindings. |
| `SearchTree.lookup_relate@1075` | Under BST, find d k (Abs t)=lookup d k t for every d. |
| `SearchTree.insert_relate@1082` | Under BST, Abs(insert k v t)=update(Abs t) k v; reuse kvs_insert_elements and a list-decoder update law. |
| `SearchTree.elements_relate@1132` | Definitional map_of_list(elements t)=Abs t; retain the source-facing BST specialization while exposing the stronger unconditional equality if useful. |
| `SearchTree.union@1154` | Exact four Option branches with overlap ↦ None, no biased container-union substitution. |
| `SearchTree.union_left@1167` | If m₂ k=None, union at k equals m₁ k. |
| `SearchTree.union_right@1172` | If m₁ k=None, union at k equals m₂ k. |
| `SearchTree.union_both@1178` | Two Some bindings, equal or different values, yield None at k. |
| `SearchTree.union_update_right@1187` | m₁ k=None permits moving a write at k into the right union operand, as function equality. |
| `SearchTree.union_update_left@1193` | m₂ k=None permits the corresponding left move, as function equality. |
| `SearchTree.map_of_tree@1204` | Direct node recursion: root update after collision-removing union of child maps. |
| `SearchTree.map_of_tree_prop@1211` | ForallT P and a Some v structural-map result imply P k v, with no BST. |
| `SearchTree.Abs'@1222` | The direct structural decoder; distinct definition from enumeration decoder. |
| `SearchTree.empty_relate'@1225` | Direct decoder E is empty. |
| `SearchTree.bound_relate'@1232` | BST-dependent binding correspondence proved via structural decoder, not prior enumeration coherence. |
| `SearchTree.lookup_relate'@1240` | BST-dependent default lookup correspondence through the direct abstraction route. |
| `SearchTree.insert_relate'@1247` | BST-dependent direct-decoder update correspondence using separator absence and union update laws. |
| `SearchTree.map_of_list_app@1258` | Disjoint projected key sets imply list-append decoder equals collision-removing union; no within-list nodup requirement. |
| `SearchTree.elements_relate'@1266` | Under BST, map_of_list(elements t)=Abs' t; thereby both abstractions agree on valid trees. |

## Exercise and command checklist

The 35 exercise headings below all have substantive work, even when the only
lexical declaration is a grading stub. Their individual declarations appear
above; optional/advanced labels do not reduce acceptance scope.

| Exercise | Source lines | Tags | Completion group |
| --- | --- | --- | --- |
| empty_tree_BST | 202–211 | standard | Invariant constructors |
| insert_BST | 213–234 | standard | ForallT preservation and BST preservation |
| bound_correct | 346–357 | optional | Three new raw bound equations, not the grading stub |
| bound_default | 359–371 | optional | Absence/default implication |
| lookup_insert_shadow | 430–439 | optional | Observational algebra |
| lookup_insert_same | 441–449 | optional | Observational algebra |
| lookup_insert_permute | 451–461 | optional | Observational algebra |
| direct_equalities_break | 486–505 | optional | Both existential shape counterexamples |
| elements_complete | 583–591 | standard | Bound-and-lookup completeness |
| elements_preserves_forall | 614–637 | standard | All-node/list predicate bridge |
| elements_preserves_relation | 639–660 | standard | Arbitrary relation specialization |
| elements_correct | 662–671 | standard | BST-dependent soundness |
| elements_complete_inverse | 683–696 | advanced | Bound=false exclusion under BST |
| elements_correct_inverse | 698–717 | advanced | Default-independent bound witness and absence converse |
| sorted_app | 725–738 | advanced | Separator list-order lemma |
| sorted_elements | 740–755 | advanced | Projected-key sortedness |
| NoDup_append | 775–786 | advanced, optional | Existing nodup/disjointness law adapter |
| elements_nodup_keys | 788–800 | advanced, optional | Key uniqueness |
| fast_elements_eq_elements | 824–840 | standard | Arbitrary accumulator and closed equality |
| kvs_insert_split | 901–915 | optional | Exact separator equation |
| kvs_insert_elements | 917–924 | optional | Enumeration/update compatibility |
| in_fst | 1035–1040 | optional | Projection membership |
| in_map_of_list | 1042–1048 | optional | Unique-key successful binding |
| not_in_map_of_list | 1050–1055 | optional | Missing-key None |
| bound_relate | 1063–1071 | optional | Enumeration decoder |
| lookup_relate | 1073–1079 | optional | Enumeration decoder |
| insert_relate | 1081–1092 | optional | Enumeration decoder |
| union_collapse | 1166–1184 | optional | All three pointwise union laws |
| union_update | 1186–1198 | optional | Both function-level update laws |
| map_of_tree_prop | 1210–1217 | advanced, optional | Raw structural-map property preservation |
| bound_relate' | 1231–1237 | advanced, optional | Direct decoder route |
| lookup_relate' | 1239–1244 | advanced, optional | Direct decoder route |
| insert_relate' | 1246–1251 | advanced, optional | Direct decoder route |
| map_of_list_app | 1257–1263 | advanced, optional | Disjoint-domain decoder union |
| elements_relate' | 1265–1271 | advanced, optional | Decoder coherence |

The eleven commands are `Check` at 383/386, 392/395, 402/406 (paired
tree/Maps empty, same-key, different-key laws), 413, 416, 419 (Maps shadow,
self-update, distinct-update commutation), 612 (`Forall_app`), and `Print` at
766 (`NoDup`). Adapt these to inspected accepted theorem types and actual
Lean list predicates; they require no new mathematical constants. Coq section,
module, notation, hint, and proof-tactic machinery receives an explanatory Lean
adaptation, not an emulation of Coq's metaprogramming system. The lone Abort is
the false enumeration-completeness attempt, whose counterexample is required.

## Efficiency and other prose obligations

Every new count must come from an instrumented actual operation with a proved
value-erasure equation. A theorem about a separately chosen recurrence alone
does not establish the algorithm's work. Keep returned values, comparisons,
tree visits, list-cell copies, and constructor requests distinguishable.

### Search, insertion, and balanced-height assumptions

For every raw tree, bound nonempty nodes visited by its actual `BinaryTree.height`.
Each visited node executes one strict comparison on a left branch and two on a
right/equality branch. Thus the number of comparator calls is at most twice
that height; constructor inspection additionally includes the terminal E when
search misses. Insertion follows the same path and reconstructs its ancestors;
its exact measured result must erase to the source insert. Prove worst-case
linear paths with a concrete skew family and appropriate query, not a claim
that every query in every unbalanced tree is slow.

Logarithmic operation work is conditional on an explicit height bound in terms
of node count and on charged comparator cost. Use log(n+1) or explicit small
cases. No balancing algorithm is present in SearchTree; that guarantee belongs
to later Redblack. A bounded comparator-cost parameter gives a weighted bound;
unary costs depend on key magnitudes and cannot be hidden in a unit comparison
claim. Opening comparisons with linked-list/update-closure maps need their
explicit representations/workloads; an unrestricted function map has no
intrinsic update-history length or expected-case distribution.

The source difference-only claim for unary Nat comparison is inaccurate.
Retain the checked equal-large-operands counterexample and exact recurrence
from the shared unary model. If identifying the instrument with the source
strict comparison, account for its actual recursion/possible successor before
≤; the existing ≤ draft explicitly does not prove that identification. Native
Lean Nat costs remain a separate runtime fact, not the theorem's conclusion.

### Naive versus accumulator enumeration

Establish `length(elements t)=numNodes t` on all raw trees. Instrument both
source append operations in the actual parenthesized node expression, and
record their association and the chosen charges explicitly. For the
right-associated expression `elements l ++ ([(k,v)] ++ elements r)`, charging
one copied cell per append first-list cell yields
`C(E)=0`, `C(node)=C(l)+C(r)+numNodes(l)+1`. Singleton construction and tree
inspection are additional, separately stated charges. If the implementation
normalizes the singleton append to a cons, prove the value bridge and report
that modified recurrence rather than silently transferring literal append cost.

For that literal append-copy model, prove a universal quadratic upper bound
and these sharp contrasting families: a left chain of n nodes has
`C=n*(n+1)/2`; a right chain has `C=n`; a perfect height-h tree has
`n=2^h-1` and `C=h*2^(h-1)` (with h=0 handled explicitly). The latter gives the
linearithmic balanced-family statement; a height-based bound can cover other
specified balanced families. These are future theorem obligations derived from
the stated model, not compiler-checked results of this plan.

The accumulator traversal creates exactly one result-list cons per internal
node and examines every internal node/empty child once, so require its model's
`numNodes` cons count and `2*numNodes+1` constructor-visit count independently
of accumulator length. It returns the untouched accumulator suffix in the
value model. The nested call on r is evaluated before the call on l can use its
result; the source's word “tail-recursive” does not prove constant stack space.
Any stack or physical sharing/allocation/GC statement requires an additional
execution/heap model and realization assumptions. None follows from list equality.

### Mathematical specification and execution boundary

Preserve the chapter's demonstration that correctness transfers from a simple
enumerator to its extensionally equal optimized enumerator: connected clients
must invoke the public equivalence theorem. Explain that algebraic and
model-based methods place proof obligations differently; they are not axioms
or a general theorem equating author effort. Correct the lookup commuting
diagram's codomain informally: `find` returns V after applying a default; an
unjustified extra `Some` arrow must not become the formal contract.

Pure source equations establish that the old value remains available after an
update. They do not certify pointer identity, physical mutation behavior, native
runtime or extracted compiler code. The book's extraction discussion routes
its executable demonstrations and primitive assumptions to #1011 Extract;
SearchTree's own operations must nevertheless be executable with Nat keys and
ordinary payload examples. No extraction axiom or native-decide proof shortcut
is introduced. Formal cost models are possible in Lean; the prose observation
that the source does not internally model runtime is a scope statement, not an
impossibility theorem.

## Checked applications and statement review

Grow the implementation with the existing example-driven workflow, retaining
independently expected outcomes and then connecting them through public laws.
These cases cover consequences, not a per-theorem example quota:

- The complete source ex_tree construction, present/absent lookups, bound result,
  BST proof, and inorder result; also key 0 and a same-key replacement.
- Source NotBst.t and its failed lookup, with explicit non-BST proof; verify a
  raw lookup-after-insert theorem still applies to this malformed input.
- An explicit binding to the chosen default versus E: same total observations,
  different bound bits/partial maps/elements. Use this to refute broken
  completeness and the converse of bound_default.
- Two inserts of one key: structural latest-write equality and the common
  observational client. Distinct keys inserted in opposite orders: different
  roots, identical partial-map observations and, once BST validity is shown,
  identical canonical inorder lists.
- A duplicate-key raw list with two different values: a shadowed member does
  not determine `map_of_list`; demonstrate why in_map_of_list needs key nodup.
- A raw tree with key 0 present in both children of a root at key 1: Abs's
  inorder head binding survives, whereas Abs' cancels the two child bindings.
  This witnesses the need for BST in decoder agreement; also retain the
  correct behavior on valid counterparts.
- All four union branches, including equal-valued Some/Some cancellation;
  retain a failed update-law case when the absence premise is omitted.
- A nonempty accumulator enumeration case consuming the arbitrary-accumulator
  theorem; transport at least one membership/order client through equality.
- A tree instance and the accepted function/association-list instance of the
  shared two-write table client. Prove the tree laws with `Valid=True` for
  raw lookup, and establish BST separately for enumeration clients. A payload
  specialization that does not require an order/equality instance checks the
  intended assumption boundary.
- Empty/singleton, left-chain, right-chain, and perfect-tree measured cases
  connected to public erasure/count results, with the comparison and append
  model explicitly named. No measured count is presented as wall-clock timing.

Review quantifier order, lookup/write direction, default scope, key rather than
pair nodup, strict versus non-strict order, all-node versus path observations,
and independent-universe constraints. Keep source equations on every raw input
where valid. Check satisfiability with E and insertion preservation rather than
closing claims under impossible invariants. Any stronger reusable theorem must
retain the exact source specialization and must not hide absent binding data.

## Implementation order and acceptance gates

After #1008 acceptance, record that exact baseline, recheck the accepted Maps
and sorting API names, and use the existing implement/example-driven loop:

1. Tree constructor adapter, source operations, source examples, all-node/BST
   predicates, validity preservation and unconditional raw lookup/bound algebra.
2. Observational client reuse and both structural counterexamples; naive
   enumeration, soundness/completeness with their distinct assumptions,
   strict order, source sortedness and key nodup.
3. Accumulator enumerator and arbitrary-suffix equality; exact kvs_insert and
   separator/update enumeration equations.
4. Head-wins list decoder, finite observed support, first abstraction laws,
   union laws, direct structural abstraction laws, and final decoder coherence
   and canonical-enumeration consequence.
5. Actual measured operation/append/traversal runs with erasure, explicit
   bounds and contrasting families; all substantive prose qualifications and
   connected cross-application examples. Complete the source coverage map.
6. Integrate every module into the public entrypoint. Preserve source/license
   provenance and complete statement review. Capture the clean candidate and
   run the unchanged required Nix `./check.sh --candidate HEAD` in isolation,
   using fresh mode only when repository policy actually requires it. Retain
   its matching success record and complete audit evidence.
7. Run the README-required proof-audit regression with its managed ProofAudit
   build prerequisite when needed. Both independent Standards/Spec axes must
   pass on the same candidate and complete requirements. Root runs
   `./check.sh --verify-candidate HEAD` immediately before acceptance, confirms
   delivered source equality, records local closure, and immediately creates,
   restore-verifies, exposes and uploads the recovery checkpoint.

Only then may ADT implementation start. Planned obligations, staged shared
drafts, selected compilation results and positive small cases cannot replace
the chapter's complete proof, integration, audit and review gates.

## Inspected input hashes

Paths below are relative to the workspace; these hashes pin the inspected
providers, not a new validation certificate. The running candidate was not
modified. The plan is the only file written for this assignment.

| Input | SHA-256 |
| --- | --- |
| `work-state/source/TREE-INVARIANT-REUSE.md` | `b7078b4a213b2a37035fa25531245749eeed411ff767aa8956a71678efe614db` |
| `work-state/source/COMPUTATIONAL-ASSUMPTIONS.md` | `eb4e8eb1cc4d04f6fe536e87622c4943d6af160b555e7ae4266979484f3eca30` |
| `work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `work-state/staging/table-specs/TableObservations.lean` | `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57` |
| `work-state/staging/unary-costs/UnaryComparisonCosts.lean` | `997aa73ce69fe65712ba97a1217909a6f7af8c2d00e7e2978a4ca03a18c01c13` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Tree/Basic.lean` | `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Tree/Get.lean` | `773d67e99f76e26c96e2d718d88203396fdacba3506d2e42476823440e5aa4bd` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/List/Nodup.lean` | `dd189100bddbb41c32991672a727d0a3ebc41e7243f390cfa25c348eb0520432` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/List/Sort.lean` | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |
| `conaled/.lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean` | `ff4855cf0c959870c20a4ade8c2d0025f24a5088218e4bd715346332597cd64d` |
| `conaled/Applications/Sorting/Stable.lean` | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| `conaled/Applications/Resources/TreeFlattening/Core.lean` | `e9d7610efc7120ca846412f8b951c0c59a6cdfd840af0432222fba95cfed9ce2` |
| `conaled/Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `conaled/Applications/Resources/Growth.lean` | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
