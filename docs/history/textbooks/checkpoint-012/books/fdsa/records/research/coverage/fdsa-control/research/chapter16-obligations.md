# Chapter 16: Priority Queues via Braun Trees — exact source inventory

Research date: 2026-11-02. Local ticket: `FDSA-016`.

**State: queued; source preparation only.** This note changes no Lean source,
build, ticket, acceptance state or remote object. Chapter 1 remains the active
sequential chapter. A row identifies a future checked obligation or reuse
bridge; it does not certify formal coverage.

## Source pins and chapter boundary

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 16, printed pp. 191–193, with p. 194 blank (PDF pages 197–200), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Direct companion | <https://isa-afp.org/browser_info/current/AFP/Priority_Queue_Braun/Priority_Queue_Braun.html>. This mutable browser URL is pinned through the archive below. |
| AFP entry | Tobias Nipkow, *Priority Queues Based on Braun Trees*, published September 4, 2014: <https://isa-afp.org/entries/Priority_Queue_Braun.html>. Reading-copy HTML SHA-256 `3b042b6c407a78a1de96772f08269ca5aa603267c8820abd68c5100d15b8a074`. The entry identifies the BSD license and a second deletion version added in 2019. |
| Dated archive | <https://isa-afp.org/release/afp-Priority_Queue_Braun-2026-10-26.tar.gz>, SHA-256 `e6f6b1a8f08b001fd08d39adda0fb2f5ef5581e2294273bf54b03fe13497a72b`. It postdates the book and targets Isabelle2026; correspondence was inspected, not presumed. |
| Main theory | Extracted `Priority_Queue_Braun.thy`, 10,740 bytes, SHA-256 `2737d31cd0c32ac2d74bf46829faf6e9f740696d2c3b3f3c6cdea075a89e9f6e`. Full file inspected, including all definitions, contracts and time bounds. |
| Shared Isabelle sources | Revision `f86f290225eebcc52c1ae7dba2e098f405f51c21` of <https://github.com/isabelle-prover/mirror-isabelle>. `src/HOL/Data_Structures/Braun_Tree.thy`, SHA-256 `c6821391fce3c471e20d733d93cee8e7ba6d942edc87d51cf897817efac29db1`; `Priority_Queue_Specs.thy` in the same directory, SHA-256 `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a`. Chapter 11 owns Braun foundations; Chapter 14 owns the heap/multiset interface. |
| Licensing | AFP BSD-3-Clause terms at <https://isa-afp.org/LICENSE>, local SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`; Isabelle COPYRIGHT SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Retain applicable notices when adapting source. |
| Reuse baseline | conaled `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Relevant Lean/library sources carry Apache-2.0 notices. |

The book has **no exercises in this chapter**. Coverage is the four source
operations, their helper algorithms, every correctness result, all three
displayed helper time bounds, the deletion height lemma, Lemma 16.1 and the
resulting logarithmic bounds. The AFP archive's `Priority_Queue_Braun2` and
`Sorting_Braun` are additional developments; their presence does not turn this
chapter into a request to port every file in that archive. The chapter credits
the algorithm to Paulson, who credits Okasaki; this attribution is preserved
without importing additional algorithms from those publications.

Reading copies and chapter extraction remain under `book-source/`; the
manuscript is not included in this original note. A scoped scan for admission
markers is useful evidence only; no Isabelle or Lean build is asserted here.

## Definitions, domains and reuse

Write `E` for the empty leaf, `N l a r` for a node, `n(t)` for the count of
labelled nodes, `h(t)` for height and `M(t)` for its element multiset. `B(t)`
is exactly Chapter 11's Braun predicate:
`B(N l a r) ↔ B l ∧ B r ∧ (n l=n r ∨ n l=n r+1)`.
`H(t)` is Chapter 14's min-heap predicate: every ancestor is at most every
value in its descendant subtrees. Queue validity is the **conjunction** `B∧H`.
All payload comparisons use the book's lawful linear order; multiplicities
are preserved, including repeated equal minima.

Use Mathlib's existing `BinaryTree α`, shared Braun/heap/multiset observations,
and Chapter 14's exact multiset priority-queue contract. The conaled
`Search.LeftistQueue` algorithms are different: cached minimum-depth ranks,
right-spine merge, and rank-based child swapping are not Braun balance or
this insertion/deletion recurrence. Its independent occurrence observation
and optional empty-deletion conventions are useful patterns.

The existing `Search.PriorityInterface.ExactQueue` / `ExactLaws` in
`Applications/Search/ExactPriority.lean` is the appropriate shared interface:
`add_exact` preserves the full occurrence list up to permutation,
`remove_none` characterizes emptiness, and `remove_spec` proves exact
one-occurrence removal, leastness and validity. A Braun realization still
needs the source single-insert, separate root minimum and multiset bridges;
extracting a minimum by executing deletion would lose constant-time lookup.
The weaker keyed `Queue` intentionally permits replacement and is insufficient
by itself. Reuse the exact interface and Chapter 14's adapters rather than
introducing a duplicate hierarchy. Chapter 16 supplies no merge operation.

Follow `fdsa-control/DECISIONS.md`: `get_min E` and `del_left E` are
underspecified source calls and should use explicit valid domains or the
established `Option` convention. A global `Inhabited α` is not justified.
For `sift_down`, the displayed equations have wildcard/omitted invalid-shape
cases. Braun validity of the assembled parent supplies the intended domain;
retain that domain and prove recursive closure. An explicit optional or
proof-domain realization is preferable to inventing a payload or claiming
unrestricted multiset preservation.

## 16.1 Algorithms: pp. 191–192

| ID | Source obligation | Exact recurrence, domain and reuse |
|---|---|---|
| C16-001 | Shared `empty=E`, `is_empty(t)=(t=E)`, root `get_min`, multiset `M`, heap `H`, and validity `B∧H`. | Reuse Chapters 11 and 14, preserving their exact definitions. `is_empty` is a constructor check, not a traversal or size recomputation. |
| C16-002 | `get_min(N l a r)=a`. On a nonempty heap this is the least element of `M(t)`. | Companion `get_min`, lines 42–46. Minimum correctness needs `H` and nonemptiness; returning the root value itself does not need Braun validity. |
| C16-003 | `insert a E=N E a E`. | No cached rank or size is stored. The new tree is both Braun and a heap. |
| C16-004 | `insert a(N l x r)` is `N (insert x r) a l` when `a<x`, otherwise `N (insert a r) x l`. | Both branches recurse into the **old right** child and make the old left child the new right child. Equal values take the second branch; preserve strict `<` rather than silently using `≤`. |
| C16-005 | `del_min E=E`; `del_min(N E x r)=E`; otherwise extract `(y,l')=del_left l` and return `sift_down r y l'`. | The second raw equation discards `r`; valid Braun shape forces it empty. In the third case `l≠E`, and the sibling order passed to sift is deliberately swapped. |
| C16-006 | `del_left(N E x r)=(x,r)`. Otherwise on `N l x r`, recursively obtain `(y,l')=del_left l` and return `(y,N r x l')`. | Base permits arbitrary `r`, without Braun validity. The recursive call is on nonempty old `l`, and its returned remainder is swapped with old `r`. This removes a leftmost value, not the root or the numerical array's last index. |
| C16-007 | `sift_down E a r=N E a E`. | Source wildcard discards `r`; the intended assembled-parent Braun premise implies `r=E`. Do not replace the premise by an unqualified heap-only condition. |
| C16-008 | `sift_down(N E x r) a E` compares `a≤x`: return `N (N E x E) a E` if true, otherwise `N (N E a E) x E`. | Intended Braun domain forces the wildcard `r=E`. Tie keeps candidate `a` at the root. |
| C16-009 | On two nonempty children `t₁=N l₁ x₁ r₁`, `t₂=N l₂ x₂ r₂`, if `a≤x₁ ∧ a≤x₂`, return `N t₁ a t₂`. | No recursive call in this branch. Boolean conjunction may short-circuit; the source's recursive-call cost model does not count each comparison separately. |
| C16-010 | Otherwise, if `x₁≤x₂`, return `N (sift_down l₁ a r₁) x₁ t₂`; else return `N t₁ x₂ (sift_down l₂ a r₂)`. | Equal child roots select the left child. Recurse into the selected child's **two children**, retaining the other whole subtree. |
| C16-011 | Both missing/wildcard shape issues are discharged by `B(N l a r)` and its recursive subtree facts. | In particular, a left node with a nonempty left child paired with empty right tree is outside the intended domain. Establish dependent/optional function coverage and recursive domain preservation instead of treating omitted cases as a proved total specification. |
| C16-012 | Termination of sift via `max(h l,h r)`; alternatively `n l+n r`. | Both decrease on recursive branches; the height measure also supports a sharp invocation bound. Source main theory lines 119–127 supplies the well-founded termination proof. Do not infer running-time bounds solely from semantic termination. |

## 16.2 Correctness: pp. 192–193

| ID | Source obligation | Exact hypotheses and supporting source |
|---|---|---|
| C16-013 | `n(insert x t)=n(t)+1`. | `size_insert`; arbitrary raw trees, no heap or Braun hypotheses. |
| C16-014 | `M(insert x t)={x}+M(t)`. | `mset_insert`; arbitrary raw trees, exact one-occurrence addition. A set-only theorem would lose multiplicity. |
| C16-015 | `B t → B(insert x t)`. | `braun_insert`; size changes plus swapping preserve the left-equal-or-one-larger condition. Heap validity is unnecessary here. |
| C16-016 | `H t → H(insert x t)`. | `heap_insert`; Braun validity is unnecessary. Prove these two invariants separately before combining them. |
| C16-017 | If `del_left t=(x,t')` and `t≠E`, then `M(t)={x}+M(t')`. | `del_left_mset_plus`; no heap/Braun premise. Optional formulation must also show success on nonempty trees. |
| C16-018 | Consequences: extracted `x` is in `M(t)`, `M(t')=M(t)-{x}`, and the tree-value set decomposes as `{x}∪set(t')`. | `del_left_mset`, `del_left_set`. These supply occurrence removal and descendant-bound preservation. |
| C16-019 | Same extraction/nonempty hypotheses plus `H t` imply `H t'`. | `del_left_heap`; no Braun premise. |
| C16-020 | Equation (16.1): same extraction/nonempty hypotheses imply `n(t)=n(t')+1`. | `del_left_size`; no heap/Braun premise. |
| C16-021 | Equation (16.2): same extraction/nonempty hypotheses plus `B t` imply `B t'`. | `del_left_braun`; size decrement and child swapping are both essential. |
| C16-022 | `B(N l a r) → n(sift_down l a r)=n l+n r+1`. | `size_sift_down`; requires the assembled Braun shape because invalid wildcard inputs can lose nodes. No heap premise. |
| C16-023 | `B(N l a r) → B(sift_down l a r)`. | `braun_sift_down`; does not require root candidate `a` to satisfy heap order. |
| C16-024 | `B(N l a r) → M(sift_down l a r)={a}+M(l)+M(r)`. | `mset_sift_down`; no heap premise, exact multiplicities. Its set-image corollary is companion `set_sift_down`. |
| C16-025 | `B(N l a r) ∧ H l ∧ H r → H(sift_down l a r)`. | `heap_sift_down`; the candidate `a` is arbitrary, so do not assume the assembled tree is already a heap. |
| C16-026 | If `B(N l x r)`, `l≠E` and `del_left l=(y,l')`, then `B(N r y l')`. | Explicit domain bridge used by deletion: `n l=n r` or `n r+1`, while `n l=n l'+1`; therefore `n r=n l'` or `n l'+1`. Preserve both child Braun predicates. |
| C16-027 | `B t → B(del_min t)`. | `braun_del_min`; includes empty and singleton trees. |
| C16-028 | `H t ∧ B t → H(del_min t)`. | `heap_del_min`; use heap-preserving left extraction and sift. No nonempty assumption needed for invariant preservation. |
| C16-029 | `B t ∧ t≠E → M(del_min t)=M(t)-{get_min t}`. | `mset_del_min`; **heap validity is absent**. The raw root-removal multiset theorem is true even if the root is not least; minimum correctness adds `H` separately. |
| C16-030 | Supporting size theorem `B t → n(del_min t)=n(t)-1`, including empty natural subtraction. | Companion `size_del_min`, lines 176–183; useful for repeated removal/resource clients and exact nonempty behavior. |
| C16-031 | All eight Chapter 14 `Priority_Queue` laws hold with validity `B∧H` and observation `M`. | Source interpretation `braun`, lines 206–227. Include empty multiset, emptiness reflection, exact insertion, nonempty deletion/minimum, and all three invariant laws. This chapter does not supply a Braun `merge` implementation or `Priority_Queue_Merge` instance. |

## 16.3 Running time: p. 193 and Appendix B.6

The source's functions count selected recursive function calls. Comparisons,
constructor formation, projections, parity-independent arithmetic and
nonrecursive wrapper work have the source's primitive tariff. In particular
`del_min` has **no extra wrapper tick**, and its two trivial branches cost
zero. Appendix B owns the normalized recurrences B-036–038; the chapter owns
their actual value connection and bounds. Do not replace this tariff by
allocation count, comparisons or total machine instructions.

| ID | Source obligation | Exact recurrence or bound |
|---|---|---|
| C16-032 | `T_insert a E=1`; on a node, selected recursive call into old right child plus 1. | Measured-value erasure must return the actual `insert` result, including value comparison branch and child swap. Source `time_fun insert`, lines 232–236. |
| C16-033 | `T_insert a t≤h(t)+1` for every raw tree. | Companion `T_insert`. No Braun/heap premise; logarithmic specialization uses Braun later. Optional stronger bridge: exact count is right-spine length plus 1. |
| C16-034 | `T_del_left(N E x r)=1`; on a node with nonempty left child, recursive `T_del_left l+1`. Empty call has no specified source result. | B-037. Use valid input or optional failure; do not insert a fabricated payload into the empty case. |
| C16-035 | Equation (16.3): `t≠E → T_del_left t≤h(t)`. | `T_del_left_height`, no heap/Braun premise. The exact count is left-spine node length, which Chapter 11 Exercise 11.2 identifies with height on Braun trees. |
| C16-036 | `T_sift_down` costs 1 in its two displayed base cases and the no-descent branch; recursive two-node branches cost selected recursive sift plus 1. | B-038. Use the actual comparison branch; comparisons themselves are not separately charged in this recurrence. |
| C16-037 | Equation (16.4): `B(N l a r) → T_sift_down l x r≤max(h l,h r)+1`, for arbitrary candidate `x`. | `T_sift_down_height`, lines 249–252. Braun shape ignores payload labels, so the premise's `a` and actual candidate `x` need not agree. No heap assumptions. |
| C16-038 | Equation (16.5): if `del_left t=(x,t')` and `t≠E`, then `h(t')≤h(t)`. | `del_left_height`, lines 256–257; no heap/Braun premise. It prevents the intermediate remainder from increasing the sift bound. |
| C16-039 | `T_del_min E=0`; `T_del_min(N E x r)=0`; on `l≠E`, obtain the actual `(y,l')=del_left l` and use `T_del_left l+T_sift_down r y l'`. | B-036 and `T_del_min_neq_Leaf`, lines 259–261. The tuple value comes from one real extraction; do not charge an extra extraction or an added wrapper call. |
| C16-040 | Lemma 16.1: `B t → T_del_min t≤2·h(t)`. | Companion `T_del_min`, lines 263–290. Prove the intermediate assembled Braun domain C16-026 before applying sift's time bound. The printed final proof line is incomplete; corrected arithmetic is below. |
| C16-041 | On a nontrivial deletion branch, with `q=max(h l,h r)`, the proof gives `T_del_min t≤h l+q+1≤2q+1≤2(q+1)=2h(t)`. | Uses extracted-height nonincrease and the exact source tariff. No induction hypothesis on `del_min` is actually needed; source proves the theorem by cases. |
| C16-042 | Braun specialization yields `T_insert≤ceil(log₂(n+1))+1`, `T_del_min≤2·ceil(log₂(n+1))`; minimum and emptiness observations are constant-time root/constructor operations. | Reuse Chapter 11's height theorem, including empty tree `n=0`. These are worst-case upper bounds under the stated abstract model, not an assertion every call takes logarithmic time. |
| C16-043 | The height measure for sift is sharp as a worst-case invocation bound. | A concrete family: both arguments complete heaps of height `q` with all labels 0, candidate 1. Each nonbase call descends through the left selected child, so count is `q+1`. By contrast a candidate already below both roots stops immediately. This supports the prose's “tight” claim without claiming a matching lower bound on every input. |

## Source defects and explicit boundary witnesses

| ID | Location or boundary | Disposition |
|---|---|---|
| C16-044 | Lemma 16.1 proof, p. 193: prose says the call of `del_min` must yield a pair, immediately displaying `del_left l=(y,l')`. | The pair-producing function is `del_left`, while `del_min` returns a tree. Correct this local function-name error; do not change operation types. |
| C16-045 | Final proof line on p. 193 ends with an upper bound `2·h(t)+1`, although the lemma claims `2·h(t)`. | The final displayed bound is true but does not finish the stated theorem. Since `h(t)=max(h l,h r)+1`, the previous quantity `2·max(h l,h r)+1` is already at most `2·h(t)`. Companion lines 284–287 explicitly make that stronger final step. Retain the original lemma and the corrected derivation; no weakening to `2h+1` is necessary. |
| C16-046 | Wildcard base case without Braun domain can discard contents. | Example `sift_down E 1 (N E 2 E)=N E 1 E`, so unconditional multiset preservation is false. Likewise `del_min(N E 1 (N E 2 E))=E` discards both labels on a non-Braun input. Check these small witnesses alongside the conditional laws. |
| C16-047 | Calling the root `get_min` does not make it a minimum without heap validity. | `N (N E 0 E) 1 E` is Braun but not a heap; root is 1 while true multiset minimum is 0. C16-029 still correctly removes one root occurrence. Preserve the separate contracts instead of strengthening every lemma to full queue validity. |
| C16-048 | Existing Chapter 11 array operations have different payload behavior. | A Braun heap insertion may replace the root and push the old value down; array `add_lo` simply installs a new first element. `del_left` extracts a leftmost payload with swaps, whereas array `del_lo` removes the root and rearranges children. Share shape/arithmetic lemmas, not unproved operation equalities or costs. |

The numerical proof correction is an arithmetic repair of an incomplete
printed step, not a counterexample to Lemma 16.1. The raw-tree examples expose
genuine false **unconditional extensions**, not errors in the source's
conditional theorems. They should become checked examples; this inventory
alone does not certify them.

## Handoff

Reuse Chapter 11's Braun predicate and Chapter 14's heap/multiset/PQ interface
on `BinaryTree α`. Preserve strict/non-strict tie directions and all swaps.
Implement the nonempty extraction and assembled-Braun sift domains explicitly;
prove value, size, heap and Braun properties separately at their original
strength. Connect B-036–038 to the actual branches, retain zero-cost trivial
`del_min` cases, and finish the corrected `2h` proof plus logarithmic
specialization. Complete exact occurrence examples, equal-priority cases and
the invalid-domain counterexamples before chapter review. All 48 rows are
queued obligations or shared integration requirements.
