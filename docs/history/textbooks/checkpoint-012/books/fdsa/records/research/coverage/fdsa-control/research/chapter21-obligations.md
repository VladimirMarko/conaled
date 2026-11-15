# Chapter 21: Splay Trees — source obligations and reuse

Prepared 2026-11-02. Local chapter handle: `FDSA-021`.

**State: queued; source preparation only.** This note covers printed
pp. 245–252 in the pinned July 27, 2026 book, including every algorithm
branch, the unnamed rotation question, all correctness and amortized
claims, Exercise 21.1, and the stated static-optimality result. The dynamic
optimality conjecture remains an explicitly unproved conjecture statement.
No Lean, Git, ticket or acceptance state was changed; no build or new
implementation/review loop was run.

## Sources and exact pins

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 21 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; PDF pp. 251–258. Rotation diagrams and the proofs on printed pp. 245, 250–251 were visually inspected. |
| Direct companion entry | <https://isa-afp.org/entries/Splay_Tree.html>; direct implementation link <https://isa-afp.org/browser_info/current/AFP/Splay_Tree/Splay_Tree.html>. |
| Fixed implementation archive | <https://isa-afp.org/release/afp-Splay_Tree-2026-10-26.tar.gz>, SHA-256 `4c9b4a9fd24a63ba40eb5a357e2d8469d32eb437173018213bff2232f6dfd2f6`. `Splay_Tree.thy` SHA-256 `1f922b404850d90b4fee6345577c945e297948dde7efe03e58886ed3df24beab`. |
| Direct analysis link | <https://isa-afp.org/browser_info/current/AFP/Amortized_Complexity/Splay_Tree_Analysis.html>. |
| Fixed analysis archive | <https://isa-afp.org/release/afp-Amortized_Complexity-2026-10-26.tar.gz>, SHA-256 `d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a`. Supporting snapshot later than the manuscript. |
| Main analysis files | `Splay_Tree_Analysis_Base.thy`: `3f8cc3fd475bf40bed0eff7f2442370eb326e140c90e66600fea220fc22cfe17`; `Splay_Tree_Analysis.thy`: `fd6ac8ae8b48e18e4dc8622e49f527ea7ce7fa8fa557f2af4231fd90e268f012`; `Lemmas_log.thy`: `efac8b7ffdbdad1cdc9a825475d9a0ac9558025a092fcfd02f6b8881e2be8d41`. |
| Differently scoped analysis | `Splay_Tree_Analysis_Optimal.thy`: `511162539e9b8cab7bf804db673c82d2d534d6365098cc81525914506df0b73d`. Its parameterized potential improves the logarithmic coefficient; despite its name it does **not** prove access-frequency static optimality. |
| Shared Isabelle support | `f86f290225eebcc52c1ae7dba2e098f405f51c21`: `Tree.thy`, `Cmp.thy`, `Set_Specs.thy`, `Sorted_Less.thy`, `List_Ins_Del.thy`, `Tree_Rotations.thy`. Their paths/hashes and precise strict-order semantics are recorded in Chapters 4–5 inventories. Raw URLs are the fixed mirror revision plus those source paths. |
| Source licenses | AFP theories BSD-licensed, shared license SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`; Isabelle support BSD-3-Clause, copyright file SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Retain applicable notices. |
| Static-optimality primary paper | Sleator and Tarjan, *Self-Adjusting Binary Search Trees*, JACM 32(3), 652–686, 1985; author's copy <https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf>. Reading-copy SHA-256 `33fe18c5aec145c30bd32fe155d05e25ffa9999f043c3422d0ea66de6ce14364`, 6,073,769 bytes. Theorem 2, printed p. 659, and variant discussion on pp. 665–670 were inspected. This paper is copyrighted ACM material, not part of the AFP BSD license and not a manuscript deliverable. |
| Lean reuse | Inspected conaled `1aabd512284fe86254278ac631eda061d311050b`; relevant existing infrastructure already at `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`, Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. |

The active implementation/correctness declarations and the main amortized
analysis were read. A scoped scan of the five splay/log files found no
`sorry`, `oops`, `axiomatization` or `admit`; no Isabelle build/proof audit
is claimed. The implementation file also contains an older commented-out
proof approach; commented text is not an additional checked theorem.

## Reuse, semantic domains and actual costs

Write `E` for empty and `N(l,a,r)` for a node. Let `n(t)` count labelled
nodes and `ell(t)=n(t)+1` count empty leaves. Here, unlike Chapter 2,
`sorted` means **strict** pairwise `<`; `bst` forbids duplicate keys.
`subtrees t` means actual structural subtrees, including the whole tree and
empty leaves, not arbitrary trees with a subset of the same keys.

| Existing API or earlier chapter | Exact reuse or missing correspondence |
|---|---|
| Mathlib `BinaryTree α` | Correct empty-leaf/node-labelled carrier. Lean constructor order is `node a l r`; do not introduce a second splay-tree datatype. |
| `BinaryTree.numNodes`, `numLeaves`, `height`, `numLeaves_eq_numNodes_succ`, `numLeaves_pos` | Exact structural observations and positivity for logarithms. None proves a balance invariant for splay trees. |
| Chapter 4 inorder/subtree foundation | Shared prospective traversal and structural-subtree facts. These are queued obligations, not existing accepted Lean code. |
| Chapter 5 strict BST and set contracts | Share strict sortedness, set observation, duplicate-suppressing sorted insertion, first-occurrence deletion, rotations and lawful comparison. `List.orderedInsert` retains duplicates and is not the source `ins_list`. |
| `List.Pairwise`, `List.erase`, append/list membership | Standard strict-order and deletion support. `List.erase` correspondence needs the chosen equality capability and the source first-occurrence behavior; set deletion then uses no duplicates. |
| Standard `Ordering` and lawful comparator machinery | Reuse the three outcomes. Structural rearrangement/size/inorder facts can be separated from comparison laws; BST membership and update correctness require comparison agreement with the strict order. |
| `Resources.Measured`, `bind`, `reweight`, erasure squares | Reuse actual splay execution with a natural call count and explicit cast to real for potential inequalities. An output-only replacement algorithm does not preserve this count. |
| `Resources.run`, `run_state`, `run_invariant`, `run_value_fusion` | Existing trace composition and observation/invariant transport. A membership client must thread the **returned reorganized tree** through the trace. |
| `Resources.Potential` and Chapter 19 extension | Existing natural potential theorems do not directly express real logarithmic potentials. Reuse the signed/real invariant-aware telescoping work once available; avoid a separate splay-specific accounting framework. |
| `Real.logb` in `Mathlib/Analysis/SpecialFunctions/Log/Base.lean` | Use base 2 directly. `logb_one`, `logb_self_eq_one`, `logb_nonneg`, `logb_le_logb_of_le`, `logb_lt_logb`, `logb_mul`, `logb_pow` supply the inspected exact algebra/monotonicity APIs. Positivity of arguments and `1<base` are explicit. |
| `Finset.sum_range_sub` | Standard additive telescoping after the actual state path is fixed; relevant generated declaration is documented in Chapter 19. |
| Existing conaled search structures | Scoped word-boundary search found no integrated splay execution in `Applications`, `SquareKit` or `Examples`. Leftist priority queues and leaf-labelled random-access trees are different carriers/algorithms; only their resource-composition patterns are reusable. |

The source computes `splay` and `splay_max` on every raw tree, with no BST
premise on execution or termination. A nonempty guarded recursive call
cannot return empty; establish that fact instead of adding an arbitrary
payload default for its partial HOL pattern. The shape-only `splay_max`
laws need no order on payloads. Source typeclass assumptions on an entire
locale/file need not become global hypotheses on each Lean lemma.

Appendix B.9 counts recursive entries. `Tsplay E=1`, but a guarded absent
grandchild costs **zero additional recursion**; it must not become an
unconditional call to `splay E`. Comparisons and rotations are uncharged
nonrecursive work in that tariff. Insertion and deletion wrappers add no
tick. Later comparison/rotation/machine-cost claims require explicit
correspondence, not just the same resulting inorder list.

## Introduction, rotations and the informal question: pp. 245–246

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-001 | Splay trees use the ordinary binary-search-tree carrier, with a restructuring search rather than stored balance data. | Reuse `BinaryTree` and strict Chapter 5 BST observation. |
| C21-002 | Splaying brings a present query, or the last visited key of an unsuccessful search, to the root. | Separate successful and unsuccessful properties; deletion subsequently removes the queried key, so the introduction's root claim describes its splay phase, not the final deletion result. |
| C21-003 | Splay trees can have linear height; logarithmic access guarantees are amortized rather than per-call worst-case balance. | Exercise 21.1 and an actual search-cost witness below. |
| C21-004 | The stated comparison with static search trees is a mathematical theorem claim, not discharged by ordinary logarithmic amortization. | Retain C21-098–101 with its frequency, initial-state and cost-model assumptions. Hot-key motivation is interpreted through this theorem, not as a universal empirical speed claim. |
| C21-005 | Left zig-zig maps `N(N(N(A1,x',A2),a,B),b,C)` to `N(A1,x',N(A2,a,N(B,b,C)))`. | Exact diagram; unconditional structural inorder preservation and label-count preservation. |
| C21-006 | Left zig-zag maps `N(N(A,a,N(B1,x',B2)),b,C)` to `N(N(A,a,B1),x',N(B2,b,C))`. | Exact diagram; distinguish subtree positions. |
| C21-007 | Corresponding mirrored rotations handle the two right-side cases. | Reuse the Chapter 4 mirror and Chapter 5 positioned rotations where available; comparator/order duality must be explicit if used to transfer proofs. |
| C21-008 | Unnumbered question: which displayed double rotation is a composition of two root rotations? | Zig-zig is two root `rotR`s. Zig-zag requires `rotL` inside the left child followed by root `rotR`; it is not two root-only rotations. Both are compositions of positioned ordinary rotations, so do not assert that zig-zag is not a composition in that broader sense. |
| C21-009 | Splay recursion terminates because each recursive argument is a proper grandchild subtree. | Structural/well-founded size proof, independent of BST validity. The source uses lexicographic termination. |

## 21.1 Splay implementation: Figure 21.1 and the empty equation

For the left cases write the input as `N(AB,b,CD)` and, if nonempty,
`AB=N(A,a,B)`; for the right cases write `CD=N(C,c,D)`.

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-010 | `splay x E=E`. | Explicit companion equation, omitted from the figure restricted to node input; needed for totality and cost base case. |
| C21-011 | Comparing equal to root `b` returns the whole input node unchanged. | Preserve structural identity in this branch. |
| C21-012 | If `x<b` and `AB=E`, return the input node. | Unsuccessful search stops at this root. |
| C21-013 | If `x<b` and `x=a`, return `N(A,a,N(B,b,CD))`. | Single right rotation. |
| C21-014 | If `x<b`, `x<a` and `A=E`, return the same single-rotation result. | Do not recurse into empty A. |
| C21-015 | If `x<b`, `x<a` and A is nonempty, obtain `splay x A=N(A1,x',A2)` and return `N(A1,x',N(A2,a,N(B,b,CD)))`. | Actual recursive result is used once; its nonemptiness requires proof. |
| C21-016 | If `x<b`, `a<x` and `B=E`, return `N(A,a,N(B,b,CD))`. | Same single rotation, different unsuccessful-search branch. |
| C21-017 | If `x<b`, `a<x` and B is nonempty, obtain `splay x B=N(B1,x',B2)` and return `N(N(A,a,B1),x',N(B2,b,CD))`. | Zig-zag; the recursive subtree is B. |
| C21-018 | If `b<x` and `CD=E`, return the input node. | Right-side unsuccessful-search stop. |
| C21-019 | If `b<x` and `x=c`, return `N(N(AB,b,C),c,D)`. | Single left rotation. |
| C21-020 | If `b<x`, `x<c` and `C=E`, return `N(N(AB,b,C),c,D)`. | No recursive empty call. |
| C21-021 | If `b<x`, `x<c` and C is nonempty, obtain `splay x C=N(C1,x',C2)` and return `N(N(AB,b,C1),x',N(C2,c,D))`. | Mirrored zig-zag. |
| C21-022 | If `b<x`, `c<x` and `D=E`, return `N(N(AB,b,C),c,D)`. | Right-right terminal single rotation. |
| C21-023 | If `b<x`, `c<x` and D is nonempty, obtain `splay x D=N(D1,x',D2)` and return `N(N(N(AB,b,C),c,D1),x',D2)`. | Mirrored zig-zig. |
| C21-024 | All nonempty-result pattern matches are justified for all raw input trees. | Source `splay_Leaf_iff` / `splay_not_Leaf`; use a dependent/nonempty helper or a total equation with an unreachable branch proof, without adding `Inhabited α`. |

## Other operations: pp. 246–248

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-025 | Boolean `isin t x` splays x, then returns false at empty or tests equality with the resulting root. | Exact displayed Set-ADT observer; companion `is_root` and `isin`. |
| C21-026 | A proper amortized membership operation returns both the Boolean and the newly splayed tree. | New connected state-returning client/adaptor, not a replacement of the displayed Boolean value contract. The latter alone discards the potential decrease. |
| C21-027 | Inserting into E produces `N(E,x,E)`. | No splay call is executed in this branch. |
| C21-028 | Otherwise, splay to `N(l,a,r)`; on query/root equality return that node. | Duplicates are suppressed; an insertion may still change shape because the splay already occurred. |
| C21-029 | On `x<a`, insertion returns `N(l,x,N(E,a,r))`. | Requires the query-separation theorem for BST correctness. |
| C21-030 | On `a<x`, insertion returns `N(N(l,a,E),x,r)`. | Symmetric reconstruction. |
| C21-031 | Deleting from E returns E. | No splay call and zero source wrapper cost. |
| C21-032 | Otherwise splay to `N(l,a,r)`; if `x≠a`, return this splayed node. | Failed deletion can change shape while preserving all contents. |
| C21-033 | If `x=a` and `l=E`, deletion returns r. | Removes the queried occurrence/root. |
| C21-034 | If `x=a` and l is nonempty, splay its maximum to `N(l',m,_)` and return `N(l',m,r)`. | Preserve the actual predecessor residual. Prove the ignored right child is empty; do not silently drop an arbitrary subtree. |
| C21-035 | `splay_max E=E`. | Total convenience case; no order capability needed. |
| C21-036 | `splay_max(N(A,a,E))` returns that node. | Existing rightmost node is root. |
| C21-037 | At `N(A,a,N(B,b,CD))` with `CD=E`, return `N(N(A,a,B),b,E)`. | Single left rotation. |
| C21-038 | Otherwise recurse into CD, obtain `N(C,c,D)`, and return `N(N(N(A,a,B),b,C),c,D)`. | Termination by proper right grandchild; the recursive output is nonempty. |
| C21-039 | On nonempty input, `splay_max` has empty right child and root equal to the old rightmost inorder element. | Structural statement can be proved without BST; maximality among labels requires strict BST/order. |

## 21.2 Correctness: pp. 248–249

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-040 | `splay x t=E ↔ t=E`. | Source `splay_Leaf_iff`; no BST premise. |
| C21-041 | `splay_max t=E ↔ t=E`. | Source `splay_max_Leaf_iff`; no order or BST premise is needed. |
| C21-042 | Equation (21.1): inorder of a splayed tree equals old inorder, on all raw trees. | Source `inorder_splay`; rotation/list algebra independent of search-order correctness. |
| C21-043 | If `splay x t=N(l,a,r)` and old inorder is strictly sorted, membership of x in old inorder is equivalent to `x=a`. | Source `splay_elemsD`; strict sorting is material. |
| C21-044 | Strictly sorted inorder implies Boolean isin exactly decides membership. | Source `isin_set`, with the empty case from C21-040. |
| C21-045 | If old inorder is strictly sorted and splay returns `N(l,a,r)`, then `inorder l ++ x::inorder r` is strictly sorted. | Source `sorted_splay`; equivalently left keys are `<x`, right keys are `>x`, even if x was absent. |
| C21-046 | Under strict sortedness, insertion's inorder is `ins_list x (inorder t)`. | Source `inorder_insert`; reuse Chapter 5's duplicate-suppressing sorted-list insertion, not duplicate-retaining insertion sort. |
| C21-047 | If `splay_max t=N(l,a,r)` and inorder is strictly sorted, `inorder l ++ [a]=inorder t` and `r=E`. | Source `inorder_splay_maxD`. The structural inorder/right-empty part admits a weaker assumption; maximality and order consequences need sorting. |
| C21-048 | Under strict sortedness, deletion's inorder is `del_list x (inorder t)`. | Source `inorder_delete`; first-occurrence list erase and strictness give set deletion. |
| C21-049 | Splay, insertion and deletion preserve strict BST validity. | Source `bst_splay`, `bst_insert`, `bst_delete`; source `splay_bstL`/`splay_bstR` provide useful query-separation consequences. |
| C21-050 | Empty, membership, insertion and deletion instantiate the Set ADT via inorder, with no extra balance invariant. | Source `splay: Set_by_Ordered`; reuse the queued Chapter 5/6 representation composition. |
| C21-051 | Splaying preserves node count, hence leaf count. | Source `size_splay`, `size_if_splay`, standard `numLeaves_eq_numNodes_succ`. |
| C21-052 | Splay-max preserves node count, hence leaf count. | Source `size_splay_max`, `size_if_splay_max`; no BST premise. |
| C21-053 | In an unsuccessful nonempty search, the final root is the last node encountered by ordinary BST search. | Preserve this unnumbered semantic characterization, not just existence of some equivalent present key. A search-path/last-visited relation from Chapter 5 or a focused proof relation is needed. |
| C21-054 | Strict-list reasoning supports replacing a final element by a greater one or an initial element by a smaller one, and insertion/deletion at ordered boundaries. | Exact primary helpers `sorted_snoc_le`, `sorted_Cons_le`, `ins_list_Cons`, `ins_list_snoc`, `del_list_notin_Cons`, `del_list_sorted_app`; derive from standard `List.Pairwise` rather than porting automation-specific `ASSUMPTION` wrappers. |

## Appendix B.9 execution correspondence and potential: pp. 249–252

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-055 | Empty splay costs 1. | B-049; exact actual measured base case. |
| C21-056 | Every nonrecursive node branch in C21-011–023 costs 1, including equality, empty child and empty guarded grandchild. | `T_splay_simps`; comparisons/rotations have no separate source tick. |
| C21-057 | Each recursive branch costs `1+Tsplay x selectedGrandchild`, with the actual selected nonempty subtree. | Preserve four recursion choices and all empty guards. `time_fun` explicitly uses `splay_code`, not an arbitrary equivalent definition. |
| C21-058 | Splay-max costs 1 at E and at nonrecursive nodes; the nonempty right-grandchild branch costs its recursive call plus 1. | B-050; discharge the nonempty-result residual case before eliminating it. |
| C21-059 | Insertion costs 0 at E and otherwise exactly `Tsplay x t`. | B-051, primary `T_insert_simp`; no wrapper tick. |
| C21-060 | Deletion costs 0 at E; otherwise pays splay, then additionally splay-max on the **actual resulting** left child only when root matches and that child is nonempty. | B-052; thread values through the measured computation. |
| C21-061 | Each measured operation erases to the exact value algorithm and has the above recurrences on the source domain. | Missing measured splay library; abstract cost recurrences detached from another implementation do not establish coverage. |
| C21-062 | `Phi E=0`; `Phi(N(l,a,r))=phi(N(l,a,r))+Phi l+Phi r`. | New real tree observation, separate from executable representation and cached sizes. |
| C21-063 | `phi t = log₂ ell(t)`. | Reuse `Real.logb 2`; `ell(t)>0` even at empty, where phi is 0. |
| C21-064 | Phi is nonnegative on every tree and zero at E. | Structural induction and `Real.logb_nonneg`; BST is not necessary. |
| C21-065 | `Asplay x t = (Tsplay x t:Real)+Phi(splay x t)-Phi t`. | Signed real difference. This charge may be negative; no natural truncation. |

## Theorem 21.1 and its complete proof obligations: pp. 249–251

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-066 | Theorem 21.1: `bst t` and structural subtree `X=N(l,x,r)` imply `Asplay x t ≤ 3*(phi t-phi X)+1`. | Primary `A_splay_ub`; retain both premises and the queried subtree, rather than proving only a weaker root-size bound. |
| C21-067 | Search branches that encounter an empty selected child/grandchild are impossible under the present-subtree premise. | Derive membership from structural subtree and use strict BST inequalities; source `in_set_tree_if` guides this step. |
| C21-068 | If x is already root, Asplay equals 1. | Value unchanged and source call count 1; target subtree is that root by BST uniqueness. |
| C21-069 | Single-rotation base case has charge `phi(N(B,b,C))-phi(N(A,x,B))+1`, at most `3*(phi t-phi X)+1`. | Size preservation cancels whole-root rank; monotonicity bounds both subtree ranks. Include the mirrored base. |
| C21-070 | Strict BST uniqueness identifies an x-labelled structural subtree with the one reached in each branch. | Needed for the displayed base proof's final replacement of `N(A,x,B)` by X. A generic label-presence assumption alone is insufficient. |
| C21-071 | In recursive zig-zig, if `splay x A=A'=N(A1,x',A2)`, reconstructed whole tree has the same phi as old `ABC`. | Source `size_splay` gives equality of leaf counts; no potential invariance is claimed. |
| C21-072 | Zig-zig charge decomposes as `Asplay x A + phi(A2BC)+phi(BC)-phi(AB)-phi(A')+1`. | Exact local potential cancellation with the figure's compound-tree naming. Preserve the `+1` and correct recursive subtree. |
| C21-073 | X belongs to A's structural subtrees, so apply the induction bound there and replace `phi(A')` by `phi(A)`. | Branch inequalities/BST route X into the selected grandchild. |
| C21-074 | For positive real x,y, `1+log₂ x+log₂ y < 2*log₂(x+y)`. | Primary `ld_ld_1_less`; stronger `2+log₂ x+log₂ y ≤ 2*log₂(x+y)` follows from `4*x*y≤(x+y)^2`. Standard logb algebra/monotonicity and square nonnegativity suffice; a new logarithm is unnecessary. |
| C21-075 | The remaining zig-zig rank inequalities close the target bound: selected proper subtrees have strictly smaller leaf counts/ranks than their ancestors. | Source proof uses C21-074 with `ell(A)` and `ell(BC)`; both positive even when another displayed subtree is empty. |
| C21-076 | Zig-zag charge decomposes as `Asplay x B + phi(AB1)+phi(B2C)-phi(AB)-phi(B')+1`, where `B'=splay x B`. | Correct p. 251's first-line `Tsplay x A` to `Tsplay x B`; primary proof already has B. |
| C21-077 | Apply the induction hypothesis for X in B, size preservation, and C21-074 to `ell(AB1),ell(B2C)` to close zig-zag. | Retain all positivity and proper-subtree rank comparisons. |
| C21-078 | Prove both mirrored inductive cases. | Explicit cases or a proved mirror/order-dual transformation; a prose statement of symmetry is not missing theorem coverage. |

## Remaining logarithmic bounds and clients: pp. 251–252

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-079 | Every nonempty tree has `phi≥1`. | `ell≥2`, log monotonicity and `logb_self_eq_one` at base 2; no BST premise. |
| C21-080 | Corollary 21.2: for a BST and a present x, `Asplay x t≤3*(phi t-1)+1`. | Primary `A_splay_ub2`, using an actual x-labelled subtree and C21-079. |
| C21-081 | Lemma 21.3: for nonempty BST t, there exists a present y with **both** `splay y t=splay x t` and `Tsplay y t=Tsplay x t`. | Primary `ex_in_set_tree`; output equality does not imply the cost equality. Preserve both conclusions in the induction and correspondence. |
| C21-082 | Corollary 21.4: for every BST, `Asplay x t≤3*phi t+1`. | Primary `A_splay_ub3`; combines the present-key case with C21-081 and handles E separately. |
| C21-083 | The stronger expression with `phi-1` cannot cover E. | At E, Asplay is 1 whereas `3*(0-1)+1=-2`. This independent boundary prevents an invalid theorem simplification. |
| C21-084 | Lemma 21.5: `bst t → Tinsert x t+Phi(insert x t)-Phi t ≤4*phi t+2`. | Primary `amor_insert`; correct exact book constant, including empty insertion of cost 0. |
| C21-085 | In insertion's new-root cases, the extra logarithmic contribution is controlled by `log₂(s+1)≤log₂ s+1` for `s≥1`, plus child-size monotonicity. | Standard logb lemma from `s+1≤2*s`; equality/empty branches remain separate. |
| C21-086 | Define `Asplay_max t = Tsplay_max t+Phi(splay_max t)-Phi t`. | Shape-only real potential charge; no payload order is inherently required. |
| C21-087 | Nonempty t implies `Asplay_max t≤3*(phi t-1)+1`. | Primary `A_splay_max_ub`; notably no BST hypothesis in the source theorem. |
| C21-088 | All t satisfy `Asplay_max t≤3*phi t+1`. | Primary `A_splay_max_ub3`, with E's cost 1. |
| C21-089 | BST deletion satisfies `Tdelete x t+Phi(delete x t)-Phi t≤6*phi t+2`. | Primary `amor_delete`; combine two actual phases, not two arbitrary input costs. |
| C21-090 | The deletion proof handles miss, empty-left hit and nonempty-left hit, preserving BST and using child size/log bounds and nonnegative residual potential. | Ensure the discarded right subtree of splay-max is justified by its correctness theorem; no invented default element. |
| C21-091 | Proper membership costs one splay plus a bounded root test and has the corresponding amortized logarithmic bound when its new state is retained. | Distinguish uncharged root tests in the recursive-call metric from a primitive-test metric with a constant extra charge. Boolean-only repeated membership is an observer and cannot spend an unretained potential decrease. |
| C21-092 | Actual mixed traces from E have work bounded by the sum of these operation-dependent logarithmic budgets evaluated at the actual prior sizes. | Reuse real-potential/invariant-aware Chapter 19 telescoping and existing `Resources.run`; no probability distribution is required. |
| C21-093 | Traces starting from an arbitrary nonempty BST retain its initial potential. | For a size-based simplification, prove `Phi t≤n(t)*log₂ ell(t)`; do not drop a potentially large stored initial credit. The AFP overall U uses looser `+3` insertion/deletion constants, while its cost definitions remain the same; this is slack, not a new wrapper tick. |

## Exercise 21.1: p. 252

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-094 | Find a sequence of k numbers whose successive insertions from empty produce height k. | Concrete target: insert `0,1,…,k-1` in that order, using `List.range k` with left-to-right state threading. |
| C21-095 | Prove the resulting tree is a left chain with k labelled nodes, height k and strict BST validity. | Induct on increasing insertions: the previous maximum is root with empty right child; splaying the new larger key leaves it unchanged, then the GT insertion puts the old tree at the new root's left. |
| C21-096 | The sequence's distinctness and chronological insertion order matter. | Unlike the skew-heap exercise, repeated equal keys are suppressed here and do not grow height. A right fold of ascending numbers is a different history. |
| C21-097 | This family demonstrates lack of logarithmic worst-case height/access while respecting amortized bounds. | For k>0, querying the minimum in this left chain takes `ceil(k/2)` source splay entries; after retaining the splayed result, another equal query costs 1. The full family/cost formula is a proof target, not already checked Lean code. |

## Static optimality and conjecture scope: pp. 245, 252

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C21-098 | Retain the Static Optimality Theorem as a separate mathematical obligation. A precise primary statement concerns m successful accesses on a fixed n-key tree, with every key accessed at least once and frequency `q_i>0`: total access time is `O(m+Σ_i q_i*log₂(m/q_i))`, with a constant uniform in the sizes, sequence and initial shape. | Sleator–Tarjan Theorem 2, p. 659. Use positive n,m for logarithmic divisions and handle the empty history/tree separately. No updates are present in that statement; the evolving tree is retained after each access. Arbitrary initial shape is allowed under the stated frequency condition. |
| C21-099 | Connect that theorem to the chapter's exact recursive splay algorithm and cost metric. | Need a weighted access lemma for this variant or an exact algorithm/cost simulation with the primary paper's analyzed variant. Neither the unweighted `A_splay_ub` nor the file named `Splay_Tree_Analysis_Optimal` provides this correspondence. |
| C21-100 | Derive the advertised constant-factor comparison with any static BST serving the same access sequence. | Define static successful-search cost, include one unit per access, and establish the required information/comparison lower bound or an equivalent direct weighted comparison. Equality of stored sets or outputs is not a cost comparison. |
| C21-101 | State startup/frequency boundaries explicitly, and give a hot-key specialization only with those boundaries. | If some stored keys have frequency zero, do not form `log(m/0)` or silently erase initial potential. A suitable positive-weight or initialization-term variant must be proved; one expensive first access is compatible with static optimality only when its startup terms are accounted for. |
| C21-102 | Declare the Dynamic Optimality Conjecture as a precise `Prop` in the documented BST trace model below, preserving its unproved status as reported by the pinned book. The proposition quantifies uniform constants before all fixed-key trees, successful-access sequences and admissible competitor traces, and permits a linear-in-key-count startup term. | Mandatory statement coverage, not a promised proof. Do not introduce an axiom, `sorry`, or an assumed instance, and do not let downstream theorems use the conjecture as an established fact. The metric/variant correspondence must be explicit. No claim about research status after the pinned manuscript is made here. |

## Verified correction and important non-equivalences

**Zig-zag proof typo.** Printed p. 251 begins its recurrence with
`Tsplay x A`; Figure 21.1 and the pinned `A_splay_ub` proof recurse into B.
A concrete strict BST has `A=E`, `B=N(N(N(E,5,E),6,E),8,E)`, left-parent key
2, whole-root key 10 and query 5. Exact recurrence evaluation gives
`Tsplay 5 A=1`, `Tsplay 5 B=2`, and whole-tree cost 3. The printed first
line would charge 2 before the same potential difference. This discrepancy
was independently evaluated and the printed prime/letter visually checked;
the corrected line uses B.

**A similarly named theorem file is not static optimality.** The inspected
`Splay_Tree_Analysis_Optimal` parameterizes logarithm base and potential
coefficient, then instantiates an improved `3/2` logarithmic splay bound.
Its potential still depends on unweighted leaf counts; no key-frequency
sequence or comparison against a static search tree appears. Keep its
optional sharper constants separate from C21-098–101. The primary paper
also discusses several splaying variants; transfer requires a proved
relationship with this book's exact recursion, not just the shared name.

**Membership can preserve the value and lose the resource guarantee.**
The displayed `isin : Tree α → α → Bool` is correct as a Set observation.
If repeatedly invoked on the same retained old tree, it is a pure observer
and its potential difference is zero for the client's state. The tree
returned internally by splay must be exposed and threaded by a separate
state-returning client before applying the amortized theorem. This is the
explicit exception already explained by the book, not permission to change
the Set interface's value theorem silently.

## Minimal placement and connected acceptance evidence

Use the shared ordinary-tree/BST domain for splay operations and value laws,
with the existing `BinaryTree` carrier and earlier strict-list observation.
Measured companions and logarithmic potential analysis belong in Resources
and import that value layer. Keep payload comparison laws, structural
inorder preservation and complexity assumptions separate. Reuse shared real
logarithm inequalities where another tree client actually needs them; there
is no reason to introduce a new log definition or a general-purpose
comparison/rotation language for this chapter alone.

Acceptance examples should distinguish every real boundary: all four double
rotation directions; a missing key stopping at a child versus a guarded
grandchild; duplicate insertion; unsuccessful deletion that changes shape;
deletion through a nonempty predecessor subtree; empty cost differences;
the corrected zig-zag tree above; and an increasing-insertion chain followed
by two retained-state searches for its minimum. Each should connect actual
tree/list or set observations with the selected measured cost. Static
optimality additionally needs a fixed key set, an explicit access-frequency
example and the metric bridge; the ordinary logarithmic examples do not
cover that retained theorem. All obligations remain queued.

## Required conjecture statement, with no promised proof: 2026-11-02

CSW-07 in `coverage-scope-audit.md` identified optional wording in C21-102.
The row now requires a precise proposition while preserving the book's stated
unproved status. The prior note and its hash are preserved by
`scope-reconciliation.md`; no implementation or acceptance is claimed here.

The already-pinned Sleator–Tarjan paper supplies **Conjecture1, §7, printed
p.684 (PDF33)**. Its introductory p.653 permits a competitor tailored to the
access sequence. The p.684 statement makes the startup term linear in the
fixed number n of keys, rather than requiring all keys to be queried or a
sufficiently long sequence. This bounded additional inspection used the same
saved PDF with SHA-256
`33fe18c5aec145c30bd32fe155d05e25ffa9999f043c3422d0ea66de6ce14364`;
no new source campaign was undertaken.

A precise declaration can use finite BSTs over `Fin n` containing each key
exactly once, an arbitrary successful-access list xs, and finite admissible
competitor traces. Each trace starts from the same arbitrary valid tree T,
searches every requested key in order from its current root, and may perform
finite sequences of legal BST rotations between accesses. Let

`W_A(trace) = sum_j (1 + depth(T_j, xs[j])) + numberOfRotations(trace)`.

The competitor may use offline knowledge of xs. It need not rotate only on
the just-searched path, and the stated model charges one per rotation anywhere
in the tree without an additional cursor walk. The conjecture proposition is
the following uniform statement, with constants before every input/trace:

`exists c0 c1 : Nat, forall n T xs trace,
  ValidBST_n T -> Admissible T xs trace ->
  W_splay(T,xs) <= c0*n + c1*W_A(trace)`.

The empty-key case has only the empty successful-access history and should be
handled explicitly. No insertion, deletion or failed lookup belongs to this
statement; unlike C21-098, no every-key-positive-frequency assumption appears.
The same-initial-tree formulation makes the initial-state convention explicit;
if different initial trees are permitted, a separate initialization bridge is
needed rather than silently changing the model.

The paper's p.658 (PDF7) counts splay rotations, with one unit when there are
none. This is not definitionally the chapter's recursive-entry observation.
Name the exact splay transition and cost in the proposition, and record/prove
the variant/constant-factor metric correspondence when connecting it to the
book's implementation. C21-099's variant warning still applies. Choosing a
modern different BST model requires a correspondence, not an unmentioned
change to this source statement.

Required Lean coverage is a checked, documented `def ... : Prop` and its
model/observation declarations or existing exact correspondences. It is not a
proof of the displayed conjecture, an axiom, or a hypothesis usable as a proved
library fact. No adjacent conjecture or other whole-paper result is added.
