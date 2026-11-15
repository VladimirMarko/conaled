# Chapter 4: Binary Trees — source obligations and existing reuse

Research date: 2026-11-02. Local ticket: `FDSA-004`.

**State: queued-source inventory only.** Chapter 1 remains the active
formalization. This document does not activate Chapter 4, add Lean declarations,
certify existing builds, or accept any Chapter 4 obligation. It records original
analysis of the pinned book, its associated Isabelle theories, and current
conaled/Mathlib interfaces. Every item still needs a checked implementation or
reuse witness, statement review, applicable validation and independent reviews.

## Evidence, pins and source boundaries

| Source | Inspected identity |
|---|---|
| Book | *Functional Data Structures and Algorithms: A Proof Assistant Approach*, version July 27, 2026; Chapter 4, printed pp. 47–58, PDF pages 53–64. Official PDF: <https://fdsa-book.net/functional_data_structures_algorithms.pdf>. SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Isabelle revision | <https://github.com/isabelle-prover/mirror-isabelle> at `f86f290225eebcc52c1ae7dba2e098f405f51c21`. This is the shared source pin used by the source inventory; it postdates the book edition. Statements were compared here, rather than assuming the revision is identical to the July 2026 development. |
| Basic binary trees | `src/HOL/Library/Tree.thy`; SHA-256 `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Tree.html>. |
| Logarithmic tree results | `src/HOL/Library/Tree_Real.thy`; SHA-256 `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6`. Discovered supporting source, not a direct Chapter 4 PDF link. |
| Prefix-to-tree balancing | `src/HOL/Data_Structures/Balance.thy`; SHA-256 `6d14341de140a4cf5d811798aa1796c143a9127aedfeae0b600f8d174e6bb3fc`. Discovered supporting source, not a direct Chapter 4 PDF link. |
| Augmented tree observations | `src/HOL/Data_Structures/Tree2.thy`; SHA-256 `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Tree2.html>. |
| Isabelle license | `COPYRIGHT` at the same revision, locally `ISABELLE-COPYRIGHT`; SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. BSD-3-Clause terms; retain applicable notices when translated source is incorporated. |
| Mathlib | Pinned commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, verified from the local dependency checkout. Inspected `Data/Tree/Basic.lean`, `Data/Tree/Traversable.lean`, `Combinatorics/Enumerative/Catalan/Tree.lean`, `Data/Nat/Log.lean`, `Analysis/SpecialFunctions/Log/Base.lean`, and relevant list/finite-set maximum interfaces. Mathlib files carry Apache-2.0 notices. |
| conaled | Pre-existing interfaces inspected at baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; current source HEAD during this inventory was `1aabd512284fe86254278ac631eda061d311050b`. Relevant existing modules are `Applications/Bracketing/Basic.lean`, `Applications/Huffman/Basic.lean`, `Applications/Sequences/RandomAccess/Basic.lean`, `Applications/Sequences/OrderedSummary.lean`, and the resource/flattening interfaces. No compile or audit was run by this inventory. |

Pinned raw Isabelle files are available by appending the paths above to
<https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/>.
The two directly linked theories alone do not cover the balancing and real-log
proofs. `Tree2.thy` also does not contain the chapter's complete generic
augmentation development or all exercise solutions. Their absence from the four
inspected files is a source-location limitation, not evidence that the exercises
are optional or that no other Isabelle development exists.

The downloaded PDF, extracted chapter text and theory reading copies remain
under `book-source/`. The durable deliverable is this original analysis and its
provenance; do not copy the manuscript into project deliverables. Conversely,
theories contain additional material, such as weight balancing, binary mirror,
heaps and internal path length, beyond this chapter's stated coverage. Their
presence does not automatically expand Chapter 4 into a port of every declaration
in the source file.

## Conventions and architectural recommendation

Write `E` for the empty leaf and `N l a r` for a node. Let `n(t)` be the number
of labelled nodes, `ell(t)` the number of empty leaves, `h(t)` the maximum
root-to-leaf distance, and `mh(t)` its minimum. `I(t)` and `P(t)` denote inorder
and preorder lists. `C(t)` means complete and `AC(t)` almost complete.

**Use Mathlib's `BinaryTree α` as the ordinary carrier.** It has exactly the
book's empty-leaf/node-labelled shape. The only constructor-order difference is
that Lean writes `BinaryTree.node a l r`. Its `nil`, `map`, `numNodes`,
`numLeaves` and `height` already have the source recurrences. Do not use the
deprecated `Tree` aliases, and do not create a duplicate datatype just to match
the source's spelling.

The existing conaled `Bracketing.Tree` and `RandomAccess.Tree` instead have
labelled leaves and unlabelled or cached binary forks. Their empty-tree behavior,
size meanings and path costs differ. They provide reusable proof patterns and
resource composition, but are not definitionally interchangeable with the book's
trees. In particular, `RandomAccess.Perfect` includes rank/cache constraints that
must not become assumptions on arbitrary Chapter 4 trees.

Reuse labels below mean:

- **R:** an inspected existing operation or statement fits; a checked source
  correspondence is still required before counting chapter coverage.
- **P:** partial reuse; a new theorem, adapter, cost argument or recurrence
  correspondence remains necessary.
- **G:** a gap in the integrated modules and library slices inspected here,
  not a claim that every archived or external source was searched.
- **Support:** an auxiliary statement used to connect the source mathematics;
  it need not receive a redundant public wrapper when an existing theorem suffices.

The source's complete trees have all empty leaves at one depth: this is often
called a perfect tree elsewhere. Its almost-complete trees have empty-leaf depths
in two adjacent levels, without a left-packing condition. Preserve these exact
definitions instead of importing a differently named library convention.

The cross-cutting choices in `fdsa-control/DECISIONS.md` apply here: prefer an
explicit valid domain or the established `Option` failure interface for partial
source operations, preserve distinct cost observations, and retain corrected
claims and meaningful counterexamples in the eventual checked development.
Default values or `Inhabited` requirements belong only to a concrete interface
that actually needs them, never to all tree labels.

## 4.1 Basic functions: pp. 47–49

| ID | Source statement or construction | Reuse and remaining obligation |
|---|---|---|
| C04-001 | Finite binary tree datatype `E` or `N l a r`, with structural recursion/induction. Root, child, depth and left/right-spine terminology are introduced; spines/depth are explicitly informal here. | R: `BinaryTree`, generated recursor, `left`, `right`. No requirement to build an extra graph/path formalism merely for the terminology. |
| C04-002 | `setTree E = empty`; `setTree (N l a r) = setTree l union {a} union setTree r`. | G/P: define the independent element-set observation using standard `Set`; ordinary duplicates are forgotten only by this observation. No `DecidableEq α` is required for mathematical sets. |
| C04-003 | `mapTree f E = E`; mapping a node maps both subtrees and the node label. | R: `BinaryTree.map`, `id_map`, `comp_map`. Preserve arbitrary functions, including noninjective ones. |
| C04-004 | `I E = []`; `I (N l a r) = I l ++ [a] ++ I r`. | G: node-labelled inorder is not the existing leaf-fringe function. Standard append laws are reusable. Parenthesization and any replacement of singleton append by cons must be explicit in cost analysis. |
| C04-005 | `P E = []`; `P (N l a r) = a :: (P l ++ P r)`. | G. Postorder is mentioned and expressly omitted in the chapter; it need not become an additional algorithm deliverable merely because `Tree.thy` also defines it. |
| C04-006 | `n E = 0`, `n (N l a r) = n l + n r + 1`; `ell E = 1`, `ell (N l a r) = ell l + ell r`. | R: `BinaryTree.numNodes`, `numLeaves`. Do not confuse either with Lean's implementation-oriented `sizeOf`. |
| C04-007 | Unnumbered theorem: `ell t = n t + 1`. Isabelle `size1_size`. | R: `BinaryTree.numLeaves_eq_numNodes_succ`; its `numLeaves_pos` also discharges later logarithm positivity. |
| C04-008 | `h E = 0`; `h (N l a r) = max (h l) (h r) + 1`. | R: `BinaryTree.height`. |
| C04-009 | `mh E = 0`; `mh (N l a r) = min (mh l) (mh r) + 1`. | G: add the minimum-height observation over the same carrier. |
| C04-010 | Unnumbered theorem `h t <= n t`. Isabelle `height_le_size_tree`. | R: `BinaryTree.height_le_numNodes`. |
| C04-011 | Unnumbered theorem `mh t <= h t`. Isabelle `min_height_le_height`. | G. |
| C04-012 | Unnumbered lower bound `2^(mh t) <= ell t`. Isabelle `min_height_size1`. | G. |
| C04-013 | Unnumbered upper bound `ell t <= 2^(h t)`. Isabelle `size1_height`. | G. Standard natural-power monotonicity is reusable. Include the empty case, whose leaf count is one. |
| C04-014 | `subtrees E = {E}`; `subtrees (N l a r) = {N l a r} union subtrees l union subtrees r`; every tree belongs to its own subtree set. | G/P: ordinary inductive relation or set recurrence, with an explicit equivalence if both are exposed. A subtree is structural, not an arbitrary pruned tree or tree with the same value set. |
| C04-015 | Support used below: `set (I t) = setTree t`, `length (I t) = n t`, and corresponding preorder set/length laws. Isabelle `set_inorder`, `length_inorder`, `set_preorder`, `length_preorder`. | G/P: derive by structural induction using standard List APIs. These are essential bridges for enumeration, reconstruction, and balancing. |
| C04-016 | Support for augmentation: mapping labels commutes with inorder, and preserves `n`, `ell`, `h` and `mh`. Isabelle has `size_map_tree`, `size1_map_tree`, `height_map_tree`, `min_height_map_tree`; traversal-map equality follows the displayed recurrences. | P: Mathlib already supplies map composition and identity, but the inspected tree file does not supply all these observation lemmas. |

## 4.1.1 Exercises: pp. 49–51

| ID | Exercise and exact obligation | Reuse, assumptions and implementation constraints |
|---|---|---|
| C04-017 | Exercise 4.1: implement `inorder2 t suffix` using cons rather than append; prove `inorder2 t suffix = I t ++ suffix` for every suffix. The source solution is `inorder2 E xs = xs`, `inorder2 (N l a r) xs = inorder2 l (a :: inorder2 r xs)`. | G/P: `Tree.inorder2`/`inorder2_inorder` in Isabelle supplies the recurrence/proof reference. `Bracketing.fringeAcc_eq` is a closely related existing pattern on a different carrier, not the required theorem. |
| C04-018 | Exercise 4.1 resource requirement: the accumulator traversal has linear source-model running time in `n(t)`; account for the introductory claim that direct inorder can be quadratic. | G: one recursive-entry charge gives the accumulator count `2*n(t)+1` when constructors/parameters cost zero. The direct traversal's cost depends on shape; use a left-chain family for quadratic worst-case growth and do not claim every shape costs quadratically. Exact constants depend on whether both displayed appends are retained. |
| C04-019 | Exercise 4.2: executable finite list `enumTree xs` with `set(enumTree xs) = {t ∣ I t = xs}`. | P/G: Mathlib `BinaryTree.treesOfNumNodesEq` enumerates unlabelled shapes of a given node count, with `mem_treesOfNumNodesEq` and `coe_treesOfNumNodesEq`. A deterministic inorder-labelling bridge could turn these into the requested trees. Alternatively recurse over every possible root position and both prefix/suffix enumerations. Prove soundness, completeness and termination; do not merely prove that enumerated trees have the right length. |
| C04-020 | Exercise 4.2 optional strengthening, explicitly retain in coverage: output has no duplicate trees. | G/P: distinct shapes and injectivity of inorder labelling at fixed input can establish `List.Nodup`, even when labels repeat. Requiring distinct labels would improperly weaken the exercise. A Finset-to-list construction needs its executable enumeration order and standard Nodup theorem connected. |
| C04-021 | Exercise 4.3 definitions: `wpld d E = 0`; at a node of weight `w`, add `(d+1)*w` and recurse into both children at `d+1`; `wpl0 t = wpld 0 t`. Define `sumTree` by left sum + node weight + right sum, and `wpl(N l w r) = sumTree(N l w r) + wpl l + wpl r`, with zero on `E`. Prove `wpl0 t = wpl t`. | G/P: natural weights, with the root contributing its full weight. Existing `Huffman.pathCost_eq` counts labelled leaves at their depth and gives zero for a root leaf; it is not this statement. Its accumulator-generalization pattern is useful. |
| C04-022 | Support for Exercise 4.3: `wpld d t = d * sumTree t + wpl t` for arbitrary `d`, hence the requested zero-depth theorem. | G: this is an inventory-derived stronger induction invariant, not an accepted theorem. No source runtime improvement is implied by the value identity. |
| C04-023 | Exercise 4.4: `level E k = []`; `level (N l a r) 0 = [a]`; `level (N l a r) (k+1) = level l k ++ level r k`. | G. Node labels at a fixed depth must retain left-to-right order and multiplicity. |
| C04-024 | Exercise 4.4: implement `levels t` by one traversal of the input tree, with no natural-number parameter or arithmetic in the algorithm; list helpers are allowed. `levels E = []`. | G: candidate `levels(N l a r) = [a] :: mergeLevels(levels l)(levels r)`, where aligned levels concatenate and an unpaired suffix is retained. Do not compute a height and then call `level` once per depth. One tree traversal alone does not establish a linear whole-program cost for the list merges. |
| C04-025 | Exercise 4.4 first correctness target: `length(levels t) = h t`. | G. |
| C04-026 | Exercise 4.4 indexed correctness: if `k < h t`, the `k`th entry of `levels t` is `level t k`; equivalently the full list is the levels at indices `0 .. h(t)-1`. | G/P: Lean bounded indexing or `getElem?` can express this without an unspecified out-of-range value. The empty tree gives no levels. |
| C04-027 | Exercise 4.5: total reconstruction algorithm from preorder and inorder lists. | G: an executable implementation needs decidable label equality to find the preorder root in inorder. Specify arbitrary malformed-input behavior while proving the source contract only on consistent traversals. Splitting preorder's tail at the root's inorder position supplies recursive subproblems smaller than the original preorder list. |
| C04-028 | Exercise 4.5 theorem: `Nodup(P t) -> reconstruct(P t)(I t) = t`. | G. Preserve the distinctness hypothesis: a root with a same-labelled left child and a root with a same-labelled right child both have preorder/inorder `[a,a]` but are different trees. Mere multiset equality of traversals is insufficient. |
| C04-029 | Exercise 4.6: rose-tree datatype `Nd a children`, where children form a finite ordered list; mirror every child and reverse the child order. | G/P: this is a different nested datatype, not `BinaryTree`. Use an existing matching rose-tree interface only if actually found; no such direct implementation was identified in the inspected conaled modules. Standard List map/reverse composition is reusable. |
| C04-030 | Exercise 4.6 theorem `mir(mir t) = t`, for all finite rose trees. | G: nested induction must provide hypotheses for every child. Reversing labels or reversing only the top-level child list is insufficient. |

## 4.2 Complete trees: pp. 51–52

| ID | Source statement | Reuse or gap |
|---|---|---|
| C04-031 | `C E` is true; `C(N l a r)` iff `h l = h r`, `C l` and `C r`. | G. A Prop-valued invariant with a proved Boolean checker is acceptable; keep executable checking separate from assumptions. |
| C04-032 | Lemma 4.1: `C t <-> mh t = h t`. Isabelle `complete_iff_height`, with opposite equality orientation also provided by `complete_iff_min_height`. | G. This connects the recursive invariant to all-leaves-same-depth meaning. |
| C04-033 | Lemma 4.2: `C t -> ell t = 2^(h t)`. `size1_if_complete`. | G. |
| C04-034 | Lemma 4.3: `not C t -> ell t < 2^(h t)`. `size1_height_if_incomplete`. | G: strictness is necessary for the subsequent converse. |
| C04-035 | Lemma 4.4: `not C t -> 2^(mh t) < ell t`. `min_height_size1_if_incomplete`. | G: distinct from the nonstrict bound C04-012. |
| C04-036 | Corollary 4.5: `C t <-> ell t = 2^(h t)`. `complete_iff_size1`, using `complete_if_size1_height`. | G: both directions required. |
| C04-037 | Unnumbered interpretation: complete trees have `h t = log_2(ell t)`. Isabelle `Tree_Real.size1_log_if_complete`. | P/G: derive the real logarithm statement from C04-033, using positive leaf count. It is not a floating-point computation. |

### Exercise 4.7: maximal complete subtree

| ID | Exact obligation | Remaining work |
|---|---|---|
| C04-038 | Construct `mcs t` with only one recursive traversal of the input tree. The algorithm may compute heights and compare trees, but may not call `complete` or `subtrees`. | G. A traversal returning a completeness flag, height and chosen complete subtree can share its structural work; compute flags from child summaries, rather than rerunning the forbidden predicates. |
| C04-039 | Returned object is a structural subtree of `t` and is complete. | G. Proving completeness alone would allow a freshly synthesized tree and miss the subtree requirement. Include `E`, since it is a subtree of every finite tree and complete. |
| C04-040 | Maximal height: for every `u`, `u in subtrees t` and `C u` imply `h u <= h(mcs t)`. | G. Ties may be resolved deterministically without asserting a unique maximizing subtree. No bound on label values or label ordering is required. |
| C04-041 | Explicit bonus: avoid all tree-equality tests. | G. A computed completeness flag and natural heights suffice for a candidate implementation, so no `DecidableEq α` should be needed for this stronger route. This remains a design proposal requiring a checked algorithm and proofs. |

## 4.3 Almost complete trees: pp. 52–56

| ID | Source statement | Reuse or gap |
|---|---|---|
| C04-042 | `AC t` iff `h t - mh t <= 1`, with natural truncated subtraction. | G. Since `mh <= h` is proved, this is equivalently `h <= mh+1`; preserve the empty case. |
| C04-043 | Lemma 4.6: `AC s` and `n s <= n t` imply `h s <= h t`. Isabelle `acomplete_optimal` allows the two trees to have different label types. | G. This is a height optimum under a node-count comparison, not a claim that every minimum-height tree is almost complete, or a machine-time optimum. |
| C04-044 | Lemma 4.7: `AC t -> h t = ceil(log_2(ell t))`. Isabelle `Tree_Real.height_acomplete`. | P/G: natural-log version `h t = Nat.clog 2 (ell t)` is appropriate, with an explicit bridge using `Real.natCeil_logb_natCast`. |
| C04-045 | Lemma 4.8: `AC t -> mh t = floor(log_2(ell t))`. `Tree_Real.min_height_acomplete`. | P/G: `Nat.log 2 (ell t)`, bridged by `Real.natFloor_logb_natCast`. Empty trees have `ell=1` and both heights/logarithms zero. |
| C04-046 | Support: completeness implies almost completeness; almost completeness passes to structural subtrees. Isabelle `acomplete_subtreeL`, `acomplete_subtreeR`, `acomplete_subtrees`. | G. These support constructor laws and later chapter clients; they do not make arbitrary height-balanced trees almost complete. |

### 4.3.1 Prefix/list/tree balancing

| ID | Source statement or construction | Reuse and remaining work |
|---|---|---|
| C04-047 | `bal 0 xs = (E,xs)`. For positive `n`, let `m=n/2`, compute `(l,ys)=bal m xs`, then `(r,zs)=bal(n-1-m)(tail ys)`, returning `(N l (head ys) r,zs)`. | G. Preserve sequential consumption: the second recursive call consumes the suffix produced by the first. Do not replace the algorithm with repeated `take/drop` and then claim the same cost. |
| C04-048 | Termination by decreasing `n`; both `m<n` and `n-1-m<n` when `n>0`. Preserve the successful-input domain `n<=length xs`, so every used head exists. | G/P: standard arithmetic is reusable. Isabelle's total `hd []` relies on its inhabited-type logic; an unrestricted Lean function over potentially empty `α` needs an explicit domain, failure return, or a stated `Inhabited α`/default policy. The source itself warns about this undersized-input case. Do not silently strengthen the useful domain's hypotheses. |
| C04-049 | Derived functions: `balList n xs = (bal n xs).fst`; `balanceList xs = balList(length xs) xs`; `balTree n t = balList n (I t)`; `balanceTree t = balTree(n t) t`. | G. If the safe core has a dependent or failure interface, supply source-compatible successful-input wrappers and show their recurrence correspondence. |
| C04-050 | Lemma 4.9: `n<=length xs` and `bal n xs=(t,zs)` imply `xs=I t ++ zs` and `n(t)=n`. Isabelle `Balance.bal_inorder`. | G. Both value decomposition and exact consumption are required; arbitrary return suffixes cannot be hidden. |
| C04-051 | Support: suffix length is `length xs - n` (`bal_length`); stronger direct observation `zs=drop n xs` follows from C04-050 and inorder length. | G/P. This is useful for a compositional consumer and shows the source precondition is propagated to the second recursive call. |
| C04-052 | Four displayed inorder laws: `n<=length xs -> I(balList n xs)=take n xs`; `I(balanceList xs)=xs`; `n<=n(t) -> I(balTree n t)=take n(I t)`; `I(balanceTree t)=I t`. | G/P: source theorems `inorder_bal_list`, `inorder_balance_list`, `inorder_bal_tree`, `inorder_balance_tree`. Preserve prefix truncation and full-sequence order/multiplicity. |
| C04-053 | Support: exact sizes of all derived results: respectively `n`, `length xs`, `n`, and `n(t)` under their corresponding successful-input premises. | G/P: `size_bal_list`, `size_balance_list`, `size_bal_tree`, `size_balance_tree`, or derive from C04-052 and inorder length. |
| C04-054 | Lemma 4.10: `n<=length xs` and `bal n xs=(t,zs)` imply `h t=ceil(log_2(n+1))`. `Balance.height_bal`. | G/P: natural-ceiling-log recurrence and Chapter 2's logarithm-halving work are reusable. Preserve `n+1`, not `n`, at zero and exact powers of two. |
| C04-055 | Lemma 4.11: same premises imply `mh t=floor(log_2(n+1))`. `min_height_bal`. | G/P: the complementary right-subtree size matters; the proof uses `n-1-m+1=(n+1)/2`. |
| C04-056 | Corollary 4.12: same premises imply `AC t`. `acomplete_bal`. | G/P: derived from the two height formulas and ceiling-floor gap, or via a separately checked equivalent structural argument. |
| C04-057 | Unnumbered extension to derived functions: the successful results of `balList`, `balanceList`, `balTree`, `balanceTree` are almost complete, with corresponding height formulas. | G/P: `acomplete_bal_list`, `acomplete_balance_list`, `acomplete_bal_tree`, `acomplete_balance_tree` and `height_*` source corollaries. The full-list/full-tree wrappers have no extra length premise. |
| C04-058 | Figure 4.3 provides the worked `balanceList [0,...,9]` example: root 5, left subtree rooted 2, right subtree rooted 8. Account for the preceding sorted-input/BST interpretation with the correct ordering assumption. | G/P: check the complete example and full inorder. To obtain Chapter 5's strict BST, require strictly increasing input or nondecreasing input plus `Nodup`; see the correction register. The generic balancer itself requires no ordering on labels. |

### 4.3.2 Exercises

| ID | Exercise and exact obligation | Remaining work |
|---|---|---|
| C04-059 | Exercise 4.8: characterize `AC(N l a r)` by a formula using only `AC`, `C`, `h`, arithmetic/Boolean operations, and `l,r`; no minimum-height operation or new tree construction is allowed on the right. | G. One candidate is C04-060; the label `a` is irrelevant to this structural property. |
| C04-060 | Candidate formula: `AC l and AC r and (h l = h r or (h l = h r+1 and C r) or (h r = h l+1 and C l))`. Prove it equivalent to `AC(N l a r)`. | G. The shorter child must be complete when heights differ by one. Merely requiring both children almost complete and height difference at most one is too weak. This formula is an original derivation; a finite Python check agreed for all 626 unlabelled shapes with at most seven nodes, which is not a Lean proof. |
| C04-061 | Exercise 4.9: prove the running time of `bal` is linear in its first argument. | G: instrument its actual recursive execution under the Chapter 1 model. If head/tail projections and arithmetic are uncharged primitive/inlined operations, `T(0)=1`, `T(n)=T(n/2)+T(n-1-n/2)+1`, yielding `2*n+1`. If another explicitly documented constant projection tariff is used, state and prove that count instead. Retain successful-input premises and the conditional unit-cost arithmetic assumption. This is not automatically a linear-cost theorem for `balanceTree`, whose shown implementation calls direct inorder. |

## 4.4 Augmented trees: pp. 56–58

| ID | Source statement or construction | Reuse and remaining work |
|---|---|---|
| C04-062 | Represent augmentation as `BinaryTree (α × β)`, with keys/values `α` and auxiliary annotations `β`. | R/P: reuse the same datatype; no second augmented-tree datatype is needed. Key lookup-table payload and cached structural measurements are distinct possible meanings of the annotation. |
| C04-063 | Augmented inorder ignores annotations: at a node labelled `(a,b)`, append left key inorder, `a`, and right key inorder. Augmented element-set observation similarly retains only first components. | P: use the ordinary inorder and `BinaryTree.map Prod.fst`; `Tree2.inorder`, `Tree2.set_tree`, `set_inorder`, `length_inorder` supply source references. |
| C04-064 | Two stated observation routes agree: `List.map Prod.fst (I t) = I (mapTree Prod.fst t)`. Structural sizes/heights stay unchanged under annotation erasure. | P: instantiate C04-016. This equality is an actual reusable observation adapter, not an injective encoding of annotations. |
| C04-065 | Size cache reader `sz E=0`, `sz(N l (a,k) r)=k`; smart constructor stores `sz l + sz r + 1`. | G/P: existing cached-size trees show the pattern but use different carriers/validity; do not substitute their perfect-tree restrictions. |
| C04-066 | Size invariant: true at `E`; at a node, `k=sz l+sz r+1` and both child invariants. | G. A correct root number alone is weaker than this all-nodes invariant. |
| C04-067 | Size smart-constructor preservation: valid children imply `invarSz(nodeSz l a r)`. | G. The smart constructor does not repair an invalid descendant. |
| C04-068 | Size observation correctness: `invarSz t -> sz t = n(t)`. | G. Separate this value theorem from the claim that reading the annotation uses constant local work. |
| C04-069 | Generic augmentation: choose arbitrary `zero : β` and `f : β -> α -> β -> β`. Define `F E=zero` and `F(N l (a,b) r)=f(F l) a (F r)`, ignoring stored annotations. | G/P: no monoid, commutativity, order, equality decision or associativity is needed. A generic tree fold is the appropriate common mathematics for size and subsequent examples. Existing ordered sequence summaries are not directly this branching fold. |
| C04-070 | Generic cache observation `bVal E=zero`, `bVal(N l (a,b) r)=b`; smart constructor stores `f(bVal l) a (bVal r)`. | G. Keep operations/independent fold/cached observations separate. |
| C04-071 | Generic invariant: true at `E`; cached `b=f(bVal l) a (bVal r)` and valid children at a node. | G. |
| C04-072 | Generic correctness: `invarF t -> bVal t=F t`; smart-constructor validity preservation is the corresponding construction law, implicit in the generic example and explicit for size/exercise clients. | G. Prove once and recover actual specializations where their types fit. A semantic equality does not justify constant work for arbitrary `f`. |
| C04-073 | Resource qualification: size/height cache reading and smart construction have bounded local overhead under primitive arithmetic/access/constructor assumptions; arbitrary `f` needs its own cost contract. | Explanatory scope plus a bounded measured specialization if a performance claim is made. No claim about actual Lean allocation, heap sharing or physical memory follows from C04-072. |

### 4.4.2 Exercises

| ID | Exercise and exact obligation | Reuse, assumptions and remaining work |
|---|---|---|
| C04-074 | Exercise 4.10: augment with a Boolean and another component sufficient to determine completeness. Define `ch`, `nodeCh`, `invarCh`; prove `invarCh t -> ch t=(C t, ? t)` and child-validity preservation. | G/P: choose the second component as height. Empty summary `(true,0)`; combine `(cl,hl)` and `(cr,hr)` as `(cl and cr and hl=hr, max hl hr+1)`. Then `? t=h t`. This is a specialization of C04-069–072 and should use that public theorem. No decidable equality of labels is needed. |
| C04-075 | Exercise 4.11: for linearly ordered labels, cache the maximum label at each nonempty node. Define `mx`, `nodeMx`, `invarMx`; prove valid empty trees yield `none`, and valid nonempty trees yield `some(Max(setTree t))`. | G/P: maximum needs no artificial bottom element; emptiness is represented by `Option`. Use standard `Finset.max'` plus finiteness/nonemptiness and a set bridge, or the standard optional list maximum specification. The source's generic annotation variable must specialize to the label type for its displayed `some(Max(...))` result to typecheck. |
| C04-076 | Exercise 4.11 preservation and generic-interface fit: valid children yield a valid `nodeMx`, while the reader and invariant cover every node. | G/P: if raw node caches are `α`, their observation is `Option α` with `none` at a leaf. The earlier generic fold with a `zero : α` cannot be applied by silently requiring `OrderBot α`. Either use a justified optional-summary adapter, or a direct source-compatible construction/proof. A generic tree with optional annotations is a different raw representation and needs an explicit bridge. |

## Existing components worth composing

| Component | Precise use here | Boundary to preserve |
|---|---|---|
| Mathlib `BinaryTree` | Same base carrier, map laws, node/leaf counts, height and two existing structural theorems. | No assumption that its introductory documentation proves logarithmic height for every arbitrary tree. |
| `BinaryTree.treesOfNumNodesEq` | Finite enumeration of unlabelled shapes with exactly `n` nodes; could support Exercise 4.2 after an inorder-labelling theorem. | Not yet an enumeration of labelled trees with a prescribed inorder list. Catalan cardinality is useful background, not required by this chapter. |
| `Nat.log`, `Nat.clog` | Discrete floor/ceiling logarithms and power characterizations (`le_log_iff_pow_le`, `log_lt_iff_lt_pow`, `clog_le_iff_le_pow`, `lt_clog_iff_pow_lt`). | Use leaf count or `n+1`, always positive here; do not exchange floor and ceiling near powers of two. |
| `Real.natFloor_logb_natCast`, `Real.natCeil_logb_natCast` | Exact bridges from standard natural logs to the source's real-log floor/ceiling formulas. | The formulas are mathematical equalities, not numeric approximation algorithms. |
| `Resources.Measured`, `bind`, `bind_erases`, `erasureSquare` | Instrument the actual traversal/balancing result and compose independent value correctness with a separately stated count. | Value equality alone cannot transfer costs from a different recurrence. |
| `Resources.TreeFlattening` | Existing pattern for comparing direct append traversal and worklist traversal, followed by a shared sequence/query consumer. | Its trees are leaf-labelled and its append counts copied cells rather than source call entries. Reuse composition interfaces, not mismatched counts or shapes. |
| `Bracketing.fringeAcc_eq` | Existing arbitrary-suffix accumulator correctness pattern. | It is not the node-labelled inorder theorem. |
| `Huffman.pathCost_eq` | Existing depth-offset generalization pattern for weighted path equivalence. | Leaf weights at depth zero differ from Chapter 4's internal-node weights at depth plus one. |
| `Sequences.OrderedSummary` | Inorder can feed full ordered sequence observation and any existing monoidal summary consumer. | Summary equality generally loses information; neither summary equality nor set equality replaces inorder preservation. |
| `Squares` and relational representations | Erasure of annotations, flattening, balancing and subsequent observation can be connected through existing exact/relational contracts. | Do not impose injectivity on annotation erasure or a single canonical concrete representation. |

A reasonable module decomposition is ordinary binary-tree observations and
structural laws, traversals/exercise algorithms, balancing, and augmented-fold
realizations under a tree domain, with resource interpretations under the existing
resource domain and checked compositions in `Examples`. The chapter ledger can
span those modules. No new Lake package or duplicate `BinaryTree` carrier is
justified by this inventory.

## Corrections, ambiguities and counterexamples

1. **Sorted list versus strict BST, p. 54.** The sentence connecting sorted input
   to the next chapter's BST needs the next chapter's strict-order convention.
   With Chapter 2's nondecreasing convention alone it is false: `xs=[1,1]` is
   sorted, while `bal 2 xs` produces `N (N E 1 E) 1 E`, whose left/root ordering
   would require `1<1`. This exact result was independently evaluated with the
   displayed recursion in a scratch Python check. State strict sortedness, or
   nondecreasing sortedness plus `Nodup`, for the future BST corollary. The
   balancing/inorder theorems themselves correctly allow duplicates.
2. **Unspecified head on too-short inputs.** `Balance.thy` explicitly notes that
   its total result can contain `hd []` when `n>length xs`, and that this is not
   an eager functional execution account. Lean types may be empty: choosing
   `α=Empty`, `n=1`, `xs=[]` demonstrates why a node-labelled result of the
   source shape cannot be manufactured without a domain/failure/default
   decision. Keep all useful source correctness premises and make the interface
   decision explicit rather than hiding an inhabitant assumption.
3. **The cost of derived tree balancing.** The book's linear claim and Exercise
   4.9 concern `bal`. The displayed `balanceTree` first calls direct inorder;
   on a left chain, the lengths copied by append are `0+1+...+(n-1)`, so this
   wrapper does not acquire a linear bound merely from the balancer's bound.
   A linear wrapper can use the checked accumulator traversal, but then must
   have its own measured composition theorem.
4. **Quadratic inorder means worst case.** A right chain has empty left
   traversals at each node and only bounded append work per node; it is linear
   under the same source metric. A left chain supplies quadratic growth.
   Avoid interpreting the exercise's wording as a uniform quadratic lower
   bound on every tree of size `n`.
5. **Almost completeness is stronger than a local height check.** Two
   almost-complete children with heights differing by one do not always yield
   an almost-complete parent: the shorter child must be complete. For a
   concrete shape, take a complete height-3 left child and a height-2,
   minimum-height-1 right child. Both are almost complete and their heights
   differ by one; the parent has height 4 and minimum height 2. C04-060 retains
   the missing condition.
6. **Maximum annotation type, p. 58.** The displayed `mx` result is written
   using the generic annotation variable, but its right-hand side contains a
   maximum of labels. Specialize that annotation type to the label type, or
   explicitly provide a representation map if a different cache is chosen.
   Do not add a bottom-element assumption to make the empty case disappear.
7. **Exercise restrictions are observable requirements.** The accumulator
   traversal must not use append; `levels` must not repeatedly index/retraverse
   the tree with natural depths; `mcs` may not call the predicates it is
   supposed to derive. A function extensionally equal to a complying algorithm
   does not by itself meet these implementation restrictions or cost claims.

These observations do not reject the valid numbered structural theorems.
They make their assumptions, algorithms and cost interpretations precise enough
for later statement review.

## Completeness cross-check and chapter-order handoff

The inventory accounts for all Chapter 4 sections and subsections, all displayed
base/augmented algorithms and invariants, all eleven numbered exercises including
the explicitly optional enumeration strengthening and maximal-subtree bonus,
and every named result from Lemma 4.1 through Corollary 4.12.

| Named source result | Checklist item |
|---|---|
| Lemma 4.1 | C04-032 |
| Lemma 4.2 | C04-033 |
| Lemma 4.3 | C04-034 |
| Lemma 4.4 | C04-035 |
| Corollary 4.5 | C04-036 |
| Lemma 4.6 | C04-043 |
| Lemma 4.7 | C04-044 |
| Lemma 4.8 | C04-045 |
| Lemma 4.9 | C04-050 |
| Lemma 4.10 | C04-054 |
| Lemma 4.11 | C04-055 |
| Corollary 4.12 | C04-056 |

| Exercise | Checklist items |
|---|---|
| 4.1 | C04-017–018 |
| 4.2 | C04-019–020 |
| 4.3 | C04-021–022 |
| 4.4 | C04-023–026 |
| 4.5 | C04-027–028 |
| 4.6 | C04-029–030 |
| 4.7 | C04-038–041 |
| 4.8 | C04-059–060 |
| 4.9 | C04-061 |
| 4.10 | C04-074 |
| 4.11 | C04-075–076 |

When the preceding chapters are accepted, begin with the standard carrier and
observation bridges, then traversal exercises and complete/almost-complete laws,
prefix balancing and its cost, and generic augmentation with its actual size,
completeness/height, and maximum clients. Share log-halving and resource-model
results already established by earlier chapters. This is a dependency suggestion,
not activation of Chapter 4 or permission to omit the exercises.

Meaningful checked cases should cover empty/singleton trees, left/right chains,
complete and almost-complete-but-incomplete shapes, repeated labels, arbitrary
traversal suffixes, distinct and repeated-label reconstruction, enumeration of
`[]` and repeated-label inputs, rose trees with several differently shaped
children, tied maximal subtrees, prefixes with an untouched suffix, the ten-item
balancing figure, lengths immediately around powers of two, invalid descendants
under an apparently correct root cache, and the optional maximum of empty and
nonempty trees. Preserve explicit counterexamples to weakened assumptions.

No Lean source, ticket state, repository branch/index, build configuration,
Library item, or GitHub object was changed by this source inventory.
