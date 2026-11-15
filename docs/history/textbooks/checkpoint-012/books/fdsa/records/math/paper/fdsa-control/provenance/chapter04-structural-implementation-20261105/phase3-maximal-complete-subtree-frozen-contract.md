# Chapter 4 phase 3: maximal complete structural subtree contract

## Scope and authority

This is a frozen design proposal for C04-038–041, including the mandatory tree-equality-free bonus. It creates no source file, candidate, proof, review outcome, or accepted coverage. Source work remains held until root reviews this design and explicitly releases it after the applicable shared acceptance gates.

The original Chapter 4 base remains accepted `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`; all 76 frozen obligations remain in scope. The existing structural author head `af03b76c478bf1b71b2cbe38fb05ca6a69ad91b1` and all previous reports are immutable. The proposed new author paths are `Applications/Trees/MaximalCompleteSubtree.lean` and `Examples/TreeMaximalCompleteSubtree.lean`, both absent at the inspected structural and XT02 commits.

The primary statement is Exercise 4.7, printed p. 52 / PDF p. 58, in the exact manuscript bound by `phase3-design-input-identities.json`. The book asks for maximality **in height** among complete structural subtrees. Node-count maximality is an additional requested corollary, derived for complete candidates; it is not attributed to an additional book claim. This phase does not redefine structural subtree membership as equal contents, a subsequence, a pruned tree, or an embedding.

## Exact dependencies and smallest assumptions

The proposed module imports the pure `CompleteSummary` contract from the accompanying design note and the existing `BasicObservations` interface. Namespace: `Trees`. Labels are arbitrary `α : Type u`. There is no equality, order, finite-type, or inhabitance assumption on labels. Natural-number comparison and Boolean case analysis are sufficient, including for the `Empty` label type.

Use these exact inputs:

- The structural API at author head `af03b76c478bf1b71b2cbe38fb05ca6a69ad91b1`: `Applications/Trees/BasicObservations.lean`, blob `b41b456122021f1bc3cb73e8defb2802afb4362c`, SHA-256 `3d2decdac9a8803edde8b5b36a97d0deba1a4d7b1cb1f15a93057044f342afc6`. It defines inductive `Subtree.refl`, `Subtree.left`, `Subtree.right`, `subtree_nil_iff`, `subtree_node_iff`, `Subtree.trans`, `subtrees`, and `mem_subtrees_iff`. Its prior author status was uncompiled; root owns qualification and eventual reception.
- Exact XT02 development commit `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe`, Shape SHA-256 `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3`, explicitly not accepted in the assignment. Relevant laws are `Complete`, `complete_nil`, `complete_node`, and `numLeaves_eq_pow_height`.
- Accepted XT01 `90469ce4ba3fc49397d369a5db7d58aec7014f58` supplies the fold used by the proposed shared summary.
- Pinned Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, whose inspected `Mathlib/Data/Tree/Basic.lean` has SHA-256 `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d`, supplies the tree recurrences and `BinaryTree.numLeaves_eq_numNodes_succ`. Exact source headers and unchanged pins are recorded in `phase3-existing-api-bindings.json`.

No existing `Subtree.height_le` or `Subtree.numNodes_le` theorem is assumed: those declarations do not occur in the inspected structural module. If needed, prove private generic containment bounds inside the new maximal-subtree module. Do not edit the existing structural module or invent a previously compiled API.

## One-pass executable contract

Reserve the public structure `Trees.McsSummary` with fields:

```lean
structure McsSummary (α : Type u) where
  whole : Bool × Nat
  best : BinaryTree α
  bestHeight : Nat
```

Here `whole` describes the whole input subtree. It must never be confused with the shape or height of `best`. The third field retains the candidate's height so selection does not traverse that candidate.

Freeze the computation below as the source-design contract. This is pseudocode with Lean names, not compiled source:

```lean
mcsSummary : BinaryTree α → McsSummary α
mcsSummary .nil = ⟨(true, 0), .nil, 0⟩
mcsSummary (.node a l r) =
  let sl := mcsSummary l
  let sr := mcsSummary r
  let wh := completeHeightStep sl.whole a sr.whole
  if wh.1 then
    ⟨wh, .node a l r, wh.2⟩
  else if sr.bestHeight ≤ sl.bestHeight then
    ⟨wh, sl.best, sl.bestHeight⟩
  else
    ⟨wh, sr.best, sr.bestHeight⟩

mcs (t : BinaryTree α) : BinaryTree α :=
  (mcsSummary t).best
```

There is exactly one recursive call for each child of each visited internal node. Each recursive result is retained in a let-binding. A complete current node returns its original children unchanged. An incomplete current node returns one already computed child candidate. It must not construct `.node a sl.best sr.best`: that can produce a complete pruned tree absent from the input's structural subtree set.

The selection rule is deterministic: prefer the left candidate when the two candidate heights are equal; otherwise take the larger candidate height. Compare `bestHeight`, never `whole.2`. A tall incomplete branch can have a shorter best candidate than its sibling.

Permitted executable operations are pattern matching, the two recursive calls, the shared nonrecursive `completeHeightStep`, projections, record/node construction, Boolean branching, natural-number equality, maximum, addition, and comparison. Neither this definition nor a helper it executes may call `Complete`, `subtrees`, `Subtree`, `BinaryTree.height`, `numNodes`, `completeHeight`, `completeBool`, a full annotation pass, or tree/label equality. In particular, deciding a proposition or comparing reconstructed trees is not a substitute for the equality-free bonus.

The no-tree-equality requirement concerns the executable dependency graph, not just the final type signature. Merely omitting a `DecidableEq α` argument does not establish the bonus if a hidden executable helper uses classical equality.

This is a structural traversal contract. It does not assert heap sharing, allocation counts, a generated-code runtime bound, or constant-time arbitrary-precision arithmetic. The example cases and later source inspection must establish that an extensional shortcut has not replaced the required one-pass computation.

## Frozen public specification

The structure constructor and projections are public through `McsSummary`. Reserve the definitions `mcsSummary` and `mcs`. Freeze these theorem names and mathematical statements:

```lean
mcsSummary_nil :
  mcsSummary (BinaryTree.nil : BinaryTree α) =
    ⟨(true, 0), .nil, 0⟩

mcsSummary_node (a : α) (l r : BinaryTree α) :
  mcsSummary (.node a l r) =
    let sl := mcsSummary l
    let sr := mcsSummary r
    let wh := completeHeightStep sl.whole a sr.whole
    if wh.1 then ⟨wh, .node a l r, wh.2⟩
    else if sr.bestHeight ≤ sl.bestHeight
      then ⟨wh, sl.best, sl.bestHeight⟩
      else ⟨wh, sr.best, sr.bestHeight⟩

mcsSummary_whole (t : BinaryTree α) :
  (mcsSummary t).whole = completeHeight t

mcsSummary_bestHeight (t : BinaryTree α) :
  (mcsSummary t).bestHeight = (mcsSummary t).best.height

mcs_nil :
  mcs (BinaryTree.nil : BinaryTree α) = .nil

mcs_subtree (t : BinaryTree α) :
  Subtree (mcs t) t

mcs_complete (t : BinaryTree α) :
  Complete (mcs t)

mcs_height_maximal (t s : BinaryTree α)
    (hsub : Subtree s t) (hc : Complete s) :
  s.height ≤ (mcs t).height

mcs_numNodes_maximal (t s : BinaryTree α)
    (hsub : Subtree s t) (hc : Complete s) :
  s.numNodes ≤ (mcs t).numNodes

mcs_height_le (t : BinaryTree α) :
  (mcs t).height ≤ t.height

mcs_numNodes_le (t : BinaryTree α) :
  (mcs t).numNodes ≤ t.numNodes

mcs_eq_self_iff_complete (t : BinaryTree α) :
  mcs t = t ↔ Complete t

mcs_node_left (a : α) (l r : BinaryTree α)
    (hn : ¬ Complete (.node a l r))
    (hle : (mcs r).height ≤ (mcs l).height) :
  mcs (.node a l r) = mcs l

mcs_node_right (a : α) (l r : BinaryTree α)
    (hn : ¬ Complete (.node a l r))
    (hlt : (mcs l).height < (mcs r).height) :
  mcs (.node a l r) = mcs r
```

Thus the explicit proposed library additions are one structure, two definitions, and fourteen theorems, plus the structure-generated constructor/projections. These signatures are a mathematical contract; no successful elaboration is claimed.

By the existing definition of `subtrees` and `mem_subtrees_iff`, the book-facing statements are exactly:

```lean
mcs t ∈ subtrees t
Complete (mcs t)
∀ s, s ∈ subtrees t → Complete s → s.height ≤ (mcs t).height
∀ s, s ∈ subtrees t → Complete s → s.numNodes ≤ (mcs t).numNodes
```

These are direct formulations of the frozen structural statements, not separate requested wrapper declarations. There is no claim of a unique maximizer. The left-tie rule selects one of possibly several distinct maximizers.

## Proof design

Maintain a single inductive summary invariant for every input subtree: the whole summary equals `completeHeight` of that input; the stored best height equals the returned candidate's actual height; the candidate is structurally contained; it is complete; and every complete contained tree has height at most the stored best height.

For the empty case, `subtree_nil_iff` identifies every competitor with the empty tree. The empty tree is complete and has height and node count zero.

For a node whose combined whole flag is true, the shared Boolean bridge proves the original node complete. The selected candidate is precisely that original node, so reflexive containment applies. Any structural competitor has height at most the current tree's height. This containment height bound follows independently by induction over `Subtree` and the existing maximum-plus-one height recurrence.

For a false combined flag, the original node is not complete. A complete structural competitor cannot equal the root, so `subtree_node_iff` puts it in one child. Apply that child's induction hypothesis and the chosen candidate-height comparison. The selected candidate's completeness and containment follow from the child invariant and `Subtree.left` or `Subtree.right`. Both branches preserve the original whole summary.

The candidate and input size bounds use structural containment; they do not need completeness of the input. Prove private height/node-count monotonicity helpers locally if necessary, with no equality assumptions.

For node-count maximality, both the competitor and the selected candidate are complete. XT02's `numLeaves_eq_pow_height` turns height maximality into a comparison of powers of two. Monotonicity of natural exponentiation and `BinaryTree.numLeaves_eq_numNodes_succ` then yield the node-count inequality. The precise arithmetic lemma invocation must be resolved against the pinned sources during authorized implementation; no uninspected Lean lemma signature is asserted here. An extra count cache is unnecessary.

For `mcs_eq_self_iff_complete`, one direction follows from universal candidate completeness after rewriting the equality, and the converse follows from the true whole flag and the root-selection branch. The two node-choice theorems expose the exact left-tie behavior through already proved candidate-height correctness.

## Required connected examples and remaining gates

Use the full expected-value and counterexample matrix in `phase3-case-notes.md`. In particular, test equal-height incomplete children, a tall incomplete branch whose best candidate loses to a shorter complete branch, repeated labels, distinct tied candidates, and a synthetic recombination that is complete but not a structural subtree.

Examples must include uses of `mcs_subtree`, `mcs_complete`, both maximality theorems, and the choice laws, alongside independent explicit expected values. A reflexive example of the algorithm's own definition is not enough. Concrete calculations are planned, not yet checked.

The source-assessment history and independent full acceptance gates of XT01/XT02/XT03 and the whole Chapter 4 task remain in force. This note grants no acceptance to a dependency or row. Root retains the compiler, immutable-candidate checks, audit, both independent review axes, integration, and durability work.
