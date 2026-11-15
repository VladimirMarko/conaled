# Chapter 4 phase 3: completeness summary and cache contract

## Status, ownership, and exact scope

This is a frozen implementation-design proposal recorded on 2026-11-05 under root's bounded report-write authorization. It creates no Lean declarations, candidate, proof result, review credit, or acceptance. Root must review this contract and explicitly authorize source work after the applicable shared acceptance gates. The existing structural author head `af03b76c478bf1b71b2cbe38fb05ca6a69ad91b1`, its four source additions, and the earlier author hold remain immutable.

The original whole Chapter 4 task remains based on accepted `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2` and all 76 frozen obligations. This phase supplies the executable completeness bridge used by C04-031, the shared computation required by C04-038–041, and the Boolean/height cached specialization C04-074. It neither discharges nor removes any other obligation. Root retains entrypoints, chapter correspondence, coverage, integration, validation, and review coordination.

Proposed new source ownership, only after separate authorization:

- `Applications/Trees/CompleteSummary.lean` and `Examples/TreeCompleteSummary.lean`.
- `Applications/Trees/CompleteCache.lean` and `Examples/TreeCompleteCache.lean`.

Both pairs are absent at the inspected structural and XT02 commits. No file at these paths has been created. The shared summary belongs in the pure module; the cache module imports it and the accepted generic cache API. The maximal-subtree module will consume the same pure step, without importing or recomputing an augmented tree.

## Binding sources and status

Primary source: the local manuscript PDF, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`, as bound in `phase3-design-input-identities.json`. Printed pp. 51–52 (PDF 57–58) define completeness, and printed pp. 56–58 (PDF 62–64) define generic augmentation and Exercise 4.10. The book's executable Boolean completeness becomes a Boolean checker bridged to the existing Lean proposition.

The complete frozen inventory is `fdsa-control/research/chapter04-obligations.md`, SHA-256 `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4`. No inventory rows were changed.

The pure Shape development dependency is exact XT02 `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe`, tree `d002afee18c38828f01221837f4c3f302ab155cc`. Its `Applications/Trees/Shape.lean` blob is `52c589e228d4c3a8726f7010ec1de7700ba5eca2`, SHA-256 `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3`. XT02 was explicitly **not accepted** in this assignment. Its API is a development input, not permission to merge it or to bypass its independent full gates.

Accepted XT01 is exact `90469ce4ba3fc49397d369a5db7d58aec7014f58`. Its `Applications/Trees/Cached.lean` blob is `c301ca85e555a8c5bb3c9db10459446121bc6613`, SHA-256 `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6`. Its `Applications/Trees/Observations.lean` blob is `f90fbe8c85b9c88f760236d48129bd2b4c4d7e71`, SHA-256 `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752`. Exact existing source declaration headers, pins, and read identities are in `phase3-existing-api-bindings.json`.

## Pure executable definitions

All declarations below are proposed in namespace `Trees`, with arbitrary `α : Type u`, and where needed `β : Type v`. There is no `DecidableEq α`, order, finiteness, or inhabitance assumption. A tree over `Empty` is supported.

The exact computation contract is:

```lean
completeHeightStep (left : Bool × Nat) (_ : α) (right : Bool × Nat) : Bool × Nat :=
  (left.1 && right.1 && decide (left.2 = right.2),
   max left.2 right.2 + 1)

completeHeight (t : BinaryTree α) : Bool × Nat :=
  Trees.fold (true, 0) completeHeightStep t

completeBool (t : BinaryTree α) : Bool :=
  (completeHeight t).1
```

These are contract expressions, not saved or compiled Lean definitions. The two child summaries are computed once by the fold. The only equality test concerns natural-number heights. The label argument is ignored. Neither `Complete`, a decidability instance for arbitrary propositions, nor a separate call to `BinaryTree.height` appears in this computation.

Freeze these public names and statements:

```lean
completeHeight_nil :
  completeHeight (BinaryTree.nil : BinaryTree α) = (true, 0)

completeHeight_node (a : α) (l r : BinaryTree α) :
  completeHeight (.node a l r) =
    completeHeightStep (completeHeight l) a (completeHeight r)

completeHeight_height (t : BinaryTree α) :
  (completeHeight t).2 = t.height

completeBool_eq_true_iff (t : BinaryTree α) :
  completeBool t = true ↔ Complete t

completeBool_eq_false_iff (t : BinaryTree α) :
  completeBool t = false ↔ ¬ Complete t

completeHeight_map (f : α → β) (t : BinaryTree α) :
  completeHeight (t.map f) = completeHeight t
```

There are three proposed definitions and six proposed theorems. No new minimum-height definition or wrapper around existing shape bounds is proposed.

Proof route: use the accepted `fold_nil` and `fold_node` equations. For the height projection, instantiate `fold_fusion` with `Prod.snd` and the maximum-plus-one algebra, then use `fold_height`. Induction plus XT02's exact `complete_node` proves the Boolean/Prop bridge; the step requires both child flags and equality of the actual child heights. The false characterization follows from the Boolean cases and the true characterization. Label invariance follows from `fold_map` or a direct induction using the ignored label argument. These are proposed proof routes, not successful compiler results.

The abstract proposition `Complete` remains the existing shape specification. The checker is independently executable and linked to it universally; it is not defined by `decide (Complete t)`.

## Cached specialization and source correspondence

Proposed namespace: `Trees.CompleteCache`. The augmentation type is `Bool × Nat`; its Boolean reports completeness and its natural number reports height. For `t : BinaryTree (α × (Bool × Nat))`, define exactly:

```lean
ch t := Trees.Cached.read (true, 0) t

nodeCh l a r :=
  Trees.Cached.smartNode (true, 0) Trees.completeHeightStep l a r

invarCh t : Prop :=
  Trees.Cached.Valid (true, 0) Trees.completeHeightStep t

annotateCh t :=
  Trees.Cached.annotate (true, 0) Trees.completeHeightStep t
```

Use transparent definitions or abbreviations with these exact meanings. Do not introduce a second augmented datatype, a second recursive validity system, or a changed generic cache definition. The source names `ch`, `node_ch`, and `invar_ch` correspond respectively to `ch`, `nodeCh`, and `invarCh`; `annotateCh` is the connected whole-tree construction using the already accepted generic annotator.

Freeze these public laws. Here `a : α`, `q : Bool × Nat`, `l r t : BinaryTree (α × (Bool × Nat))`; `s : BinaryTree α` for annotation laws:

```lean
ch_nil :
  ch (BinaryTree.nil : BinaryTree (α × (Bool × Nat))) = (true, 0)

ch_node :
  ch (.node (a, q) l r) = q

ch_nodeCh :
  ch (nodeCh l a r) = Trees.completeHeightStep (ch l) a (ch r)

erase_nodeCh :
  Trees.Cached.erase (nodeCh l a r) =
    .node a (Trees.Cached.erase l) (Trees.Cached.erase r)

invarCh_nil :
  invarCh (BinaryTree.nil : BinaryTree (α × (Bool × Nat)))

invarCh_node :
  invarCh (.node (a, q) l r) ↔
    invarCh l ∧ invarCh r ∧
      q = Trees.completeHeightStep (ch l) a (ch r)

invarCh_nodeCh_iff :
  invarCh (nodeCh l a r) ↔ invarCh l ∧ invarCh r

ch_eq_completeHeight (ht : invarCh t) :
  ch t = Trees.completeHeight (Trees.Cached.erase t)

ch_correct (ht : invarCh t) :
  ch t = (Trees.completeBool t, t.height)

ch_complete_iff (ht : invarCh t) :
  (ch t).1 = true ↔ Trees.Complete t

ch_height (ht : invarCh t) :
  (ch t).2 = t.height

invarCh_annotateCh :
  invarCh (annotateCh s)

erase_annotateCh :
  Trees.Cached.erase (annotateCh s) = s

ch_annotateCh :
  ch (annotateCh s) = Trees.completeHeight s
```

There are four proposed definitions and fourteen proposed theorems in this namespace. Universally quantified arguments are to be explicit enough for downstream use; the omitted repetitive binders in this list have the types stated immediately above.

The main source-facing equality `ch_correct` uses `completeBool t` on the augmented tree itself. The generic theorem naturally gives the erased form `ch_eq_completeHeight`. These agree because `completeHeight_map Prod.fst` ignores annotations and `Cached.height_erase` preserves height; `completeBool_eq_true_iff` gives the book's Boolean completeness meaning. Thus no proposition is incorrectly placed in a `Bool × Nat` pair, and erasure does not weaken the source statement.

Use these accepted generic laws directly:

- `read_nil`, `read_node`, `read_smartNode`, and `erase_smartNode` give the observations.
- `valid_nil`, `valid_node`, and `smartNode_valid_iff` give the invariant equations and constructor preservation.
- `read_eq_fold` gives `ch_eq_completeHeight` under the **recursive** validity assumption.
- `annotate_valid`, `erase_annotate`, and `read_annotate` give the annotation laws.

The book's two-child invariant hypothesis is preserved exactly. The iff constructor theorem entails its requested implication and also exposes that an invalid child is not repaired by `nodeCh`. Root-local consistency alone is insufficient for correctness. The case notes include an explicit invalid descendant whose false annotation fools a correctly constructed parent.

## Boundaries and future validation

This design does not assume that the author branch already contains accepted XT02 Shape or qualified structural additions. Root controls their eventual reception and must preserve exact source identities or record and review any changed candidate.

The normal execution path for `ch` and `nodeCh` reads only annotations at the root and child roots, respectively. The erasure and correctness observations are proof specifications. No wall-clock, allocation, compiler-sharing, or machine-integer bound is asserted. C04-073's conditional local-resource obligations remain whole-chapter work and are not discharged by these value equations.

After authorization, the examples must compute independently stated expected values and consume the public laws. Root remains sole compiler and acceptance coordinator. The fixed Lean/Lake/dependency pins, proof restrictions, full immutable-candidate checks, independent Standards and Spec axes, and immediate candidate verification remain mandatory. This document is implementation preparation, not either review axis.
