# Shared binary-tree observations and cached folds

## Receiving state — 2026-11-05

This original XT01 draft is received onto accepted Chapter 3 commit
`298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`. Chapters 1–3 and the recorded
shared predecessors retain their acceptance. The first receiving candidate
`f0fd3faa84d57ab7583f877039da2c703431f0ce` added the four XT01 formal modules
byte-exactly from `64c6b777d828ecfe83234fc2aed94600a1f24297`; all 22
pre-existing local inputs in their recorded closure match this accepted base.
No unrelated shared draft is incorporated.

The first focused build passed the observations and cached-fold modules, then
failed on two proof obligations in `Resources.TreeCache`. The receiving
correction unfolds the existing smart constructor and normalizes the natural
number cost equation. The declarations, hypotheses, callback and tariff remain
unchanged. This failed attempt supplies no complete unit validation.

Both independent XT01 source assessments cover the complete original seven-path
scope and all 115 public names with zero concrete findings. Their overall
outcomes remain Blocked pending actual receiving-candidate qualification.
Focused compilation, complete actual public types, the applicable full check
and exhaustive audit, both final independent axes, and immediate verification
are still required. The qualified official Lean/Lake 4.35.0 native environment
and exact dependencies are unchanged; only the user's Nix waiver applies.

The original mathematical assessment below is retained. Its development-era
status describes the original draft, whose Chapter 1 prerequisite is now
fulfilled. This shared unit does not accept Chapter 4 or its later algorithms.

## Original implementation status and source boundary

This is the implementation-side source and statement assessment for the
FDSA-45 draft. The declarations and connected uses have been written, but
**no compiler, complete candidate gate, exhaustive audit or independent final
review has run for this unit**. Chapter 1 remains the prerequisite. These
files provide no chapter or appendix acceptance by their presence.

The source is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, July 27, 2026, pp. 47–49 and 56–58, with common clients in the
interval-tree, AVL and leftist-heap chapters. The edition SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The official manuscript is
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
It is a research input, not redistributed with this implementation.

Companion Isabelle sources were inspected at
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, especially
`src/HOL/Library/Tree.thy`, `src/HOL/Data_Structures/Tree2.thy`,
`Interval_Tree.thy`, `AVL_Set_Code.thy` and `Leftist_Heap.thy` in the same
data-structures directory. Their pinned BSD-3-Clause provenance and exact
receipts remain in the local source inventories. That revision postdates the
book; no equality of manuscript and repository build revisions is assumed.

The Lean implementation reuses Mathlib's `BinaryTree` at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. It does not duplicate the
carrier, its counts or its height. The constructor order is Lean's
`.node label left right`. Empty leaves carry no labels.

## Ordinary operations and compatibility

`Applications.Trees.Observations` supplies `Trees.fold` with an explicit
empty result and a ternary node operation taking left summary, label and right
summary. The operation needs no associativity, monoid, ordering, decidable
equality or default payload. `fold_map` handles arbitrary label maps;
`fold_fusion` requires only the actual empty/node compatibility equations for
the supplied summary observation.

`fold_numNodes` and `fold_height` connect two different fold instances to the
existing canonical tree observations. `Trees.inorder` retains every occurrence
in left/root/right order. Its length is the existing node count; it commutes
with arbitrary label maps. `numNodes_map`, `numLeaves_map` and `height_map`
preserve shape observations, including for noninjective maps. The leaf-count
law reuses Mathlib's existing node/leaf identity.

The generic fold is not restricted to sequence summaries. A balanced
three-node tree and a three-node chain can have the same inorder and different
heights. An applicative label traversal also has a different callback: it does
not receive the two child summaries needed for a branching fold.

`Applications.Trees.Cached` uses `BinaryTree (alpha × beta)` directly:

- `read` inspects only the root annotation, returning the supplied empty
  summary for an empty tree.
- `smartNode` retains both children and computes the new root annotation
  from their stored summaries and the label.
- `Valid` requires the local cache equation at every node, including valid
  descendants.
- `erase` is `BinaryTree.map Prod.fst`, an independent observation used in
  statements and proofs.

`smartNode_valid_iff` states precisely that the new tree is valid if and only
if both supplied children are valid. A smart constructor does not repair bad
descendants. The central `read_eq_fold` theorem identifies a valid stored
summary with the independent structural fold of the erased tree. Its invariant
does not assume the desired root equality as its only premise.

Erasure preserves inorder and shape unconditionally. `erase_smartNode` also
needs no validity premise. These facts remain useful for malformed caches and
do not imply that their annotations are correct.

`annotate` is an ordinary instance of the same fold whose combine is
`smartNode`. It computes actual stored summaries bottom-up. Its separate
`annotate_valid`, `erase_annotate` and `read_annotate` theorems establish
recursive validity, preservation of the original tree and root agreement with
the original fold. This value construction is not a whole-program cost theorem.

## Explicit local work with an actual callback

`Applications.Resources.TreeCache` uses the existing `Measured`, `bind`,
`pure` and `CallCount.tick`. Its named local-access observation assigns one
unit to each root read and one to the constructor entry. Pair formation,
projections and primitive operations are otherwise inlined; the actual
combining callback supplies its own natural-number observation.

`nodeRun` sequences the left read, right read and callback at those returned
summaries. It stores the callback's actual value and retains the actual child
trees. Its implementation contains no subtree fold, erasure or annotation
pass. The count is

```text
1 + (1 + (actualCallbackCost + 0)) + 1 = actualCallbackCost + 3.
```

`nodeRun_value` requires the callback value equation only at those reached
arguments. `nodeRun_valid` separately adds validity of both children.
`nodeRun_cost` needs neither condition, and `nodeRun_le` only assumes the
actual reached callback costs at most K, giving a bound K+3. The proof does
not replace this local premise with a global callback contract.

This model is separate from the source leftist-heap timing, which assigns
zero to its nonrecursive cached reader and smart constructor. No merge bound
has been transferred between these observations. Nor is primitive arithmetic
on unbounded naturals asserted physically constant-time.

The list-summary callback reuses the actual existing
`Resources.ListReversal.appendRun leftSummary (a :: rightSummary)` and
`appendRun_exact`. It returns the intended inorder value and costs
`leftSummary.length+1`. Consequently this local cached constructor costs
`leftSummary.length+4`. A valid cached left chain with n nodes yields n+4,
so arbitrary callbacks do not acquire a uniform constant bound merely because
their arguments came from caches. The chain annotation is prepared input to
the local operation; its preparation cost is not claimed to be included.

The callback is this chosen single append. The value identity with
`left ++ [a] ++ right` supplies no timing identity with a source execution
retaining two appends or different parenthesization. The source-timing bridge
for direct inorder remains in its chapter's obligations.

## Connected uses and independently expected boundaries

The public compositions are in `Examples.TreeCache`, namespace
`TreeCacheExamples`.

| Intended mathematics | Draft public connection |
| --- | --- |
| A valid size cache returns the canonical node count for arbitrary payloads. | `size_reader`, using `read_eq_fold`, `fold_numNodes` and the erasure size law. |
| A valid height cache returns structural height, including skew trees. | `height_reader`, using `read_eq_fold`, `fold_height` and the erasure height law. |
| One pair cache gives both size and height. | `pair_fold_size` and `pair_fold_height` use `fold_fusion` with the two projections; `pair_reader` applies the one pair-cache invariant. |
| The asymmetric four-node fixture has size 4, height 3 and inorder `[0,1,2,3]`. | `sample_*`, the actual `sizeSample`, `heightSample`, `pairSample`, their validity/erasure laws and reader conclusions. |
| Ordered tree observation composes with an independent existing sequence library. | `ordered_summary_fold` uses `Sequences.OrderedSummary.summary` and its nil/append/singleton laws through fold fusion. The only algebraic premise is `Monoid`; multiplication order is retained. |
| A noncommutative word detects changed ordering. | `sample_word`, connected through `ordered_summary_fold` to the independently specified word. |
| Inorder equality does not determine height. | `same_inorder_different_height`, using two three-node trees with the same repeated labels and heights 2 and 3. |
| Noninjective maps preserve shape and every repeated occurrence. | `repeated_sample`, using the public map laws. |
| Empty label types require no invented payload. | `empty_tree`, `empty_fold`, `empty_observations`, `empty_annotation` and `empty_read`. The summary's base value remains an explicit argument. |
| Root correctness and local root consistency together can hide corrupt descendants. | `corrupt_root_checks`, `corrupt_not_valid`, `corrupt_smart_not_valid`, `corrupt_smart_same_tree`; erasure still gives the correct fixture and inorder. |
| Fold transport ignores arbitrary annotations without asserting validity. | `erased_fold`, a specialization of `fold_map`. |
| Inlined size/height callbacks give local count 3 and preserve valid caches. | `size_node_*`, `height_node_*`, `measured_size_reader`, `measured_height_reader`, using the public measured and pure contracts. |
| A real recursive callback can make local work grow on valid caches. | `append_node_*`, `chainCache_*`, `chain_node_cost/value/valid/exceeds`, using the existing append theorem, annotation/read laws and `inorder_length`. |

The malformed fixture stores sizes 4,2,1,1 at labels 1,0,3,2. Its root is
correct and satisfies 4=2+1+1, while its two child summaries are wrong.
The invariant is satisfiable on every input tree through `annotate`; the
counterexample does not rely on an impossible correctness domain.

## Statement assessment and remaining gates

The implementation-side assessment checked each declaration group for:

- Independent payload/summary universes and an explicit empty result,
  without an inhabited-label or summary typeclass requirement.
- Correct constructor and child-summary positions, ordinary label-map
  composition, and fusion premises that state the actual operation laws.
- Preservation of occurrence order before any possibly lossy sequence summary;
  no commutativity, injectivity or uniqueness-of-label assumption is hidden.
- The distinction between unconditional erasure and conditional cached-value
  correctness, and between a new locally consistent root and valid descendants.
- An actual computed annotation, with erasure and invariant laws kept separate.
- Exact reached callback arguments, actual stored callback values, separate
  value and work contracts, and an explicit local-access tariff.
- Boundary cases for empty labels, skew trees, repeated payloads, bad caches
  and a valid family with growing actual callback work.

Two bounded source/API readings found no concrete semantic mismatch in the
stable pure core and resource construction. They are not compiler results or
independent final-review approval. The exact source identities, additional
client preflight and later candidate evidence are retained in the external
local review records. No informal report is a proof dependency of the Lean code.

The normal public root imports `Examples.TreeCache`, which transitively
imports all three new domain/resource modules. Matching-candidate compilation,
source/coverage guards, exhaustive axiom audit, both independent final review
axes and immediate final candidate verification remain required. Any necessary
correction is a new candidate; this draft's existence closes no acceptance gate.

The whole-fold measured executor, Chapter 4 exercises and logarithmic shape
theory, interval search/attainment, AVL balance/rotations, and the leftist
representation adapter remain outside this unit. In particular, the existing
leftist queue carrier and proofs are preserved; its smart fork can swap
children, so its unconditional content law remains a permutation statement.
These are retained later book obligations, not exclusions from the user's task.
