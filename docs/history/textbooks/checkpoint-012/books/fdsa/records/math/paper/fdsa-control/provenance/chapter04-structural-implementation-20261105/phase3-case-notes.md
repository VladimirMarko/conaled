# Chapter 4 phase 3: expected values and distinguishing cases

## Status and conventions

These are independent mathematical expectations for later checked examples, not executed Lean results. No examples have been implemented or compiled in this phase. Cases support C04-038–041 and C04-074 and the shared Boolean completeness bridge; they do not replace universal proofs or close other Chapter 4 obligations.

Use (E) for the empty tree, (N(a,l,r)) for a node, and (S(a)=N(a,E,E)) for a singleton. Height counts internal nodes on the longest root-to-empty path. Node count counts internal nodes. The whole summary is `(complete flag, height)`; the MCS candidate's cached height is a separate field.

The source and API identities are bound by `phase3-design-input-identities.json` and `phase3-existing-api-bindings.json`. All labels in the numeric examples are natural numbers only to make expected values explicit; the public algorithms and theorems remain arbitrary-label and equality-free.

## Pure summary and maximal structural subtree matrix

| Case | Tree | Whole summary | Exact MCS result | Result height / nodes | Purpose |
| --- | --- | --- | --- | --- | --- |
| Empty labels | (E : BinaryTree\ Empty) | `(true, 0)` | (E) | 0 / 0 | No inhabitance or equality assumption. |
| Singleton | (S(a)) | `(true, 1)` | (S(a)) | 1 / 1 | Both empty children are complete. |
| Complete sample | (B=N(9,S(3),S(7))) | `(true, 2)` | (B) | 2 / 3 | Complete original root is returned intact. |
| Left asymmetric | (L=N(9,S(3),E)) | `(false, 2)` | (S(3)) | 1 / 1 | Larger left candidate beats the empty right candidate. |
| Right asymmetric | (R=N(9,E,S(7))) | `(false, 2)` | (S(7)) | 1 / 1 | Symmetric non-tie choice. |
| Repeated complete labels | (N(5,S(5),S(5))) | `(true, 2)` | The whole tree | 2 / 3 | Completeness depends on shape, not distinct labels. |
| Repeated asymmetric labels | (N(5,S(5),E)) and (N(5,E,S(5))) | Both `(false, 2)` | (S(5)) in each | 1 / 1 | The same result does not identify the two different input shapes. |
| Equal-height incomplete children | (T=N(10,N(20,S(21),E),N(30,E,S(31)))) | `(false, 3)` | (S(21)) | 1 / 1 | Child flags matter, and equal candidate heights prefer left. |
| Tall branch versus better candidate | (U=N(0,C_4,P_2)), defined below | `(false, 5)` | (P_2) | 2 / 3 | Choose by best candidate height, not whole child height. |

The first complete sample is the existing `TreeBasicObservationsExamples.sample`. The repeated asymmetric pair corresponds to the existing `leftRepeated` and `rightRepeated`. Reuse those exact examples when it keeps the later module's scope clear; do not alter their definitions or assume their prior author-only compilation status has become a pass.

For the tall-branch case, define:

```text
C4 = N(1, N(2, N(3, S(4), E), E), E)
P2 = N(6, S(5), S(7))
U  = N(0, C4, P2)
```

Independently, `C4` has height 4 and 4 nodes, but its largest complete structural subtree is `S(4)`, of height 1. `P2` is complete with height 2 and 3 nodes. Thus `U` has height 5 and 8 nodes while its selected candidate is exactly `P2`. Choosing by the child whole-height field would incorrectly prefer the left branch.

For the equal-height incomplete-child case, both children of `T` have height 2, but neither is complete. The whole tree has height 3 and 5 nodes. Its complete nonempty structural subtrees are exactly `S(21)` and `S(31)`; both have height 1 and one node. The frozen tie rule returns `S(21)`, yet `S(31)` is also a maximizer. No uniqueness conclusion is valid.

## Structural counterexample to recombining candidates

For the same `T`, the synthetic tree

```text
V = N(10, S(21), S(31))
```

is complete, has height 2 and 3 nodes, and uses labels drawn from `T`. Nevertheless, `Subtree V T` is false. The structural subtrees of `T` are the whole `T`, its two original height-2 children, the two singleton children, and the empty tree. None is `V`.

This must become an explicit checked negative example, using structural decomposition or equivalent constructor discrimination. It distinguishes structural containment from pruning/recombining and from equal or included label sets. A faulty algorithm that rebuilds a root from the two selected best children would produce `V` and violate C04-039.

The equality-free implementation may still have proof statements about equality and concrete example inequalities. Those logical specifications are distinct from executable equality tests inside `mcsSummary` and its computation helpers.

## Cache construction and validity matrix

Here `E` also denotes an empty augmented tree; let the payload annotation be a pair `(Bool, Nat)`. The source-facing cache namespace is `Trees.CompleteCache`.

1. **Empty cache.** `ch E = (true, 0)` and `invarCh E`. This includes an empty tree with labels of type `Empty`.
2. **Valid complete cache.** Build `cachedB = nodeCh (nodeCh E 3 E) 9 (nodeCh E 7 E)`. It erases to `B`, satisfies `invarCh`, and has `ch cachedB = (true, 2)`. Consume `invarCh_nodeCh_iff`, `erase_nodeCh`, and `ch_correct`.
3. **Valid asymmetric cache.** Build `cachedL = nodeCh (nodeCh E 3 E) 9 E`. It erases to `L`, satisfies `invarCh`, and has `ch cachedL = (false, 2)`. A valid cache need not describe a complete tree.
4. **Whole-tree annotation.** For each of `B`, `T`, and `U`, consume `invarCh_annotateCh`, `erase_annotateCh`, and `ch_annotateCh`. Expected reads are respectively `(true, 2)`, `(false, 3)`, and `(false, 5)`.
5. **Repeated labels.** Annotation of `N(5,S(5),S(5))` has the same expected shape summary `(true, 2)` while preserving all repeated labels under erasure.

These examples should combine direct expected values with public correctness and preservation laws; unfolding only the cache definition does not exercise its semantic connection.

## Invalid-descendant counterexample

Use direct augmented node construction for the intentionally malformed child, and smart construction for its parent:

```text
g         = N((4, (true, 1)), E, E)
badChild  = N((3, (true, 2)), g, E)
rightGood = nodeCh (nodeCh E 5 E) 6 (nodeCh E 7 E)
badParent = nodeCh badChild 9 rightGood
```

The singleton `g` is valid. The erased shape of `badChild` is asymmetric, with height 2 and 2 nodes, so its correct summary is `(false, 2)`. Its stored summary `(true, 2)` is wrong, hence `invarCh badChild` is false.

The smart constructor does compute the root of `badParent` from its children's stored summaries. Both stored child flags are true and both stored child heights are 2, so `ch badParent = (true, 3)`. This root-local equation is correct as a computation, but the erased parent is incomplete: its left child is incomplete. Its actual height is 3 and node count is 6. Thus `invarCh badParent` is false, and unconditional correctness of `ch` would be false.

A separate whole-tree reannotation `annotateCh (Cached.erase badParent)` is valid, has exactly the same erased tree, and reads `(false, 3)`. This construction explicitly traverses the erased tree; it is not an action performed by `nodeCh` and does not license a claim that smart construction repairs invalid descendants.

This case must consume the recursive invariant's node equation or `invarCh_nodeCh_iff`, not only assert a concrete annotation mismatch.

## Public theorem consumption and case names

Example namespaces should be `TreeCompleteSummaryExamples`, `TreeCompleteCacheExamples`, and `TreeMaximalCompleteSubtreeExamples`, matching their proposed files. Concrete theorem names may be chosen during later source authorization; the cases, expected values, and required public-law uses above are the frozen content.

Pure examples must connect `completeBool_eq_true_iff`, `completeHeight_height`, and label invariance to independently expected shapes. MCS examples must use `mcs_subtree`, `mcs_complete`, `mcs_height_maximal`, `mcs_numNodes_maximal`, and the explicit left/right choice laws. At least one nontrivial competing complete subtree should be supplied to each maximality law. Neither universal theorem may be replaced by an example-only fact.

Nothing in this note is compiler output or a Spec/Standards review. All concrete claims remain mathematical expectations to be encoded and checked after source release.
