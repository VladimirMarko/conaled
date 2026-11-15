# Source maximum caches and the shared optional summary

This unit addresses FDSA Chapter 4, Exercise 4.11 and rows C04-075–076,
plus the key-set portion of C04-063 in the retained July 27, 2026
[chapter ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter04-obligations.md).
It is a new Lean development against the recorded source analysis, without a
claim of another manuscript read. Existing shape and inorder erasure laws
retain their ownership of the other C04-063 observations.

## Raw representation and local operations

`Applications.Trees.MaximumCache` retains the source carrier
`BinaryTree (α × α)`. A nonempty node has a key and a raw maximum annotation.
`mx` inspects only the constructor and root annotation: nil returns `none`,
and a node returns `some` of its stored annotation. Thus `mx t = none` if and
only if `t = nil`, even for invalid raw caches. This needs no typeclass on α.

The source smart constructor `nodeMx l a r` reads the two child roots and
stores `localMax (mx l) a (mx r)` with the supplied key and children. The local
operation starts from the actual key a and incorporates present child values.
An empty child contributes no invented zero, bottom or default inhabitant.
Construction, the independent `summary` fold and all cache transport laws
require only `Max α`. Greatest-element meaning has a separate ordered owner.

The recursive `invarMx` requires both child invariants and the actual local
root equation. The new root does not repair an invalid descendant. Neither
the reader nor the constructor calls a representation adapter or traverses a
child. Equality of ordinary tree values makes no physical-sharing claim.

## Explicit adapters consume generic correctness

The existing `Trees.Cached` needs an empty summary. Its annotation type is
therefore `Option α`, with empty value `none` and combining operation `combine`
that always produces `some (localMax ...)`.

`lift` maps every raw annotation b to `some b`, preserving keys and shape.
Its reader, key-erasure and smart-node laws are exact. The equivalence
`invarMx_iff_valid_lift` identifies the source invariant with generic validity
of the lifted tree. `nodeMx_valid_iff` then consumes
`Cached.smartNode_valid_iff`; `mx_eq_summary` consumes `Cached.read_eq_fold`.
There is no duplicate induction proving generic cached-fold correctness.

The reverse `project` adapter uses each node's actual key as the `getD`
fallback for an absent annotation. `project_lift` is unconditional. For the
other direction, generic validity is sufficient for `lift_project`,
`project_valid` and `mx_project`. It is not necessary for the inverse identity:
an all-present cache can round-trip while storing numerically wrong maxima.
An absent annotation at a nonempty node prevents an unconditional inverse law.
Key erasure is preserved by projection on every input, including invalid ones.

`annotate` is an explicit client of the generic full-tree annotation pass,
followed by the representation projection. It yields a valid source cache,
the original erased tree, the correct summary and the same lifted generic
annotation. This client performs full-tree work; it is not the local smart
constructor and no one-pass, allocation or machine-time bound is claimed.

## Independent maximum and occurrence-preserving observations

`Applications.Trees.MaximumCacheObservations` requires `LinearOrder α` and
proves `summary_eq_max?_inorder` using the actual shared `Trees.fold_fusion`.
The node algebra is proved from the pinned `List.max?_cons'`, `max?_cons`,
`List.foldl_append` and `List.foldl_cons` APIs. It uses the optional `List.max?`
interface directly, with no silent identification with `List.maximum`.

`mx_eq_max?_inorder` gives the canonical optional maximum of the erased inorder
list for a valid source cache. Standard `List.max?_eq_some_iff` and the existing
inorder/set bridge yield `mx_eq_some_iff`:

```
mx t = some m ↔
  m ∈ Trees.setTree (Cached.erase t) ∧
  ∀ x ∈ Trees.setTree (Cached.erase t), x ≤ m.
```

This includes attainment as well as the upper bound. `Trees.setTree_map` adds
the general image law at the existing independent set-observation owner. It
uses canonical inorder mapping and membership, accepts arbitrary functions
between independent universes and requires no injectivity or label equality.
The erased-key specialization consumes that theorem. The existing
`Cached.inorder_erase` separately preserves order and every occurrence; taking
a set or a maximum may forget that information.

## Connected cases and validation boundary

`Examples.TreeMaximumCache` covers empty labels, singleton construction,
repeated maxima, asymmetric children in both directions, and keys -5, -2, -9
whose maximum is -2. It exercises actual source smart nodes, their generic
counterparts, both adapters and the generic annotation pass. A forged child
remains invalid even when the parent's local and global maximum are correct.
An absent optional annotation demonstrates the failed unconditional round trip;
a wrong all-present cache demonstrates that validity is not necessary for it.

The public application aggregate reaches this example. Focused checks include
the new client and affected structural, cached and completeness clients. The
audit enumerates every declaration of the four changed or new formal modules,
including private and generated declarations. Exact candidate checks, statement
assessment, both source reviews and final comparison belong to local CTB
checkpoint evidence. Final 76-row Chapter 4 qualification is separate; receiving
whole-library build, exhaustive audit and final acceptance remain pending.
