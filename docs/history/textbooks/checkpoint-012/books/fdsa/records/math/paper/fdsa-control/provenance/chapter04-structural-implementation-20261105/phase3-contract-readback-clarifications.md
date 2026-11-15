# Phase 3 contract readback clarifications

These clarifications were identified during complete readback of the new design notes. They add no implementation or new scope and do not modify any saved note. Read this file together with the frozen contracts.

## Exact cache parameter types

The four proposed cache definitions have these exact parameter and result types, with arbitrary `α : Type u`:

```lean
ch (t : BinaryTree (α × (Bool × Nat))) : Bool × Nat :=
  Trees.Cached.read (true, 0) t

nodeCh (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) :
    BinaryTree (α × (Bool × Nat)) :=
  Trees.Cached.smartNode (true, 0) Trees.completeHeightStep l a r

invarCh (t : BinaryTree (α × (Bool × Nat))) : Prop :=
  Trees.Cached.Valid (true, 0) Trees.completeHeightStep t

annotateCh (s : BinaryTree α) : BinaryTree (α × (Bool × Nat)) :=
  Trees.Cached.annotate (true, 0) Trees.completeHeightStep s
```

In particular, the annotator's input is the unaugmented `s : BinaryTree α`. The paragraph introducing the abbreviated definitions in `phase3-completeness-frozen-contract.md` types the observation input `t` as augmented; that contextual sentence must not be interpreted as a restriction of `annotateCh` to an already augmented input. Its annotation-law section already gives the intended unaugmented `s` type. The explicit signatures above remove that presentation ambiguity.

The new module remains `Trees.CompleteCache`; all four definitions and fourteen laws keep their frozen names and meanings. These snippets remain design expressions, not compiled source.

## Equality restriction

The MCS contract expressly permits decidable natural-number equality in `completeHeightStep` and natural-number comparison in candidate selection. Its warning about deciding a proposition as a substitute for the equality-free bonus concerns deciding `Complete`, tree equality, or label equality through hidden helpers. It does not prohibit the two permitted arithmetic decisions. Logical uses of structural membership, completeness, and equality remain necessary in theorem statements and proofs.

## Case-table notation

The saved case table uses ordinary parentheses around tree expressions. Its literal text `BinaryTree\ Empty` denotes the type `BinaryTree Empty`; the backslash is a typesetting artifact, not Lean source. Likewise, `C_4` and `P_2` in that table denote the concrete `C4` and `P2` definitions immediately below the table. The code-style tree definitions and all numeric expected values are unchanged.

## Identity metadata

The `lines` field recorded for the manuscript PDF in the input identity JSON is a raw byte-splitting count, not a page count or a claim of textual line coverage. The actual primary-source read coverage for this phase is PDF pages 57, 58, 62, 63, and 64, recorded separately by tool receipt `e5d411`. The manuscript SHA-256 and byte size are the identity checks. No manuscript or render copy was added to the project.
