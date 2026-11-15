# Phase 2 weighted-path contract and worked expectations

Frozen before source writing, after Phase 1 commit `5b17c8e4a962a8e79251eda1b5f94f97a3d4cc34`. Ownership remains the existing Chapter 4 author assignment: two new weighted-path modules only, plus new reports here. No earlier source or report is to be edited.

## Operations and statements

Use `BinaryTree Nat` and namespace `Trees`. The exact assigned source recurrences on printed pages 49–50 are:

```lean
sumTree : BinaryTree Nat → Nat
sumTree .nil = 0
sumTree (.node w l r) = sumTree l + w + sumTree r
wpld : Nat → BinaryTree Nat → Nat
wpld d .nil = 0
wpld d (.node w l r) =
  (d + 1) * w + wpld (d + 1) l + wpld (d + 1) r
wpl0 (t : BinaryTree Nat) : Nat := wpld 0 t
wpl : BinaryTree Nat → Nat
wpl .nil = 0
wpl (.node w l r) = sumTree (.node w l r) + wpl l + wpl r
```

The nil/node equations are public as `sumTree_nil`, `sumTree_node`, `wpld_nil`, `wpld_node`, `wpl_nil`, `wpl_node`. `wpl` is defined independently of `wpld`. The main new public statements are:

```lean
wpld_eq_offset (d : Nat) (t : BinaryTree Nat) :
  wpld d t = d * sumTree t + wpl t
wpl0_eq_wpl (t : BinaryTree Nat) : wpl0 t = wpl t
```

The offset theorem is universal in the arbitrary incoming depth, all finite trees and all natural weights including zero. It needs no positive-weight premise. The root contributes `(d+1)*w`, so at depth zero a single node contributes its full weight. A subtree-sum recurrence is a value specification here; no runtime-improvement claim is made. The existing Huffman theorem uses labelled leaves with root-leaf depth contribution zero, so its theorem is not substituted for this statement.

## Independently expected applications

`TreeWeightedPathsExamples.sample` will have root 3 and children 5 and 7: sum 15 and weighted path length `3 + 2*5 + 2*7 = 27`. At incoming depth 2 the direct definition gives `3*3 + 4*5 + 4*7 = 57`, and the offset formula independently predicts `2*15+27 = 57`. The generic sample-at-depth specialization will consume `wpld_eq_offset`; the zero-depth example will consume `wpl0_eq_wpl`.

A left chain with weights 3,5,7 has the same total 15 but weighted path length `3 + 2*5 + 3*7 = 34`. Its incoming-depth-2 value is 64. A connected comparison will establish equal total weights and strictly different zero-depth path lengths, exposing accidental dependence on total weight alone.

A singleton with arbitrary weight `w` has zero-depth result `w`; a numeric 7 specialization will consume that general fact. An empty tree has all zero observations even at arbitrary incoming depth. A zero-weight root with child 7 has result 14, showing that a zero-weight node still increases the depth of descendants. These expectations precede implementation and are not altered to satisfy a compiler.

This is an uncompiled source contract. Root owns all actual-type, compiler, complete-check, audit, independent-review and immediate-verification evidence. No chapter coverage or shared unit is accepted by this contribution.
