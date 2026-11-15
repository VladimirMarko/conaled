# Separate future scope: almost-complete structural facts

## Boundary

This note records a later design boundary only. It is not part of the present completeness-summary, cache, or maximal-complete-subtree author phase. It reserves no new source path, authorizes no implementation, modifies no existing Shape or structural API, and grants no review or coverage credit. C04-046 and C04-059–060 remain whole Chapter 4 obligations under original base `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2` and the unchanged 76-row inventory.

The exact development input is XT02 `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe`, `Applications/Trees/Shape.lean`, SHA-256 `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3`. It was not accepted in this assignment. Its existing definitions are:

```lean
AlmostComplete t := t.height ≤ minHeight t + 1

almostComplete_children (a : α) (l r : BinaryTree α)
    (ht : AlmostComplete (.node a l r)) :
  AlmostComplete l ∧ AlmostComplete r
```

The structural `Subtree` interface is the immutable authored input bound separately in the phase 3 identity record. Its qualification and reception remain root's responsibility.

## Structural closure to prove later

The future mathematical statement for C04-046 is:

```lean
AlmostComplete t → Subtree s t → AlmostComplete s
```

It has no equality or order assumptions on labels. Induction on the structural containment derivation uses reflexivity at the root and the existing `almostComplete_children` theorem when descending left or right. This statement covers every original descendant, including the empty tree; it does not cover arbitrary pruning or tree reconstruction.

## Constructor characterization to prove later

Exercise 4.8, printed p. 56 / PDF p. 62, permits only completeness, almost-completeness, height, arithmetic, Boolean operations, and the two child trees in its right-hand formula. The proposed exact proposition-level characterization is:

```lean
AlmostComplete (.node a l r) ↔
  AlmostComplete l ∧ AlmostComplete r ∧
    (l.height = r.height ∨
      (l.height = r.height + 1 ∧ Complete r) ∨
      (r.height = l.height + 1 ∧ Complete l))
```

The right-hand side uses no `minHeight` and constructs no new tree. `minHeight` may be used in the proof against the existing specification. When child heights are equal, both children may be merely almost complete. When they differ by one, the shorter child must be complete. The symmetric alternatives retain both left-heavy and right-heavy cases.

This is a proposed future theorem, not an already proved or typechecked API. A later assignment must freeze its name, ownership, proof, and examples separately, preserving the complete scope of C04-059–060.

## Why the shorter-child condition is necessary

Let the left child be a complete height-3 tree with 7 internal nodes and minimum height 3. Let the right child be an asymmetric height-2 tree with 2 internal nodes and minimum height 1. Both children are almost complete, and their heights differ by one. Their parent has height 4 and minimum height 2, so it is not almost complete.

Consequently, the weaker formula “both children almost complete and their heights differ by at most one” is false. The shorter right child in this example is not complete, exactly the condition excluded by the proposed formula.

Do not conflate this property with local height balance, the existing height-optimality theorems, or a claim that every tree of minimum possible height is almost complete. No such extension is part of the current phase. The maximal-subtree algorithm selects **complete** structural subtrees; it must not silently replace its shared completeness Boolean with this future almost-completeness predicate.
