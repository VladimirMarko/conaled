# Phase 1 author source and statement assessment

Status: UNCOMPILED. This is the source author's assessment in the existing
whole Chapter 4 loop, not independent Standards or Spec approval.

The implementation follows the previously frozen algorithm: left recursion,
root read from its returned suffix, then right recursion on that suffix tail.
It never repeatedly splits the original list with take/drop. Both recursive
sizes decrease from positive n; the requested size is the termination measure.
The safe core preserves arbitrary label types and has no Inhabited constraint.
Failure is explicit, including the empty-root-suffix branch.

The public bal_spec is a success implication, not a conclusion assumed by its
own premise: the premise is the result of executing bal. It gives the complete
ordered decomposition and exact node count. bal_exists separately supplies
all inputs with n <= length xs, so bal_succeeds_iff and bal_eq_none_iff express
both directions of the exact domain. The list reconstruction retains both
order and multiplicity. Suffix identity and length follow from the independent
inorder-length theorem and ordinary list take/drop laws.

The four wrapper inorder contracts and four node-count contracts keep the
length/node premise only where a prefix is requested. Full-list/full-tree
wrappers discharge that premise using their actual input length. Nil fallback
is explicit and confined to out-of-domain calls. Prefix clients preserve an
arbitrary suffix; no theorem infers tree equality merely from equal inorder.

Examples connect the generic results to a non-sorted three-node prefix with
two equal suffix elements, repeated labels, zero/too-short inputs, Empty label
types, and arbitrary tree inputs. The complete ten-node shape was independently
specified before the source, and matches the recorded Figure 4.3 assessment.
Concrete shape and height equalities use kernel decision reduction, not native
execution. Inorder, size and external-leaf observations consume public generic
results. The concrete height four is not claimed to supply any general height,
minimum-height, almost-completeness or strict-BST theorem.

Scope: source for C04-047..053 and the concrete Figure 4.3 part of C04-058.
C04-054..057, the strict-order connection in C04-058, and other original Chapter
4 obligations remain mandatory. Phase 2 adds actual call counting separately.

Validation: full source readback completed; local whitespace/staging identity
checks are recorded separately. No Lean/Lake/check/audit or dependency/output
writes were performed by this author. Source declarations are not reported as
elaborated types. Root must compile, inspect actual types and conduct the full
candidate gates and independent review under the original whole scope.
