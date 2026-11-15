# Stack/list implementation evidence (in progress)

Requirements chapter02.md version1. Base82501d108f33c62d21b5e0d0f7d2376b902d8d49.
Public mathematics from book pp7–11: generic stack operations with observable
empty head/tail failure, List/custom realizations, generic append preserving
ordinary concatenation. Source integer update decreases even negative indices
until empty, so a negative precheck is not an execution-cost refinement.

First case, independently expected: append the stack holding [1,2] to [3]
observes [1,2,3], both originals remain valid; empty tail fails while the tail
of [1] succeeds with an empty stack. These list propositions follow by ordinary
reduction, but the generic stack/operator-to-list theorem and custom-stack
connection are missing at the baseline. This is a missing public connection,
not a manufactured failing syntax/import test.

Implementation will use operation-only Ops and separate Laws relative to a
possibly nonfunctional relation to List. The generic append calls only Ops,
uses an explicit sufficient fuel bound proved for every related input, and
counts invoked stack primitives with an explicit unit convention. It will be
connected through existing Relational squares, without a new framework.

## First compiled layer

Applications.Sequences.AbstractStack and Examples.AbstractStack compiled in the
pinned offline Nix shell, current source prior to integration/commit. Public
appendRun_correct derives both output relation and exact4*n+1 primitive-call
count from actual operator execution. appendSquare and headSquare are pasted
using Relational.compose for appendHead_correct. List/direct append and the
separate inductive Stack exercise the same generic theorem. Cases cover the
nonempty append, excess fuel, empty left operand, empty tail failure and a
successful empty tail. No integrated acceptance is asserted. Two local proof
issues (over-decomposition of arithmetic equality and an unused change tactic)
were corrected; no public claim or independent expected result changed.

Statement review: each primitive count is explicitly a unit operator invocation;
no cell allocation or Lean-runtime cost is inferred. Fuel is an external
sufficient bound in the input relation, not a hidden observation available to
abstract code. The arbitrary relation may encode a validity invariant; concrete
List and Stack instances establish satisfiability and observable failures.

## All source integer indices

IntegerUpdate and Examples.SharedListIntegers compiled through the focused
669-job r9 check, with source hashes in validation/chapter02-integer-ordered-focused-r9.json.
The independent negative-index expectation was failure after n+1 structural
visits, including empty, for every negative integer. The implementation
decrements the integer at each recursive step; it does not shortcut negative
values. Nonnegative executions equal the existing Nat traversal even at the
raw-fuel boundary, and valid success inherits copied-prefix/tail-identity
results. updateIntegerRun_correct and updateIntegerSquare connect both signs to
the independent direct-list specification. Concrete -1 and -20 indices on the
three-element list both fail after four visits. Replacing index1 returns the
expected list while retaining the old version and the untouched suffix root.
The final proof correction used the nondeprecated integer-cast lemma; no
statement or evaluation rule changed.
