# AVL height bounds and attained minimum size

This bounded increment addresses FDSA Chapter 9 rows C09-010–017 and
C09-046–051. It uses the accepted cached AVL foundations and the existing
`BinaryTree`, cached-fold and tree-observation interfaces. The implementation
owners are `Applications/Trees/AVL/Height.lean` and `Examples/AVLHeight.lean`.
Exact-candidate validation and the independent review records establish source
qualification; this correspondence note is not an execution receipt.

The source is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, edited by Tobias Nipkow, version July 27, 2026. The height argument
is on printed pages 106–107, physical PDF pages 112–113. Exercise 9.2 is on
printed page 111, physical page 117. The pinned PDF SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Canonical requirements remain in
`docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md`,
under the complete CTB-28 owner. Its Chapter 4/5/6 prerequisite obligations are
unchanged. The [Chapter9 continuation paper](fdsa-avl-continuation.md)
retains the original primary-reading attribution. The height-preparation pass
read the canonical rows, root's earlier exact-coefficient argument and selected
Mathlib definitions/proofs at `56a005855ea17e0b0958f73ec801ae140b0a1679`;
it did not newly render/inspect the PDF or read the Isabelle/AFP companions.
The useful proof mathematics is in this note and its source owners.
[CTB-116 and CTB-78](../textbooks/CTB.json) distinguish donor qualification from
current receiving acceptance. No new visual PDF reading is inferred here.

## Measures and assumptions

For a raw tree `t`, `t.height` is its actual structural height, with empty height
zero. `t.numLeaves` counts external empty leaves, including the one leaf of an
empty tree. `t.numNodes` counts internal labelled nodes. The existing exact law
is `t.numLeaves = t.numNodes + 1`. None of these measures counts distinct labels.

`Trees.AVL.Balanced` recursively requires balanced children and both natural
height inequalities. The accepted `height_balance_iff` connects these inequalities
with the intended signed integer absolute difference at most one. The shape
condition ignores payload values and cached heights. All universal shape bounds
therefore quantify over arbitrary `Type u` payloads, with no order, equality,
inhabitance, injectivity or distinctness requirement.

For a cached tree, `Valid` combines balance of `Cached.erase t` with recursive
`CacheValid`. Erasure preserves actual height, nodes and leaves unconditionally.
The source-valid bound wrappers use these erasure laws. Stored `ht t` is used
only after `ht_eq_height t h` supplies the necessary cache-correctness evidence.
A balanced raw shape with a wrong root annotation does not satisfy that premise.
Search ordering is absent from all these bounds and minimum comparisons.

## Fibonacci lower bound

The mathematical Fibonacci sequence is the pinned `Nat.fib`, with
`Nat.fib_zero`, `Nat.fib_one` and `Nat.fib_add_two`. Its recurrence's summand
order can be exchanged by commutativity. The actual `Nat.twoStepInduction`
provides the two base cases and the step from indices n and n+1 to n+2.
The existing executable Fibonacci implementation is optimized; the use of its
mathematical recurrence here makes no naive double-recursion runtime claim.

The public shape theorem states

\[
  \operatorname{Balanced}(t)
  \Longrightarrow F(h(t)+2)\leq\operatorname{leaves}(t).
\]

Its structural induction separates the two orderings of child heights. Suppose
the left height is l, the right height is r, and r≤l. The parent height is l+1.
Balance also gives l≤r+1, so Fibonacci monotonicity supplies
`F(l+1) ≤ F(r+2)`. The recurrence and the child hypotheses give

\[
 F(l+3)=F(l+2)+F(l+1)
 \leq F(l+2)+F(r+2)
 \leq\operatorname{leaves}(left)+\operatorname{leaves}(right).
\]

The other ordering is symmetric. The empty case is F2=1. This argument uses
natural indices without predecessor subtraction. Applying it to erasure yields
the cached `Valid` theorem on actual height; the stored-height corollary then
uses the already established cache bridge.

## Exponential and exact logarithmic bounds

The real constant is the existing `Real.goldenRatio`, namely
`(1 + Real.sqrt 5) / 2`. Its pinned public properties include
`Real.one_lt_goldenRatio`, `Real.goldenRatio_lt_two`, `Real.goldenRatio_sq`
and the natural-power recurrence. The two-step Fibonacci argument proves,
for every natural n,

\[
 \varphi^n\leq(F(n+2):\mathbb R).
\]

At zero both sides are one. At one the inequality follows from φ<2=F3.
The recurrence `φ^(n+2)=φ^(n+1)+φ^n` adds the two preceding inequalities.
Composing with the shape Fibonacci theorem gives
`φ^(t.height) ≤ (t.numLeaves : Real)`.

The logarithmic theorem retains the exact coefficient:

\[
 (h(t):\mathbb R)
 \leq \frac{1}{\log_2\varphi}\,\log_2(\operatorname{leaves}(t)).
\]

Both the logarithm's base condition `1 < (2 : Real)` and positivity of
`φ^height` are explicit in the proof. Monotonicity and `Real.logb_pow` give
`height * logb 2 φ ≤ logb 2 leaves`. Since φ>1, `logb 2 φ` is positive, so
division preserves the inequality. The proof does not require
`0 < logb 2 leaves`; the empty tree has leaves=1 and logarithm zero.

The node-count corollary substitutes `(t.numNodes : Real) + 1` inside the
logarithm. Removing the `+1` would make the singleton assert `1 ≤ 0`.
The cached wrappers distinguish the actual height from `ht`; using `ht` requires
`Valid` and the exact existing height equality. The resulting bounds describe
tree size and height, without an operation-cost model or benchmark claim.

### Checked coefficient correspondence

The public numerical statement is the strict exact enclosure

\[
 \frac{1440}{1000}
 <\frac{1}{\log_2\varphi}
 <\frac{1441}{1000}.
\]

It justifies the printed approximation 1.44 while explicitly excluding both
equality to 1.44 and use of 1.44 as an upper bound. The height theorem keeps the
exact real multiplier.

The proof route uses rational bounds `809/500 < φ < 16181/10000`, obtained from
φ²=φ+1 and φ>1 by exact polynomial signs. The existing identity
`Real.goldenRatio_mul_fib_succ_add_fib` relates powers to Fibonacci numbers:

\[
 \varphi^{36}=14930352\varphi+9227465,
 \qquad
 \varphi^{85}=259695496911122585\varphi+160500643816367088.
\]

The pinned proof-producing `NormNum.NatFib` extension proves the numeral values
using doubling identities. Exact rational arithmetic then establishes
`φ^36 < 2^25` and `2^59 < φ^85`. Applying the strictly increasing natural
logarithm and using positive `log φ` yields

\[
 \frac{36}{25}<\frac{\log 2}{\log\varphi}<\frac{85}{59}
 <\frac{1441}{1000}.
\]

The left endpoint is exactly 1440/1000. `Real.inv_logb` and the definition of
`Real.logb` connect this quotient with the public coefficient. No floating-point
sample, Python calculation or unproved decimal approximation supplies a proof.

## Executable Fibonacci trees and exact minima

`fibTree : Nat → BinaryTree Unit` is an actual unannotated constructor program:

\[
\begin{aligned}
 T_0&=E,\\
 T_1&=N((),E,E),\\
 T_{n+2}&=N((),T_{n+1},T_n).
\end{aligned}
\]

The displayed constructor order is Lean's label/left/right order. The book's
notation places the label between the children. The constructor equations,
balance, exact height n and exact leaves F(n+2) refer to this same executable
program. They are not only statements about a detached numeric recurrence.

The two base trees have heights0/1 and leaves1/2. In the step, exact child
heights n+1 and n establish the local balance condition and parent height n+2.
The child leaf equations and Fibonacci recurrence establish the parent's count.
The resulting public laws are exposed independently so that callers can inspect
the height, count and invariant obligations separately.

For every balanced tree t, the universal lower bound and the witness's count
give `leaves(fibTree(t.height)) ≤ leaves(t)`. For every prescribed n, `fibTree n`
has height n, is balanced and has F(n+2) leaves. Together these statements prove
the minimum at the prescribed height. Counting alone would be insufficient:
`fibTree 4` and a perfect height3 tree both have eight leaves.

Define the minimum sequence observationally by `M n = (fibTree n).numLeaves`.
The actual constructor equations give M0=1 and M1=2, and the node leaf equation
gives `M(n+2)=M(n+1)+M n`. There is no underspecified minimum over a potentially
empty family. Attainment uses Unit-labelled shapes; an arbitrary uninhabited
payload type cannot support a positive-height tree.

Correct annotation supplies cached attaining witnesses. Existing
`valid_annotate_iff`, `erase_annotate`, `Cached.height_erase` and
`Cached.numLeaves_erase` establish validity and preserve the height/count facts.
Universal comparisons retain arbitrary payload universes, independently of
the concrete Unit witness. Node minimality follows from the leaf comparison
using `numLeaves_eq_numNodes_succ` on both trees, and the witness's exact node
equation is `numNodes(fibTree n) + 1 = F(n+2)`.

## Canonical correspondence

| Rows | Public result or reused primary interface | Essential boundary |
|---|---|---|
| C09-010 | `Nat.fib_zero`, `Nat.fib_one`, `Nat.fib_add_two`; actual use of `Nat.twoStepInduction` | Mathematical recurrence; no naive-Fibonacci cost assertion. |
| C09-011 | `fib_height_le_numLeaves`, `fib_height_le_numLeaves_of_valid` | Actual height and external leaves; balance is necessary. |
| C09-012 | `Real.goldenRatio` and its >1, <2, square and power properties | The actual pinned real constant. |
| C09-013 | `goldenRatio_pow_le_fib` | Every natural index, with both bases and recurrence. |
| C09-014 | `goldenRatio_pow_height_le_numLeaves`, `_of_valid` | Natural/real conversion of the same leaf count. |
| C09-015 | `height_le_logb_numLeaves`, `_of_valid`, node-count and stored-height corollaries | Empty included; nodes+1; stored height requires validity. |
| C09-016 | `height_coefficient_bounds` | Strict rational enclosure and exact multiplier. |
| C09-017, C09-050 | `fibTree_minimal`, `_of_valid`, attainment packages and leaf recurrence | Universal lower bound plus an actual witness of the prescribed height. |
| C09-046 | `fibTree`, `fibTree_zero`, `fibTree_one`, `fibTree_add_two` | Concrete executable unannotated tree construction. |
| C09-047 | `balanced_fibTree`, `valid_annotate_fibTree` | Recursive balance and correctly restored caches. |
| C09-048 | `height_fibTree`, `height_annotate_fibTree` | Exact height, independently from counting. |
| C09-049 | `numLeaves_fibTree`, `numLeaves_annotate_fibTree` | External leaves F(n+2). |
| C09-051 | `numNodes_fibTree_add_one`, `fibTree_numNodes_minimal`, `_of_valid` | Derived node translation; repeated labels still count as occurrences. |

## Independent cases and statement review

The expected cases were saved before implementation. The client module connects
them to the public results, including results that are also reducible on a small
concrete tree. They supplement the general proofs and do not replace them.

| Case | Independent expectation | Connected evidence |
|---|---|---|
| H01 | Empty: height0, leaves1, logarithm0. | `empty_bounds`, `cached_empty_bounds`, `empty_logarithm`. |
| H02 | Singleton: height1, nodes1, leaves2; node-only logarithm fails. | `singleton_nodes_log_bound`, `singleton_node_only_log_fails`, cached bound. |
| H03 | Height2 minimum has three leaves; perfect height2 has four. | `minimum_two_observations`, `perfectTwo_minimum_comparison`, strict comparison. |
| H04 | A height3 one-sided chain has four leaves<F5, even with correct caches. | `chainThree_not_balanced` consumes the universal bound; `cached_chain_observations` preserves the cache/balance distinction. |
| H05 | Eight leaves can occur at heights4 and3. | `equal_leaves_different_heights` uses separate witness-height and count laws. |
| H06 | Repeated Unit labels: four nodes/five leaves at height3. | Witness observations, actual inorder and universal minimum comparison. |
| H07 | A singleton storing3 has actual height1/leaves2; the stored Fibonacci bound fails. | Actual-height bound on erasure, stored-bound counterexample, cache invalidity and repaired bounds. |
| H08 | Empty trees over PEmpty are included; positive-height attainment is impossible there. | Arbitrary-universe empty bounds and `empty_payload_no_positive_height`; attainment remains over Unit. |
| H09 | The exact coefficient is strictly greater than1.44 and below1.441. | `coefficient_enclosure`, `coefficient_not_le_one_point_four_four`. |
| H10 | Initial minimum leaves1,2,3,5,8 and nodes0,1,2,4,7. | Actual witness observations, constructor/leaf recurrence and shape/cached attainment. |
| H11 | Generic arbitrary-payload and Valid cached domains. | Generic bound/minimum consumers, checked against the exported elaborated signatures. |

Statement assessment must examine the actual quantified types, universe levels,
casts, recurrence indices, strict coefficient direction, invariants and witness
domains. Generated and private declarations are retained in the type export and
must not be miscounted as separately authored source obligations. The proof
audit checks the actual imported project root set and allowed axiom closure;
whole-library receiving acceptance is separately attributable.

The remaining AVL rotations, updates, balance-factor and generalized-balance
algorithms, Exercise9.1's separate requested proof route, other exercises,
operation-cost results, unfinished Chapter5 rows, remaining FDSA/PFDS work and
receiving integration obligations remain mandatory. These height/count results
make no physical-sharing, bit-cost, whole-update runtime or whole-book claim.
