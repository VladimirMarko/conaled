# Fixed-tolerance logarithmic height

The original height increment addresses FDSA Chapter 9 obligation **FDSA-9-61**. The canonical
owner is
`docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md`.
The Chapter Notes on printed page 116 state that every fixed positive balance
tolerance still gives logarithmic height. Exercise 9.4's pedagogical proof waiver
does not remove that mathematical claim from the formalization task. The ledger
explicitly permits the coefficient `d + 1`; an optimal exponential base is not
required.

The [height/operation-cost preparation](fdsa-height-updates.md#unqualified-preparation-for-measured-operation-costs)
retains its original author, exact paper/PDF identities and primary-reading
scope: printed pages 105–112 and 116 were individually inspected, with text
read for printed 105–116. This increment reuses that reading and the exact
canonical row. It does not claim a fresh reading or port of the alternative AFP
proof. Its pure height result is implemented. The later measured update/query
work and logarithmic cost composition are maintained in the linked papers;
the optional sharper minimum recurrence remains unqualified preparation.

## Measures and exact domains

The production owner is `Applications/Trees/HeightBalance/HeightBound.lean`, in
the existing `Trees.HeightBalance` namespace. It uses the existing binary-tree
measures and recursive `BalancedD` predicate. If `h` is actual height, `L` is the
number of external leaves and `N` is the number of internal nodes, then

\[
h(\mathrm{nil})=0,\qquad L(\mathrm{nil})=1,\qquad
N(\mathrm{nil})=0,\qquad L(t)=N(t)+1.
\]

At a node, both subtrees must themselves satisfy `BalancedD d`, and their heights
must differ by at most `d`. The pure results quantify over **every natural `d`**,
including zero, and arbitrary payloads `α : Type u`. They require no ordering,
decidable equality, inhabited carrier or cached annotation. A perfect tree is a
nonempty usable model at tolerance zero. The existing update-preservation regime
remains `1 ≤ d`.

The main statements are

\[
2^{\lfloor(h(t)+d)/(d+1)\rfloor}\le L(t),
\qquad
h(t)\le(d+1)\log_2 L(t),
\qquad
h(t)\le(d+1)\log_2(N(t)+1).
\]

For natural heights the displayed integer quotient is the ceiling of
`h(t)/(d+1)`. The real inequalities cast natural measures explicitly. They have
no additive constant, nonempty-tree premise or hidden restriction to tolerance
one. The coefficient depends on the fixed supplied tolerance.

## Threshold induction and ceiling rounding

Put `q = d + 1`, so `q > 0`. At a balanced node with child heights `a` and `b`,
the two local balance inequalities give

\[
\max(a,b)+1\le a+q,\qquad \max(a,b)+1\le b+q.
\]

The theorem `two_pow_succ_le_numLeaves_of_mul_lt_height` proves

\[
kq<h(t)\quad\Longrightarrow\quad 2^{k+1}\le L(t)
\]

by induction on `k`, generalized over the input tree. At zero, positive height
forces a node, and each child has at least one external leaf. In the successor
case, expand `(k+1)q = kq+q`. Each child's height is strictly greater than `kq`,
so the induction hypothesis applies to both balanced subtrees. Adding their
leaf bounds doubles the power. No minimum-size oracle or Fibonacci recurrence
is assumed.

For the ceiling theorem set

\[
k=(h+d)/q,\qquad r=(h+d)\bmod q.
\]

The exact natural division identities give `r + q*k = h+d` and `r ≤ d`.
Consequently `h ≤ q*k`. If `k = 0`, leaf positivity supplies `1 ≤ L`. If
`k = j+1`, expand and cancel to obtain `h = r+j*q+1`; therefore `j*q < h` and
the threshold theorem gives `2^(j+1) ≤ L`. Successor multiplication and the one
commuted product are normalized explicitly before invoking linear arithmetic.
The private `height_le_mul_ceil` helper supplies the independent rounding step.

This ceiling strength matters. The numerical data `d=2`, `h=4`, `L=2` satisfy
the floor-power estimate `2^(4/3) ≤ 2`, but violate `4 ≤ 3*log₂(2)`. This is an
arithmetic counterexample to that inference, not a claim that those are the
measures of a balanced tree.

## Taking logarithms and transporting observations

`BinaryTree.numLeaves_pos` supplies a strictly positive logarithm argument,
including the empty tree. Cast the ceiling-power inequality into the reals and
apply `Real.logb_le_logb` at base two. The identities for a natural power and the
logarithm of the base give `k ≤ log₂ L`. Multiplication by the nonnegative real
coefficient `d+1`, together with the proved rounding inequality, gives

\[
h\le(d+1)k\le(d+1)\log_2 L.
\]

The node formulation uses `BinaryTree.numLeaves_eq_numNodes_succ`; it does not
take the logarithm of a raw zero node count at nil.

The integer corollaries `height_le_mul_clog_numLeaves` and
`height_le_mul_clog_numNodes_add_one` use the same ceiling-power and rounding
proofs. `Nat.le_log_of_pow_le` gives k≤floor(log₂ L), and `Nat.log_le_clog`
then gives k≤clog₂ L. Multiplying the natural inequality by d+1 proves

\[
h(t)\le(d+1)\operatorname{clog}_2 L(t)
=(d+1)\operatorname{clog}_2(N(t)+1).
\]

These corollaries retain arbitrary payload universes and every natural d,
including0. They add no order, annotation, inhabitedness or nonempty premise.
They are convenient natural-number inputs to the measured work recurrences.
The sharper real bound and ordinary AVL golden-ratio bound remain unchanged.

The cached adapters use an arbitrary complete
`HeightAnnotation α σ`, with independent `σ : Type v`. `ValidD ann d t` provides
balance of `Cached.erase t` and correctness of the complete annotation. The
existing `Cached.height_erase`, `numLeaves_erase` and `numNodes_erase` identify the
actual measures of the erased and annotated trees. The `_of_valid` theorems
therefore transport the pure results without inspecting an annotation value.

The stored-height theorems `two_pow_ceil_ht_le_numLeaves`,
`ht_le_mul_logb_numLeaves` and `ht_le_mul_logb_numNodes_add_one` additionally use
`ht_eq_height`. A root summary containing the number 99 on a singleton remains a
balanced **shape**, but is not a valid height cache; the actual-height bound still
holds and the stored-height bound fails. Correctly constructing the complete
singleton annotation supplies the positive counterpart for every supplied
annotation algebra and every natural tolerance.

## Existing algorithms and ordinary AVL specialization

The clients live in `Examples/HeightBound.lean`. They keep the pure production
owner independent of AVL, update algorithms, Set refinement and resource models.

`insert_log_bounds` and `delete_log_bounds` apply the full-validity components of
the existing `validD_insert` and `validD_delete` theorems to the **actual local
programs**. They need only `LT α`, `DecidableLT α`, a positive tolerance and full
initial validity. No ordering laws or strict inorder are introduced for these
shape/cache consequences.

`mixed_history_node_bound` and `mixed_prefix_log_bounds` reuse the existing Set
laws' execution and prefix validity. The prefix length is any natural number,
including lengths past the word's end. Their `LinearOrder` and `SetValid`
premises belong to that existing history interface; the height proof itself
does not need them. There is no new history induction.

The positive-integer clients retain both facts from `int_tolerance_toNat`:
`1 ≤ D.toNat` and `(D.toNat : Int) = D`. The insertion client consumes the first
fact to justify the update and returns the second to identify the exact supplied
integer tolerance. A negative integer is not silently admitted by truncation.

For ordinary valid AVL trees, `AVL.validD_one_iff` supplies the generalized
tolerance-one premise. `ordinary_avl_bounds` consumes the new coefficient-two
result alongside the unchanged sharper result

\[
h(t)\le\frac{1}{\log_2\varphi}\log_2 L(t),\qquad
\frac{1440}{1000}<\frac{1}{\log_2\varphi}<\frac{1441}{1000}.
\]

Those golden-ratio statements and their proof owner remain unchanged. The
general bound supplements their ordinary specialization.

## Discriminating cases and public connections

The mathematical expectations were recorded before the draft implementation.
Finite measure calculations and negative cases are separate from the positive
public theorem applications.

| Case | Expected mathematics | Public connection or separation |
| --- | --- | --- |
| B01 | Nil has height 0, one external leaf and no nodes, at every natural tolerance. Arbitrary carriers and `PEmpty` need no payload witness. | `empty_shape_bounds`, `empty_cached_bounds` and `empty_carrier_bounds` consume pure and stored public bounds. |
| B02 | A perfect height-three tree is balanced at zero, with eight leaves and seven nodes; its logarithmic bound is sharp. | `perfect_three_power` and `perfect_three_log` use the new pure theorems after `perfect_three_balanced_zero`; a separate equality calculates the sharp value. |
| B03 | A three-node chain is balanced at two but not one. Attaching it beside a singleton gives height four and six leaves, in both orientations. | `chain_three_power` and `ceiling_boundary_power` consume ceiling and strict-threshold APIs with actual recursive balance proofs. |
| B04 | Ceiling exponents at heights 0, `q` and `q+1` are 0, 1 and 2. A floor bound alone can miss the logarithmic conclusion. | `ceiling_block_arithmetic` and `floor_power_log_gap` distinguish rounding strengths independently of any fabricated tree. |
| B05 | A stale singleton cache does not change actual height, but invalidates stored-height replacement. | `stale_singleton_actual_bound` uses the pure result; separate invalidity and failure proofs reject the stale cache. `annotated_singleton_bounds` uses the complete positive cache invariant. |
| B06 | A seven-node chain has height seven and eight leaves. It violates the coefficient-two bound but is balanced at six. | `chain_seven_bound` applies the supplied tolerance-six theorem; `chain_seven_rejects_coefficient_two` and `chain_seven_balance` expose the necessary tolerance premise. |
| B07 | Actual updates and arbitrary mixed histories preserve the full invariant on their established domains. | Raw update, full-history, every-prefix and exact positive-integer clients consume the existing preservation APIs and the new height theorem. |
| B08 | Ordinary AVL's sharper theorem remains available. Seven repeated nodes can contain only one distinct key. | `ordinary_avl_bounds` consumes both public bounds. `repeated_key_node_bound` succeeds, while `distinct_size_cannot_replace_nodes` rejects substituting inorder distinct-key cardinality. |

## Qualification boundary and next mathematics

The explicit logarithmic-height theorem is the requested FDSA-9-61 outcome.
The argument does not prove costs for arbitrary annotation callbacks, runtime
complexity, physical allocation or a relation between node count and Set
cardinality. In particular, a perfect repeated-key height-three tree has seven
nodes and one distinct key; substituting distinct-key cardinality into the
coefficient-two formula would assert the false inequality `3 ≤ 2`. A positive
cardinality replacement needs its own strict-order/uniqueness bridge.

The [actual measured updates](fdsa-height-updates.md#implemented-measured-local-repairs-and-updates)
now have height-to-cost and logarithmic consequences, including the ordinary
height-only specialization. The [interval query and full sweep](fdsa-measured-rectangle-scan.md#closed-admitted-support-and-logarithmic-height)
separately combine strict complete-key cardinality with finite admitted support.
Full accounting for FDSA-9-39 to FDSA-9-41 and the remaining cost part of FDSA-9-60 still
retains their ordinary-search and exact implementation-correspondence
requirements; these new corollaries do not by themselves qualify those rows.
Construction, balance-factor algorithms, the other book obligations and
receiving integration acceptance remain separate.
