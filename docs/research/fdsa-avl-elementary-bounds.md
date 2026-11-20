# Direct AVL height bounds and global almost-completeness

This increment addresses FDSA Exercise 9.1 and Exercise 9.3, printed page 111
(physical page 117 of the pinned PDF). The exact canonical outcomes are
**C09-042–045 and C09-052–053**, under the unchanged CTB-28 Chapter 9 owner.
The local increment is CTB-117; these identifiers are distinct from GitHub
integration owners. The complete canonical catalog remains
`docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md`.

The universal owner is `Applications/Trees/AVL/ElementaryBounds.lean`, in
namespace `Trees.AVL`. It reuses the existing binary tree, observations, AVL
shape/cache predicates and Chapter 4 global almost-completeness. Connected
clients are in `Examples/AVLElementaryBounds.lean`. Their small Fibonacci trees
are witnesses from the already separate `AVL.Height` owner; they do not supply
the direct universal proof.

## Counting and statement domains

Height is the maximum distance to an external empty leaf. The empty tree has
height zero, one external leaf and zero internal nodes. External leaves are
the size used here. A repeated payload occupies another node occurrence; no
set-cardinality or distinct-label premise is involved. All shape results
quantify over arbitrary `α : Type u`, including an empty payload universe,
without ordering, decidable equality, inhabitance or injectivity assumptions.

Write `h = t.height`, `L = t.numLeaves`, and let division of natural numbers
mean floor division. The three numerical conclusions from `Balanced t` are

\[
2^{\lfloor h/2\rfloor}\le L,\qquad
2^{\lceil h/2\rceil}\le L,\qquad
h\le 2\log_2 L.
\]

The ceiling exponent is represented exactly by `(h + 1) / 2` in natural
arithmetic. The logarithmic conclusion has coefficient two and no additive
constant. In particular, the nil case gives `0 ≤ 0`, so the theorem must not
assume a strictly positive logarithm.

| Canonical row | Formal connection |
| --- | --- |
| C09-042 | `two_pow_half_height_le_numLeaves`; the connected `prescribed_height_bounds` and `prescribed_stored_height_bound` retain the source's explicit height index. |
| C09-043 | `two_pow_ceil_half_height_le_numLeaves`, with a height-indexed direct two-step induction and the stronger odd-height exponent. |
| C09-044 | `height_le_two_mul_logb_numLeaves`, derived from the stronger natural bound and exact logarithm/rounding laws. |
| C09-045 | `floor_power_log_gap` and the connected `arithmetic_floor_gap`: the exact arithmetic separator `n = 3, L = 2`. |
| C09-052 | Reuse `Trees.AlmostComplete`, `Trees.minHeight`, `almostComplete_children` and `minHeight_le_height`; no replacement predicate is introduced. |
| C09-053 | `balanced_of_almostComplete` and `valid_annotate_of_almostComplete`; the global predicate implies local recursive balance for arbitrary payloads. |

## The direct induction and the missing arithmetic inference

The printed exercise asks for the floor estimate by Fibonacci/two-step
computation induction on the height. The proof here uses `Nat.twoStepInduction`
directly with a motive generalized over every balanced tree of height `n`.
It establishes the stronger quantity

\[
S(n)=2^{(n+1)\mathbin{\mathrm{div}}2}
\]

at the same time. It does not import the Fibonacci size theorem or use the
golden-ratio height argument in place of this method.

At height zero, constructor cases force the empty tree and its one external
leaf. At height one, the nonempty node has two children, each with a positive
external-leaf count, giving at least two leaves. For a parent of height `n+2`,
the maximum child height is `n+1`. The two natural AVL inequalities force
**each** child height to be either `n` or `n+1`. The appropriate induction
hypothesis therefore gives at least `S(n)` leaves in each child, including
both orientations and the equal-height case. Leaf counts add, and the exact
division and power identities give

\[
2S(n)=2^{(n+3)\mathbin{\mathrm{div}}2}=S(n+2).
\]

The literal floor estimate then follows by exponent monotonicity. For the
logarithmic consequence, let `k = (h+1) / 2`. Natural arithmetic proves
`h ≤ 2*k`. Cast the stronger power inequality to the reals, establish that
the power and the external-leaf count are positive, and apply base-two
logarithm monotonicity. The power and self-logarithm identities give
`k ≤ log₂ L`; together these inequalities yield the exact conclusion.

The additional strength matters. The arithmetic pair `n=3,L=2` satisfies
`2^(n/2) ≤ L` but fails `n ≤ 2*log₂ L`. This pair is **not claimed to be the
height and leaf count of an AVL tree**. It demonstrates a limitation of an
inference from the floor estimate alone. The stronger estimate supplies the
missing inference while preserving the exercise's final AVL conclusion.

The direct bound is not asserted to be the exact minimum leaf count at each
height. The balanced height-three witness has five leaves, whereas the
ceiling estimate only requires four. Exact minimum-size results retain their
separate existing owner.

## Global almost-completeness and local balance

The reused Chapter 4 definition is

\[
\operatorname{AlmostComplete}(t)
\quad\Longleftrightarrow\quad
\operatorname{height}(t)\le\operatorname{minHeight}(t)+1.
\]

Minimum height measures the distance to the nearest external empty leaf.
This is a global statement about depths and requires no left packing.
Structural induction obtains almost-completeness of both children through
the existing inheritance theorem. If their maximum heights are `hL,hR` and
minimum heights are `mL,mR`, the parent's global premise yields

\[
\max(hL,hR)\le\min(mL,mR)+1.
\]

Combining this with each opposite child's unconditional minimum-height bound
gives `hL ≤ hR+1` and `hR ≤ hL+1`. The recursive induction hypotheses supply
both child balance predicates. These are precisely the four components of
the existing recursive `Balanced` node condition.

There is no converse. The accepted fourth Fibonacci tree is balanced and has
height four, minimum height two and eight leaves, so it is not almost complete.
Its two children are themselves almost complete and their heights differ by
one. Even those child facts plus local AVL balance do not imply the global
parent condition. A separate right-heavy two-node client is almost complete,
showing that no left-packing convention is hidden in the implication.

## Actual height, stored height and correct decoration

`Valid t` combines recursive cache correctness with balance of the erased
shape. The three `_of_valid` numerical theorems concern actual structural
height; they follow by erasure and the existing height/count preservation
laws. The stored-height versions are
`two_pow_ceil_half_ht_le_numLeaves`, `two_pow_half_ht_le_numLeaves`, and
`ht_le_two_mul_logb_numLeaves`. Each retains `Valid t` and uses the existing
`ht_eq_height` law. An arbitrary raw cache cannot replace actual height merely
because its erased shape is balanced or almost complete.

For a concrete singleton storing three, actual height is one and the external
leaf count is two. Its stored floor estimate still holds, while its stored
ceiling estimate fails. Storing four makes both fail. Both raw trees have the
same balanced, almost-complete erased shape. These cases preserve the precise
cache hypothesis rather than treating every malformed cache as the same
counterexample. Correct decoration with `annotate` supplies the valid cached
consequence and preserves erasure; it is a construction, not an assumption
silently added to an arbitrary cached tree.

## Independent cases and their actual connections

The D01–D09 expectations were independently derived before comparison with
the root plan and preserved during checkpoint 066. This task adopts them
without claiming a new independent derivation. Small shape observations may
reduce by computation; positive case conclusions consume the general theorem.

| Case | Connected clients and distinguishing outcome |
| --- | --- |
| D01 | `empty_observations`, `empty_bounds`, `empty_logarithm`: height zero, one external leaf, zero logarithm, both direct powers. |
| D02 | `singleton_observations`, `singleton_bounds`: the floor power is one and ceiling power is two; the bounds consume the universal results. |
| D03 | `heightThree_observations`, `heightThree_bounds`, `heightThree_strict_bound`, `repeated_payload_observation`: height three, five leaves, powers two/four, repeated labels. |
| D04 | `arithmetic_floor_gap`: the exact non-tree pair `n=3,L=2`, with no weakened conclusion. |
| D05 | `chainSix_power_failures`, `chainSix_logarithm_fails`, `chainSix_not_balanced`; `chainFour_not_balanced`, `chainFour_power_bounds`, `chainFour_logarithm_bound`: six nodes refute both bounds, while an unbalanced four-node chain satisfies them. |
| D06 | `fibFour_observations`, `fibFour_not_almostComplete`, `children_and_local_balance_do_not_supply_global_condition`: balanced does not imply global almost-completeness, even with almost-complete children. |
| D07 | `rightHeavy_observations`, `rightHeavy_almostComplete`, `rightHeavy_balanced`, `rightHeavy_children_almostComplete`, `rightHeavy_valid_annotation`, `rightHeavy_bounds`: no left-packing or order assumption. |
| D08 | `bad_cache_observations`, `same_erased_shape`, `badThree_actual_height_bound`, the distinct stored-bound failures and cache-invalidity proofs, `repaired_valid`, `repaired_erasure`, `repaired_bounds`: raw and repaired caches are kept distinct. |
| D09 | `empty_payload_bounds`, the empty-type global/cached consequences, and `empty_payload_no_positive_height`: arbitrary universes without an inhabitance assumption; generic payload/cached/indexed wrappers retain the exact intended premises. |

The chain logarithm cases prove the arithmetic claims separately: `7 < 2^3`
gives `log₂7 < 3`, whereas `2^2 ≤ 5` gives `2 ≤ log₂5`. Unbalance alone is not
used to infer either numerical failure or success. Logarithm power identities
are applied before numerical expansion, with the required positive arguments.

## Validation and qualification boundary

The selected validation inspects the actual universal module's project import
closure separately from the clients, so a client witness import cannot obscure
a forbidden dependency in the direct argument. Source review checks the actual
two-step motive, both induction bases, the child-height alternatives and the
rounding step. Elaborated type inspection covers universes, hypotheses, casts,
private/generated declarations and all case connections; proof audit checks
the actual transitive axiom closure. [CTB-117](../textbooks/CTB.json) records the accepted donor scope and
candidate-specific evidence; CTB-78 owns current receiving validation/review.
Historical receipts are not relabelled as current runs, and neither declaration
counts nor this prose establish acceptance.

This increment concerns six rows only. Later donor owners now supply
[rotations](fdsa-height-rebalance.md), [updates](fdsa-height-updates.md),
[Set refinement](fdsa-height-set-refinement.md) and
[generalized logarithmic height](fdsa-height-bound.md). These separate
qualifications still do not complete Chapter9 or its operation-cost obligations. The remaining Chapter 5 rows, other FDSA chapters and appendices, PFDS
requirements, and the separate receiving integration and whole-library
acceptance remain part of the continuing three-book task.
