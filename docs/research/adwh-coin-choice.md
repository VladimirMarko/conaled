# Aligned coin choice reconstruction (#163)

The reconstruction gives two objectives over the same independently defined
feasible tuples: lexical greatestness and fewest coins. The quotient/residual
executor satisfies the lexical objective directly. It does not call an
enumerator or selector, and it is not generally a minimum-coin algorithm.
For denominations `[4,3,1]` and amount 6, its tuple `[1,0,2]` uses three coins;
the independently optimal `[0,2,0]` uses two.

`Applications.CoinChoice.Basic` retains one positional representation relation
and one proof of enumeration completeness and greedy maximality. `Currency`
requires positive denomination positions ending in 1. It admits repeated
positions such as `[2,2,1]` and nonmonotone positions such as `[1,5,1]`.
`Represents` aligns one count with each denomination. The source `amount`
uses zipped multiplication and truncates mismatched lists, so its equation
alone does not imply feasibility. `represents_iff_amount` keeps the length
equation explicit.

The ascending nested-bind enumerator and its map-based alternative retain
the source traversal order, singleton-unit priority and every occurrence.
Their exact equality holds on totalized inputs. Completeness is proved
against `Represents` on `Currency`, without a decreasingness assumption.
Greedy feasibility and its bound against every independently feasible tuple
use quotient/residual arithmetic. Standard List lexical order replaces the
source's local equality-or-Lex relation; `lexLE_iff` proves that bridge.

`Presentation` contains the second source's recursive weighted sum and
explicitly aligned `IsTuple`. It proves their equivalence with `amount` and
`Represents`, rather than duplicating the algorithm proofs. The exact
`ValidDenominations` predicate is equivalent to strict pairwise decreasingness
plus `Currency`. Its feasibility and completeness clients specialize the
broad-domain results through these bridges. Equations for both ascending
executors and greedy show that reversing the source's singleton-test
conjunction leaves their recurrences unchanged. Both source objective
presentations have explicit equivalence theorems.

## Shared optimization and ties

`Selection.feasible` supplies the common independent candidate set.
`minCoins_iff_minimizer` uses the existing `Optimization.minimizers` with the
sum of counts. `lexical_iff_minimizer` uses the same interface with the order
dual of a tuple's standard lexical order. `enumeration_minimizer` discharges
the coverage obligation of `Optimization.minimizer_transport` from enumeration
completeness. Both selector consumers use this theorem and the accepted
`Optimization.Thinning.argmin_correct` result.

`lexicalChoice` selects the greatest tuple through `argmin` and `OrderDual`.
It equals the direct greedy result by independent lexical uniqueness.
`mkchange` selects the first minimum coin count in ascending traversal.
`mkchangeStrict` selects the last minimum using the same selector after
reversal. The shared `argminLast_cons` theorem proves exactly the source's
strict right-fold recurrence. No second generic selector is implemented.

The shared selector work was isolated in commit
`7a379cffdb9600babb53f9a89d564898050afe8b`:

- `Optimization.FirstMinimum` and `LastMinimum` describe before/after score
  bounds independently of a selector.
- `argmin_firstMinimum`, its converse and its equivalence characterize the
  existing first-tie selector.
- `lastMinimum_iff_first_reverse`, `argminLast_eq_some_iff` and
  `argminLast_correct` connect last ties to reversal and original-input
  minimality.
- `Bracketing.FirstMinimum` remains a compatible abbreviation. Its public
  argmin certificate forwards to the shared theorem; existing Bracketing
  examples still pass.

These predicates work for arbitrary score types; selector theorems use the
existing Mathlib `LinearOrder` interface. This is a change from the source's
separate Std order-law parameters, not a claim that unlawful or unrelated
`LE` and `LT` operations are supported. The concrete coin objective uses Nat.
The shared first-tie interface also supports OrderDual Int, checked separately
in `Examples.SelectionTies` and consumed by the segment reconstruction.

`Descending` retains an actual recursive `downFrom` and a recursive descending
nested comprehension. It does not define the generator by reversing a
finished ascending enumeration. `mktuples3_eq_reverse` proves exact ordered
reversal, including inner traversals. Consequently the first minimum in that
descending enumeration equals the strict last minimum in ascending order as
a selected tuple. In contrast, first and last ascending minima need only
have equal coin counts; distinct selected tuples are demonstrated at amount 54.

## Provenance and remaining scope

The immutable source is
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md).
Extracted members were checked against the preserved SHA-256 manifest:

| Archive member | SHA-256 |
|---|---|
| `project/adwh-lean/ADWH/Chapter07/CoinChange.lean` | `16668810c4c26f1c9e57885d25ac9df7cc37bfac6b3689aba8ce0cb0f6245728` |
| `project/adwh-lean/ADWH/Chapter07/CoinChangeDecreasing.lean` | `88c9b7d1a3732153cd12bc6f3332a69ae201411d4582cb26f303019972cefecb` |
| `project/adwh-lean/ADWH/Chapter07/CoinChangeMinima.lean` | `c92d100ee9097768e18c54ef82cf7ba4c09521aadb43c0776a48ff0f3535f365` |

The [declaration ledger](adwh-coin-choice-provenance.tsv) covers all 140
explicitly named definitions, inductives, abbreviations and theorems in these
members. The source private `represents_amount` is identified by its lexical
source name and is public locally. Generated names, unnamed instances and
anonymous examples are not separate rows. Each row gives the source member,
hash, qualified lexical name, destination and precise disposition. Shared
selector proofs and reused standard interfaces are distinguished from
coin-specific reconstructions.

Twenty-one rows remain deferred. These are second-presentation helper wrappers
and the literal `maximumPair`/`maximumTuple` fold-left implementation and its
`mkchange2` wrappers. The new `lexicalChoice` is an alternative objective
consumer with proved agreement to greedy; it is not advertised as a literal
port of that fold-left implementation. Names covered by a stronger shared
result or a semantic bridge are marked composed or bridged, not independently
ported copies.

Currency exchange and canonicality arguments, residual-representation
variants, all-minima selectors and execution resource bounds remain separate
work. Empty currencies, zero denominations and missing terminal units have
explicit executable extensions, but no source-domain feasibility or lexical
optimality theorem is claimed for them. Nat models the intended nonnegative
source amounts and counts.

`count` is the number of coins. `mkchange3_length` is the number of tuple
positions. `mktuples3_length` compares enumeration cardinalities. None measures
execution steps, time, allocation or memory, and no performance claim follows
from exact semantic agreement.

## Checked development and statement review

The initial case separated the two objectives at `[4,3,1]`, amount 6. The
expected feasible tuples and coin counts were computed independently before
connecting them to the universal optimality theorems. Existing shared argmin
correctness lacked the complete positional first/last contracts; those became
the shared selector obligations. They were checked against text-length ties,
a strict tie step and an OrderDual Int maximum before the coin clients.

A subsequent nonmonotone case retained `[1,1,0]` as a minimum for `[1,5,1]`,
amount 6. Attempting to connect it to the first selector failed because that
selector returns `[0,1,1]`, another two-coin solution. The expected minimum
was unchanged; the corrected connection uses the strict-last theorem. This
exercises the difference between minimum score and tie-selected witness.

`Examples.CoinChoice` retains these public-result connections:

| Case | Checked observation |
|---|---|
| `zero_amount`, `unit_currency` | Arbitrary valid currency at 0 and arbitrary amount for `[1]`; both independent objectives follow through greedy and minimum-selector contracts. |
| `ascending_order`, `descending_order` | Exact ascending-map alternative and actual descending recursion are connected through their equivalence/reversal theorems. |
| `enumeration_complete` | All candidate lists are characterized by aligned length 3 and weighted amount 6 for `[4,3,1]`. |
| `repeated_positions`, `nonmonotone_positions` | The broad domain remains usable; lexical and minimum objectives can choose distinct positions or different coin counts. |
| `ordinary_change`, `different_objectives` | `[5,2,1]` at 11 has a checked common optimum; `[4,3,1]` at 6 refutes greedy minimum-count optimality. No universal currency canonicality claim is inferred. |
| `lexical_reference` | Standard argmin over OrderDual agrees exactly with direct greedy through independent lexical uniqueness. |
| `distinct_minimizers`, `tie_positions`, `descending_tie` | At 54, first ascending chooses `[6,4,0]`, last ascending and first descending choose `[7,1,2]`. Both are independently minimum-coin tuples with equal counts and different selected tuples. |
| `only_greatest_tie_is_lexical` | Of those tied minima, only `[7,1,2]` is lexically greatest; uniqueness rules out the other. |
| `decreasing_bridge`, `alignment_matters` | The stronger source domain enters through its explicit bridge; a truncated zipped amount does not satisfy aligned feasibility. |
| `outside_domain`, `empty_selections` | Checked total evaluations are explicitly outside the positive-unit correspondence domain. |

Statement review covered each new or changed formal claim:

- Domain and representation constructors, their length/value/unit lemmas and
  domain equivalences quantify over finite positional Nat lists. Positivity
  and a final unit are sufficient for the broad results; decreasingness is
  imposed only by the second source domain. Alignment is never inferred from
  the truncated amount function alone.
- Enumeration equations, alternative equality, membership equivalences,
  nonemptiness and zero cases retain all candidate occurrences and exact
  traversal order. Leading-count bounds require a positive denomination;
  residual decomposition uses Nat arithmetic under that bound.
- Greedy equations and length are total. Feasibility, global lexical bound,
  maximality, membership and uniqueness are restricted to `Currency` where
  required. The bound quantifies over every independently represented tuple,
  not only outputs of a particular enumerator. Standard lexical antisymmetry
  justifies tuple uniqueness.
- Presentation and objective bridges are equivalences. The recursive
  weighted-sum extension agrees with zipped amount even on unequal lengths;
  `IsTuple` separately keeps alignment. The recurrence bridges change only
  conjunction order in the singleton-unit test.
- Optimizer transport uses identity realization, unchanged costs, feasibility
  of every enumerated tuple and an enumerated lift for every independent
  feasible tuple. Minimum and lexical selection instantiate this same
  theorem with different ordered costs.
- First/last certificates quantify over a split at a selected occurrence.
  Strictness is before the first and after the last. Reversal swaps those
  positions, and the strict recurrence handles empty tails and equal costs.
  The Bracketing abbreviation preserves its Nat contract definitionally.
- Minimum-selector specifications preserve the selected tuple and prove
  feasibility and global minimum coin count. Existence follows from valid
  enumeration nonemptiness. Score uniqueness does not assert tuple uniqueness.
  Descending reversal, permutation and cardinality hold on totalized inputs;
  its feasibility and minimum claims retain the source-domain condition.

Targeted `lake build` checks pass for `Examples.CoinChoice`,
`Examples.SelectionTies`, and the existing `Examples.Bracketing` regression.
All are imported through `SquareApplications.lean`. The coordinating session
owns the fresh full build, exhaustive axiom audit and independent Standards,
Spec and supervising intent reviews.
