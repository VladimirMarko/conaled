# Signed growth and measured resource observations

The adaptation preserves the source’s signed, one-sided growth comparisons and
connects their sign-qualified forms to standard norm asymptotics. Three shared
results in [`Applications/Resources/Growth.lean`](../../Applications/Resources/Growth.lean)
support actual reverse and fold observations; generic source algebra and
boundary clients live in [`Examples/ResourceGrowth.lean`](../../Examples/ResourceGrowth.lean).
The source evidence and the separation from candidate outcomes are recorded below.

## Public surface and source meaning

The adaptation uses native `Filter` expressions, ordinary order, and Mathlib's
`Asymptotics.IsBigO`/`IsTheta`. It adds no copied `Eventually`, `Nonnegative`,
`BigO`, `BigOmega`, `BigTheta`, `NatO`, `NatTheta`, `factor`, or `above` wrapper.
The [source ledger](adwh-resource-growth-provenance.tsv) has exactly **32 rows**:
nine definitions, twenty named theorems and three anonymous cases. The eight
ledger contexts below are separate from that declaration count.

The shared owner remains `Applications/Resources/Growth.lean`, namespace
`Resources`. Its three additions are:

| Name | Public interface |
| --- | --- |
| `isBigO_rat_iff_eventually_le_mul` | Arbitrary domain/filter and rational functions, both eventually nonnegative: norm Big O iff a positive rational eventual upper multiplier. |
| `isBigO_natCast_iff` | Arbitrary domain/filter and natural functions: real-cast norm Big O iff a positive natural eventual upper multiplier. At natural `atTop`, retain the exact positive `C` and `N ≤ n` convention. |
| `successor_square_bounds` | For `n ≥ 1`, `n*n ≤ (n+1)*(n+1) ≤ 4*n*n`. |

`Resources.isBigO_of_nat_bound` remains unchanged, including coefficient zero.
Only the source's native existential representation insists on a positive
coefficient; a zero upper witness can be enlarged where the natural-count
interface requires positivity. There is no additional shared Theta bridge.

The generic clients are in `Examples.ResourceGrowth`. Their `rat_upper_*`,
`rat_lower_*` and `rat_twoSided_*` names describe propositions with explicit
existential coefficients, not new relation definitions. For example, the
source upper comparison is exactly

```text
∃ C : ℚ, 0 < C ∧ ∀ᶠ n in Filter.atTop, f n ≤ C * g n.
```

Reflexivity, transitivity, lower/reversed-upper reciprocal equivalence,
two-sided conjunction/symmetry/transitivity retain arbitrary signed functions.
Positive coefficients multiply; events are intersected. Multiplication by a
context requires only that context to be eventually nonnegative; the remaining
factors stay signed. Global source nonnegativity specializes to the weaker
available eventual premise. Natural-to-rational transfer casts the actual
positive coefficient and keeps its threshold. From a reverse natural upper
coefficient `D > 0`, the rational lower coefficient is `1/(D : ℚ)`.

A norm bound can imply a one-sided bound on a signed left function when the
right function is nonnegative. The stated **equivalence** needs both eventual
sign hypotheses. It must not identify arbitrary signed source comparisons with
norm asymptotics. The retained contrasts at natural `atTop` are `-n` versus
`1` (source upper, no norm Big O), `1` versus `-1` (norm Theta, no positive
source upper), and `-1` versus `-2` (rational multiplier `1/2`, no positive
natural multiplier). Negative filter claims do not extend to the bottom filter.

## Factorization and boundaries

`conditional_factor_eq_div` preserves the source conditional as ordinary
`h n / f n`, including zero denominators. It does not assert that every
existential factor theorem uses that specific witness.

`rat_upper_factorization` weakens the source global nonnegative `f,g,h` premises
to eventual nonnegativity on an arbitrary domain/filter, while retaining
an arbitrary **signed** existential `u`: one-sided upper boundedness of `h`
by `f*g` iff there is such a `u` one-sided upper bounded by `g` and
`h =ᶠ f*u`. The source witness is not required to be norm bounded.
`multiplicative_isBigO_factorization` separately composes Mathlib's zero-aware
bounded-factor machinery for standard norm bounds. Equality is eventual;
neither interface needs an eventual-nonzero premise merely to permit division.

The retained cases include infinitely many zero factors; an obstruction at
index zero to global factorization despite eventual equality; and `f=h=0`,
`g=1`, `u=-n`, where a signed source witness works without a norm bound. These
cases consume the public contracts: `parity_factorization`,
`finite_zero_factorization`, and `zero_product_from_signed_witness`. Their
nonvanishing/global-equality failures are separate declarations. The standard
norm proof may select a different witness. The adopted actual
body assessment confirms that the raw reverse implication consumes its supplied
signed witness without requiring a norm bound on it.

`lt_ceil_natAbs_add_one` retains the exact expression `q.ceil.natAbs+1` for
all rational `q`, including negative values. The additive counterexample keeps
both parts: `2*n*n` has source upper coefficient two against `n*n+1`, while
no positive rational additive constant works eventually against `n*n+C`.
This is not a claim that the usual Big-O addition theorem fails.

The three canonical examples at source lines 221–223 route to the positive
zero/one witnesses and shifted-square results. The destination module has
anonymous connections at `Examples/ResourceGrowth.lean:325`, `:326`, and
`:328`: the last explicitly states both positive natural coefficients and natural
threshold witnesses and obtains them through `nat_upper_iff_isBigO`. Thus the source
`NatTheta` pair is retained alongside the standard real-cast conclusion. Zero not Theta one is asserted
at nontrivial natural `atTop`. Shifted squares use threshold one, fail the
upper bound at zero, attain coefficient four at one, and are not eventually
equal to unshifted squares.

## Actual resource consumers

The clients consume the existing measured algorithms and public value/work
facts; they do not manufacture cost pairs or replace execution owners.

| Client family | Value/observation contract |
| --- | --- |
| `half_reverse_value/work/bounds/theta` | Apply existing `reweight (fun k => (k : ℚ)/2)` to the actual reverse. Preserve its value and obtain observation `n+1/2`, with lower1/upper3/2 for `n ≥ 1`; length 3 gives 7/2 and empty input gives 1/2. |
| `recursive_fold_value/work/bounds/theta` | Actual fixed-price `ListExecution.foldlViaInit` on `List.replicate n a`; preserve the fold value and Theta of `n²`, upper `4*(3+c)`, reverse upper1, threshold1. |
| `direct_fold_value/work/bounds/theta`, `fold_values_agree` | Same combiner, seed and input family; exact direct work `(1+c)*n+1`, unchanged value, and the corresponding linear comparison. |
| `recursive_fold_factorization` | Factor the actual recursive-fold work observation eventually as `n*u(n)` with `u=O(n)`. This is a mathematical observation factor, not an executable instrumentation pass. |
| Existing tree clients | Retain recursive/stack flattening Theta, rank-three counts 27/16, and recursive rank-zero boundary through their existing owners. |

The combining price is fixed outside the varying input index. The model does
not price the internal computation of an arbitrary combiner, construction of
the input family, machine time, allocation, or additional instrumentation.
The positive empty observations explain why the displayed linear upper bounds
cannot be required globally with a right side `C*n`.

All fourteen retained case contracts have the following source routes. Names
in this table have prefix `Examples.ResourceGrowth.` unless an existing owner
file is stated. Their actual contracts and connections are covered by the
adopted bounded
assessment; no extra canonical source rows are created.

| Retained case ID | Exact route or retained owner |
| --- | --- |
| `signed-unbounded-negative` | `signed_negative_upper`, `signed_negative_not_isBigO` |
| `signed-negative-comparator` | `signed_negative_comparator_theta`, `signed_negative_comparator_not_upper` |
| `signed-coefficient-rounding` | `signed_half_coefficient`, `signed_no_positive_nat_coefficient`; `signed_context_case` also consumes the one-half witness. |
| `finite-negative-prefix` | `negative_prefix_eventually_nonnegative`, `negative_prefix_theta`, `negative_prefix_upper_witness` |
| `infinitely-many-zeros` | `parity_factorization`, `parity_factor_not_eventually_nonzero` |
| `finite-zero-obstruction` | `finite_zero_factorization`, `finite_zero_no_global_factorization` |
| `signed-factor-witness` | `signed_factor_witness`, `zero_product_from_signed_witness` |
| `additive-context` | `additive_context_counterexample` |
| `zero-one-source-cases` | `zero_upper_one`, `zero_isBigO_one`, `zero_not_twoSided_one`, `zero_not_isTheta_one`; anonymous source connections at lines325–327. |
| `successor-square-source-case` | `successor_square_theta`, `successor_square_rat_theta`, `successor_square_zero_upper_false`, `successor_square_one_sharp`, `successor_square_ne`, `successor_square_not_eventuallyEq`; native paired witnesses at lines328–334. |
| `actual-recursive-init` | `recursive_fold_value/work/bounds/theta`, `direct_fold_value/work/bounds/theta`, `fold_values_agree`, `fold_nil_costs`, `fold_singleton_costs`, `fold_three_costs` |
| `actual-rational-reverse` | `half_reverse_value/work/bounds/theta`, `half_reverse_nil`, `half_reverse_three`, `half_reverse_no_global_linear_bound` |
| `actual-observation-factor` | `recursive_fold_factorization`, `recursive_fold_not_global_factorization` |
| `existing-tree-clients` | Existing `Applications/Resources/TreeFlattening/Growth.lean` and `Examples/TreeFlatteningCosts.lean`; combined-candidate retention/regression outcomes are recorded separately. |

The module also supplies `old_nat_adapter_zero`, calling the existing adapter
with `C=0,N=0`. Its private `rat_upper_of_isBigO` helper assumes only the
right-hand eventual sign and has no converse. The public rational equivalence
still assumes both signs. All rational signed laws use arbitrary
`ι : Type u` and `l : Filter ι`; the negative examples use natural `atTop`.
The norm factorization is generic over `𝕜 : Type v` with `[NormedField 𝕜]`;
the raw signed factorization is rational. The actual signature/body assessment
preserves these distinct assumptions.
For the natural source interface, the coefficient is positive while the natural
threshold may be zero; the comparison always uses inclusive `N ≤ n`.

## Separate source contexts

These eight IDs retain the original claims and qualifications from the
335 Chapter2 ledger, SHA-256
`a8f205eac08b753c283171d172507b55358af369da09f7173e53df755c626ff1`.
The selected dispositions have the bounded source evidence below. Coordinates are
ledger attributions; no PDF was inspected. The source's claim of an Answer2.1
`Theta(n)` typography slip remains an attributed report, not a new visual
confirmation. The actual constant-order question is retained.

| Context ID | Ledger pointer | Printed / PDF coordinates | Selected obligation and limit |
| --- | --- | --- | --- |
| `2.1-definitions` | `/body_items/0` | 25,26 / 42,43 | Signed rational native-order laws and their sign-qualified norm bridges; rational/natural specialization, not arbitrary-real source semantics. |
| `exercise-2.1` | `/exercises/0` | 38,40 / 55,57 | Zero is bounded above by a positive constant and lacks a positive lower constant. Reported Answer2.1 typography is inherited attribution only. |
| `2.1-zero` | `/exercises/0/subquestions/0` | 38,40 / 55,57 | Both native and standard zero/one boundaries at the nontrivial natural atTop filter. |
| `exercise-2.2` | `/exercises/1` | 38,40 / 55,57 | Multiplicative factorization uses eventual equality; the additive claim has the exact two-part counterexample. |
| `2.2-multiply` | `/exercises/1/subquestions/0` | 38,40 / 55,57 | Retain eventual equality and signed source witness; zero factors do not require eventual nonvanishing. |
| `2.2-add` | `/exercises/1/subquestions/1` | 38,40 / 55,57 | Coefficient2 upper comparison and failure of every positive rational eventual additive slack. |
| `exercise-2.3` | `/exercises/2` | 39,40 / 56,57 | Explicit square constants and source/standard Theta with threshold1; no function equality. |
| `2.3-bounds` | `/exercises/2/subquestions/0` | 39,40 / 56,57 | n²≤(n+1)²≤4*n² for n≥1; upper fails at0 and is attained at1. |

## Evidence, recovery, and limits

The source ledger preserves each retained source ID, kind, line/end-line,
header, definition RHS and lexical-entry hash. Growth’s historical span method
can include adjacent example lines before the next blank; overlapping lexical
spans are not relabeled as separate compiler commands. Native-expression
absorption is intentional and adds no relation wrapper.
