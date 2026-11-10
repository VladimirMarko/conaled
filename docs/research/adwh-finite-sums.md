# Finite sums, actual derivatives, and quantitative rational convergence

The adaptation uses native finite sums and actual polynomial derivatives,
retains the exact rational error and an explicit strict precision bound, and
connects those formulas to existing measured folds and the prepared polynomial
scan. Shared mathematics lives in
[`SquareKit/FiniteSums.lean`](../../SquareKit/FiniteSums.lean);
[`Examples/ResourceFiniteSums.lean`](../../Examples/ResourceFiniteSums.lean) and
[`Examples/GeometricSumScan.lean`](../../Examples/GeometricSumScan.lean) supply
the resource and scan clients. Source evidence and candidate outcomes are
recorded separately as described below.

The [source ledger](adwh-finite-sums-provenance.tsv) has exactly **50 authored
rows**: nine definitions, 34 named theorems, and seven anonymous cases.
FiniteSums contributes 34 and GeometricTail 16. The fifteen source contexts below
are separate; four shared contexts remain partial. Native expressions absorb
the nine definitions without copying a source-specific sum, polynomial,
convergence or asymptotic hierarchy.

## Meanings, indices, and public arithmetic

For exposition, write `T_n = ∑ k ∈ Ico 1 (n+1), k`,
`S_n = ∑ k ∈ Ico 1 (n+1), k*k`, and
`B_n = ∑ k ∈ Ico 1 (n+1), k*2^k`, all natural. Arbitrary positive-index sums
exclude `f 0`; a range conversion needs that zero contribution handled
explicitly. Empty positive intervals at `n=0` belong to every universal
contract. These shorthands are not new Lean definitions.

Shared results live in namespace `SquareKit.FiniteSums`:

| Names | Public contract |
| --- | --- |
| `sum_Ico_one_eq_sum_range`, `list_range_sum_eq_triangle` | The arbitrary AddCommMonoid bridge explicitly requires `f 0=0`; the second connects the actual List.range sum used by the existing fold-cost theorem. |
| `triangle_double/exact/bounds` | `2*T_n=n*(n+1)`, exact natural quotient, `n*n≤2*T_n` and `T_n≤n*n`, including zero. |
| `squares_six/exact/bounds` | `6*S_n=n*(n+1)*(2*n+1)`, exact natural quotient, `n³≤6*S_n` and `S_n≤n³`, including zero. |
| `weighted_two_cast/identity/bounds` | Faithful natural/rational finite-sum cast, `B_n+2^(n+1)=n*2^(n+1)+2`, and `n*2^n≤B_n≤2*(n*2^n)` for every n. |

The source's arbitrary-summand monotonicity uses `Finset.sum_le_sum` on the
selected interval. Its exact arbitrary-f/g specialization is the anonymous
case at `Examples/ResourceFiniteSums.lean:27`; the constant-one distinction
between the positive interval and the zero-inclusive range is at line34.
`n≤n*n` uses existing `Nat.le_mul_self`; no new alias is required for accounting. The exact natural quotients are not rational division.
The twice-weighted identity retains its subtraction-free form at zero.

`Examples.ResourceFiniteSums` supplies the standard real-cast growth instances
through the existing `Resources.isBigO_of_nat_bound`:

| Client | Source upper / reverse upper coefficients | Threshold |
| --- | --- | --- |
| `triangle_isTheta_square` | 1 / 2 | 0 |
| `squares_isTheta_cube` | 1 / 6 | 0 |
| `quadratic_linear_isTheta_square` | 5 / 1 for `2*n*n+3*n` | 0 |
| `weighted_two_isTheta` | 2 / 1 against `n*2^n` | 0 |
| `quadratic_linear_isBigO_cube` | upper5, with `quadratic_linear_cube_bound` | 0 |

`quadratic_linear_bounds` retains the independent all-index bounds. Growth's
new interfaces are not a prerequisite of these SUMS instances. The existing
natural adapter's coefficient-zero interface remains unchanged.

## Actual polynomial derivative

For `R : Type u` with `[CommRing R]`, use the actual standard polynomial

```text
P_n = ∑ k ∈ Finset.range (n+1), Polynomial.X^k : Polynomial R
Q_n = Polynomial.derivative P_n
G_n(x) = ∑ k ∈ Finset.range (n+1), x^k
D_n(x) = ∑ j ∈ Finset.range n, (j+1 : R)*x^j
W_n(x) = ∑ k ∈ Finset.Ico 1 (n+1), (k : R)*x^k.
```

`geom_eval`, `derivative_geom_eval` and `weighted_derivative` connect
`P_n.eval x = G_n(x)`, `Q_n.eval x = D_n(x)`, and
`W_n(x)=x*Q_n.eval x`. The derivative is not merely a named recurrence.
`geom_polynomial_scaled` and `derivative_geom_polynomial_scaled` connect the
actual polynomial and its formal derivative before scalar evaluation.

The scalar `geom_scaled`, `derivative_geom_scaled` and `weighted_geom_scaled`
retain, for all x and n,

```text
(1-x)*G_n(x) = 1-x^(n+1)
(1-x)^2*D_n(x) = 1-(n+1)*x^n+n*x^(n+1)
(1-x)^2*W_n(x) = x*(1-(n+1)*x^n+n*x^(n+1)).
```

Only `geom_closed` and `weighted_geom_closed` require `[Field R]` and `x≠1`.
The scaled identities need no order, characteristic-zero, completeness or
`x≠1` premise. The geometric sum has n+1 terms and the derivative sum n terms; `P_0=1`,
`Q_0=0`; `D_0(0)=0`, `D_(n+1)(0)=1`; `W_n(0)=0`; and the scaled x=1
specializations. Over ℚ, at x=1 the geometric sum is n+1 and cannot equal
the corresponding totalized quotient zero. Any optional real analytic Jets
interpretation requires its separate existing bridge and is not inferred here.

## Exact half sum and strict modulus

Write `H_n = ∑ k ∈ Ico 1 (n+1), (k : ℚ)/(2 : ℚ)^k` and
`R_n=(n+2 : ℚ)/(2 : ℚ)^n` as document shorthands. The shared surface is
`half_sum_eq_weighted_geom/scaled/closed/add_remainder/nonnegative/lt_two/step/mono`,
`half_remainder_pos/antitone`, `square_le_even_power`,
`half_remainder_lt`, `half_sum_ceiling_modulus`, `tendsto_rat_iff_epsilon`
and `half_sum_tendsto`.

The shared results prove the finite identities, positive denominators, termwise
specialization at one half, `H_n+R_n=2`, `0≤H_n<2`, and the positive exact remainder, including
`H_0=0`, `R_0=2`. The elementary source power facts use standard positive-power
and product-power identities rather than another arithmetic wrapper.

`half_remainder_lt` states the strict all-later contract:

```text
∀ ε : ℚ, 0 < ε → ∀ k : ℕ, 2 < ε*(k+1 : ℚ) →
  ∀ n : ℕ, 2*k ≤ n → 0 < R_n ∧ R_n < ε.
```

`half_sum_ceiling_modulus` uses the retained witness
`k=(⌈2/ε⌉ : ℤ).natAbs+1`, followed by `N=2*k`, and returns both
`0<R_n<ε` and the strict two-sided source epsilon comparison.
The witness depends on ε and controls every later index.
`square_le_even_power` supplies the finite bound `(k+1)^2≤2^(2*k)`. At n=6, `R_6=1/8`, so the strict error target fails;
at n=7, `R_7=9/128<1/8`. A non-strict bound or an existence-only limit does
not replace this quantitative result.

The convergence equivalence is universal in `f : ℕ → ℚ` and `a : ℚ`:

```text
Tendsto f atTop (nhds a) ↔
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    a-ε < f n ∧ f n < a+ε.
```

It is not just the H_n-to2 instance. The implementation proves this
arbitrary-sequence equivalence through `tendsto_order` and inclusive
`Filter.eventually_atTop` thresholds. `half_sum_tendsto` then consumes
`half_sum_ceiling_modulus`. The proof uses the explicit-modulus/order-topology route.
It has no `CompleteSpace ℚ` assumption. The adopted actual-body assessment
confirms the arbitrary sequence and limit,
strict quantifier order, exact ceiling witness, and absence of a rational
completeness premise.

## Actual execution and scan clients

For arbitrary element and accumulator universes, `c : ℕ`, combiner f, seed e,
list xs, and n=xs.length, the two **existing** ListExecution programs have the
same value `xs.foldl f e`. `Examples.ResourceFiniteSums.fold_values_agree`
uses both public value contracts. The `foldlViaInit_work_double`
and `foldlViaInit_work_overhead` consume the public work contracts and shared
Gauss bridge to state

```text
2*(ListExecution.foldlViaInit c f e xs).2 = 3*n*(n+1)+2*c*n+2
2*(ListExecution.foldlViaInit c f e xs).2 =
  2*(ListExecution.foldl c f e xs).2+3*n*n+n.
```

Direct work is `(1+c)*n+1`. Universal empty cases retain terminal work 1;
singletons have recursive work c+4 and direct work c+2. The examples
`recursive_fold_empty`, `direct_fold_empty`, `recursive_fold_singleton`,
`direct_fold_singleton`, `recursive_fold_add_two` and `direct_fold_add_two`
keep those boundaries. With c=1, addition, seed0 and `[1,2]`, both values are 3
and work is 12 versus 5. These are full finite-spine structural observations;
combiner internals and input construction are unpriced, no physical reverse
is free, and no machine-time/allocation result is claimed.

`Examples.GeometricSumScan.shaped_derivative_evaluation` consumes the existing
`Examples.JetScan.shaped_evaluation_correct` on the actual Q_n, with
`Q_n.natDegree < plan.shape.size` and the existing coefficient adapter. The
existing JetScan interface has `R : Type`; its rational specialization fits
universe zero. Generic shared algebra over `Type u` does not broaden that
client interface. `shaped_weighted_evaluation` then uses the public weighted
identity. Preparation must supply enough slots: `natDegree 0=0`, so even Q_0
requires a nonempty adequate plan. Use existing `prepare`/`prepare_correct`
or a proof of the strict shape premise.

`geometric_three_derivative_at_two` retains 17 at n=3,x=2 through the
actual prepared scan. `geometric_three_weighted_at_two` consumes
`weighted_geom_closed` to obtain the canonical source value 34.
The separate `geometric_three_scan_weighted_at_two` states both the actual
weighted scan/sum equality and its value 34 through the derivative value17.
`geometric_zero_derivative` retains zero at n=0 for every rational input.
No independent polynomial evaluator is introduced.

The seven canonical source cases have the following exact destinations.
Their actual contracts and required public-theorem connections have the
bounded checked evidence below.

| Canonical source case | Concrete destination | Public mathematical connection |
| --- | --- | --- |
| `FiniteSums.example@204` | `Examples.ResourceFiniteSums.triangle_five` | `triangle_exact 5`, then natural arithmetic: T5=15. |
| `FiniteSums.example@205` | `Examples.ResourceFiniteSums.squares_five` | `squares_exact 5`, then natural arithmetic: S5=55. |
| `FiniteSums.example@206` | `Examples.GeometricSumScan.geometric_three_weighted_at_two` | `weighted_geom_closed (2:ℚ) 3`; the separate `geometric_three_scan_weighted_at_two` retains the actual scan connection. |
| `FiniteSums.example@207` | `Examples.GeometricSumScan.geometric_three_derivative_at_two` | Actual `evaluatePolynomial` on the prepared derivative, `derivative_geom_eval`: D3(2)=17. |
| `GeometricTail.example@125` | `Examples.ResourceFiniteSums.half_sum_one` | `half_sum_closed 1`: H1=1/2. |
| `GeometricTail.example@126` | `Examples.ResourceFiniteSums.half_sum_two` | `half_sum_closed 2`: H2=1. |
| `GeometricTail.example@127` | `Examples.ResourceFiniteSums.half_sum_three` | `half_sum_closed 3`: H3=11/8. |

Supplemental mathematical boundaries in `Examples.ResourceFiniteSums` are
`half_sum_zero`, `half_remainder_zero`, `half_remainder_six`,
`half_remainder_six_not_strict`, `half_remainder_seven` and
`half_remainder_seven_strict`. They state H0=0, R0=2, R6=1/8 and its failed
strict target, and R7=9/128<1/8. They carry no resource-cost attribution.
The four literal half-sum intervals have natural endpoints; their summands
and results are rational, as confirmed by the actual explicit signatures.

The actual preparation interface is also exposed through
`prepared_derivative_adequate`, `prepared_derivative_evaluation` and
`prepared_weighted_evaluation`. `geometric_zero_prepared_size` states the
one-slot zero-derivative boundary; `geometric_zero_empty_shape_inadequate`
excludes the empty shape; `geometric_successor_derivative_at_zero` retains
D_(n+1)(0)=1; `geometric_derivative_at_one` gives the triangle at x=1 through
the prepared evaluator. The required scalar endpoints are also explicit in
the scan owner. These scalar endpoint statements are rational
specializations of the shared commutative-ring identities:

| Boundary | Source meaning and universal connection |
| --- | --- |
| `geometric_zero_endpoints` | P0=1, its actual derivative=0, G0(x)=1, D0(x)=W0(x)=0; consumes `geom_eval`, `derivative_geom_eval`, and `weighted_derivative`. |
| `geometric_at_zero` | G_n(0)=1, W_n(0)=0 through `geom_eval` and `weighted_derivative`. |
| `geometric_at_one` | G_n(1)=n+1 and D_n(1)=W_n(1)=(T_n:ℚ); consumes actual derivative/weighted identities and faithful natural sum casting. |
| `geometric_at_one_quotient_obstruction` | The totalized quotient is zero at x=1, while G_n(1) differs for every n. |
| Three anonymous x=1 cases | Explicit uses of `geom_scaled`, `derivative_geom_scaled`, `weighted_geom_scaled` at the excluded quotient point. |

The root assessment inspected every actual scan public body and retained these
required supplemental connections. They do not create extra canonical source
rows or establish chapter closure.

## Separate source contexts

The following fifteen records retain exact IDs and pointers from the same
335 Chapter2 ledger, SHA-256
`a8f205eac08b753c283171d172507b55358af369da09f7173e53df755c626ff1`.
There are eleven SUMS-exclusive records and four shared records. The selected
obligations have the bounded source evidence below. “Exclusive” identifies the
bounded source mapping; final exercise/context dispositions are recorded
separately.

| Context ID | Ledger pointer | Printed / PDF coordinates | Scope | Selected obligation and limit |
| --- | --- | --- | --- | --- |
| `2.1-growth-examples` | `/body_items/1` | 25,26 / 42,43 | shared; partial | Triangle, square and quadratic-polynomial instances only. Cubic floor-log and harmonic/logarithmic interpretations remain outside SUMS. |
| `2.2-cost-model` | `/body_items/5` | 27,28 / 44,45 | shared; partial | Exact actual recursive/direct fold observations and fixed combining charge. General cost groups and demand semantics remain separate. |
| `2.2-series` | `/body_items/11` | 29,32 / 46,49 | shared; partial | Finite half-geometric sum, exact remainder and rational limit. Factorial-prefix and reciprocal-factorial series remain outside this slice. |
| `exercise-2.4` | `/exercises/3` | 39,40 / 56,57 | SUMS-exclusive scope | Both positive-index sum formulas and bounds; final exercise disposition is recorded separately. |
| `2.4-linear-sum` | `/exercises/3/subquestions/0` | 39,40 / 56,57 | SUMS-exclusive scope | Gauss double/exact natural quotient/bounds and connected actual fold cost. |
| `2.4-square-sum` | `/exercises/3/subquestions/1` | 39,40 / 56,57 | SUMS-exclusive scope | Scaled square identity, exact natural quotient, bounds and standard growth. |
| `exercise-2.5` | `/exercises/4` | 39,40,41 / 56,57,58 | shared; partial | Only quadratic and cubic-upper subitems. Log/root, harmonic, factorial and exact-expression claims remain outside SUMS. |
| `2.5-quadratic` | `/exercises/4/subquestions/0` | 39,40,41 / 56,57,58 | SUMS-exclusive scope | All-index natural polynomial bounds; real-cast Theta, coefficients5 and1 at threshold0. |
| `2.5-cubic-upper` | `/exercises/4/subquestions/1` | 39,40,41 / 56,57,58 | SUMS-exclusive scope | All-index natural cubic upper coefficient5, then real-cast Big O. |
| `exercise-2.6` | `/exercises/5` | 39,41 / 56,58 | SUMS-exclusive scope | Five finite/limit portions; actual formal polynomial derivative, x≠1 on quotient formulas, every rational ε. No optional real analytic interpretation inferred. |
| `2.6-geometric` | `/exercises/5/subquestions/0` | 39,41 / 56,58 | SUMS-exclusive scope | n+1-term sum and ring identity; field quotient requires x≠1. |
| `2.6-derivative` | `/exercises/5/subquestions/1` | 39,41 / 56,58 | SUMS-exclusive scope | Actual derivative of P_n and n-term shifted evaluation; rational JetScan client. |
| `2.6-twice` | `/exercises/5/subquestions/2` | 39,41 / 56,58 | SUMS-exclusive scope | Native weighted-two cast, subtraction-free identity, all-index bounds and growth. |
| `2.6-half` | `/exercises/5/subquestions/3` | 39,41 / 56,58 | SUMS-exclusive scope | Exact finite half sum, positivity, monotonicity and positive remainder. |
| `2.6-limit` | `/exercises/5/subquestions/4` | 39,41 / 56,58 | SUMS-exclusive scope | Generic rational convergence equivalence, strict all-later modulus, and Tendsto H_n to2. |

Printed/PDF coordinates are ledger attributions only. The original report's
visual-confirmation and completion language remains attributed in the retained
inputs; this work has not inspected a PDF and does not inherit those claims.
In particular the four shared contexts are not closed by SUMS. Unselected
logarithmic, harmonic, factorial and recurrence obligations remain separate.

## Source identities and evidence boundary

The exact primary members are:

| Member | Bytes | SHA-256 |
| --- | ---: | --- |
| `ADWH/Chapter02/FiniteSums.lean` | 6,824 | `c9ffbc5a5eecb2165044317867c33075442c293439619cbf1fc6ecb184ce191b` |
| `ADWH/Chapter02/GeometricTail.lean` | 4,967 | `3553e2746b53b0920a600a2c22cfb3d7a31dcae432bda47451b32a93a881d041` |

## Standard theorem reuse

`two_pow_pos` routes to standard `pow_pos` in
`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:584`, specialized to positive
rational two in `half_remainder_pos` and the denominator proofs.
`half_power_identity` routes to `mul_pow` in
`Mathlib/Algebra/Group/Basic.lean:228` and the local `hpow` inside
`half_sum_scaled`: rewrite backwards and normalize `(1/2:ℚ)*2=1`.
`self_le_square` routes to `Nat.le_mul_self` in
`Init/Data/Nat/Lemmas.lean:757`, actually cited by `triangle_bounds` and
`quadratic_linear_bounds`. `sumUp_mono` uses the generated additive theorem
`Finset.sum_le_sum`; its source owner is the `to_additive` attribute and
`prod_le_prod` at `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:117–118`.
These standard theorems are used directly; no aliases were added solely for
source accounting.

The shared file has 36 public theorems. ResourceFiniteSums has 27 named
theorems and two anonymous native-expression instances; its S3 proofs call
only the unchanged natural adapter. GeometricSumScan has 17 named theorems
and three anonymous uses of the scaled identities at x=1.
