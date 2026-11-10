# Finite affine recurrences, scanner values, and measured work

The RA, RB, and RC adaptations use native positive-index folds, finite sums,
factorials, and uniform two-parameter growth.
Shared mathematics lives in
[`SquareKit/FiniteRecurrences.lean`](../../SquareKit/FiniteRecurrences.lean),
growth consequences in
[`Applications/Resources/Recurrences.lean`](../../Applications/Resources/Recurrences.lean),
and connections in
[`Examples/ResourceRecurrences.lean`](../../Examples/ResourceRecurrences.lean)
and [`Examples/RecurrenceScans.lean`](../../Examples/RecurrenceScans.lean).
Shared mathematics imports neither client layer. Existing FiniteSums imports
include topology/filter dependencies; this adaptation adds no growth statements
to SquareKit.

The [source ledger](adwh-recurrences-provenance.tsv) accounts for exactly
**61 source commands**: the retained **33 RA commands** (five definitions,
23 theorems, five cases), **12 RB commands** (ten theorems, two cases), and
**16 RC commands** (four definitions, nine theorems, three cases).
Its ten separately qualified context rows bring the ledger to 71 rows.
Within RA, seventeen source theorem rows have shared finite
dispositions, one reuses `Nat.factorial_pos`, four belong to Applications, and
one retains Theta together with function inequality in Examples. Several source
rows share a generic declaration; source-row counts are not declaration counts.

## Native meanings and definition dispositions

For exposition only, write

```lean
F weight toll b n =
  (List.range' 1 n).foldl (fun x k => weight k * x + toll k) b
```

There is no new `F` or source recurrence definition. The functions `weight` and
`toll`, and the independent base `b`, are natural-valued. The empty fold returns
`b`; successor executes index `n+1`. Index-zero values are unused. A zero
positive-index weight resets the accumulator to that index's toll.

| Source definition | Native disposition |
| --- | --- |
| `GeneralRecurrences.run` | The displayed arbitrary affine fold, with `affine_fold_zero/succ`. |
| `Recurrences.addRec` | Weight 1, toll `c*k`; exposition shorthand `A(b,c,n)`. |
| `Recurrences.doubleRec` | Weight 2, toll `c*k`; shorthand `D(b,c,n)`. |
| `Recurrences.factorialRec` | Weight `id`, toll `c*k`; shorthand `P(b,c,n)`. |
| `RecurrenceDerivations.reciprocalFactorials` | `R(n) = ∑ k ∈ Finset.range n, 1 / (Nat.factorial k : ℚ)`. |

The client has universal zero/successor specializations for A, D, and P.
For R it uses the native empty sum and `Finset.sum_range_succ`: the next term
is `1/n!`, so both `0!` and `1!` occur. The source factorial-positivity theorem
uses `Nat.factorial_pos` directly, with an arbitrary-n example and no wrapper.

## RA: fifteen shared theorems

Write `Q(n)=∑ k ∈ Finset.Ico 1 (n+1), k` and
`H(n)=∑ k ∈ Finset.Ico 1 (n+1), (k:ℚ)/(2:ℚ)^k`, again only as document
shorthands. Existing `FiniteSums.triangle_bounds` and `half_sum_scaled` supply
the corresponding arithmetic.

| Public names | Contracts and domains |
| --- | --- |
| `affine_fold_zero`, `affine_fold_succ` | Empty base and chronological successor for arbitrary natural weights/tolls. |
| `le_affine_fold`, `affine_fold_le` | Both arbitrary-sequence comparison directions from base and successor inequalities. |
| `additive_exact`, `additive_bounds` | `A=b+c*Q(n)` for all b,c,n; `n²≤2*A` and `A≤(b+c)*n²` for c>0,n≥1. |
| `doubling_exact`, `doubling_upper`, `doubling_lower` | `D+c*(n+2)=2^n*(b+2*c)` and `D≤(b+2*c)*2^n` universally; `c*2^n≤2*D` for n≥1. |
| `factorial_reserve`, `factorial_lower` | `P+2*c≤(b+3*c)*n!` and `c*n!≤P`, with the recorded n≥1 domain. |
| `doubling_normalized_sum`, `factorial_normalized_sum` | `(D:ℚ)=2^n*((b:ℚ)+(c:ℚ)*H(n))` and `(P:ℚ)=(n!:ℚ)*((b:ℚ)+(c:ℚ)*R(n))`, all b,c,n. |
| `reciprocal_factorial_sum_nonneg`, `reciprocal_factorial_sum_lt_three` | `0≤R(n)<3` for every n, including the empty sum. |

Normalization explicitly casts the **natural** fold before entering ℚ.
The proofs retain independent b,c and never cancel c. The factorial denominator
is positive; the reciprocal bound is finite and needs no infinite-series limit.
The factorial reserve also holds at zero, although its retained public theorem
uses n≥1. The additive quadratic upper bound and the doubling/factorial lower
bounds have explicit counterinstances at zero.

## Six universal comparisons

For arbitrary `T : Nat → Nat`, `le_affine_fold` assumes `T 0≤b` and
`T(n+1)≤weight(n+1)*T n+toll(n+1)`, concluding `∀ n, T n≤F weight toll b n`.
`affine_fold_le` reverses both premises and the conclusion. Neither requires
positive tolls or weights.

The six source comparison rows are the two directions specialized to A, D,
and P. `Examples/ResourceRecurrences.lean` contains six exact universal examples:
weights 1, 2, and `id`, toll `c*k`, arbitrary T,b,c, and the original base/step
premises. They call the generic pair rather than substituting a second fold
for T. These examples preserve source coverage without six additional aliases.

## RA growth and coefficient conversion

The three RA recurrence growth declarations use standard real-cast
`Asymptotics.IsTheta Filter.atTop`. Each assumes c>0 and permits b=0.
The underlying natural inequalities retain these coefficients and inclusive
thresholds:

| Family | Upper coefficient / threshold | Reverse coefficient / threshold |
| --- | --- | --- |
| A against n² | b+c / 1 | 2 / 1 |
| D against 2^n | b+2*c / 0 | 2 / 1 |
| P against n! | b+3*c / 1 | 1 / 1 |

`nat_bound_iff_rat_bound` preserves the full existential equivalence for
natural-valued f,g:

```lean
(∃ C N : Nat, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n) ↔
  (∃ C : ℚ, 0 < C ∧ ∃ N : Nat,
    ∀ n, N ≤ n → (f n : ℚ) ≤ C * (g n : ℚ))
```

The comparator may vanish. The proof uses the accepted Growth bridges;
it adds no signed-rational generalization. Clients retain the rational
coefficient 1/2 versus natural coefficient 1 and a zero comparator.
`theta_is_not_function_equality` separates n² and n²+n at n=1 despite their
Theta comparison, with coefficients 1 and 2 at threshold zero.

The theorem `zero_toll_additive_not_isTheta` is a symbolic negative result:
`A(3,0,n)=3` cannot be Theta(n²). Any reverse eventual coefficient C and
threshold N are contradicted at `n=N+3*C+1`. This checks the need for a positive
toll assumption beyond a single finite sample.

## RA scanner and source cases

The generic scanner interface quantifies over `α : Type u`, arbitrary base b,
shape, and actual `Scanner.inclusive`. Transitions inhabit
`MulOpposite (Function.End α)`, where multiplication observes f followed by g.
`inclusive_fusion` and `ListFusion.scanl_prefix_values` connect actual scanner
outputs to native folds. The premise equates **ordered flattening** with the
transition list; equal lengths would not establish the result.

The affine specialization returns every prefix, including the initial state:

```lean
(List.range (n+1)).map (fun j =>
  (List.range' 1 j).foldl (fun x k => weight k*x+toll k) b)
```

The five-entry recipe composes four leaves and a fifth leaf using existing
composition/product plans. Empty, pair, and leaf plans supply boundary checks.
The five retained source cases connect as follows:

| Case | Public connection and required observation |
| --- | --- |
| A(3,2,5)=33 | `additive_exact`; actual prefixes `[3,5,9,15,23,33]`. |
| D(3,2,5)=210 | `doubling_normalized_sum`, H(5)=57/32; `[3,8,20,46,100,210]`. |
| P(3,2,5)=1010 | `factorial_normalized_sum`, R(5)=65/24; `[3,5,14,48,200,1010]`. |
| R(4)=8/3 | Native rational sum together with both public reciprocal bounds. |
| D(3,2,0)=3 | `affine_fold_zero` and actual empty observation `[3]`. |

Additional discriminators retain chronological `[3,8,20]` versus reversed
`[3,10,22]`, a zero-weight reset `[123,7]`, ignored index-zero data, c=0 values
3/96/360, arbitrary weights with b=c=0, and normalized empty base 3 rather
than the erroneous product 6. These are value claims, not measured work/span
or machine-runtime results.

## RB: arbitrary eventual tolls

RB keeps the same positive-index native fold and independent base. It adds four
finite theorems in SquareKit and four growth theorems in Applications. The two
source sum obligations reuse `Finset.sum_le_sum_of_subset` and
`Finset.single_le_sum_of_canonicallyOrdered` directly. Their checked anonymous
Nat specializations retain arbitrary summands, `n≤m`, and `1≤k≤n` respectively;
no additional project sum wrapper or guessed anonymous declaration name is used.

| New finite theorem | Contract |
| --- | --- |
| `additive_toll_exact` | `F(1,toll,b,n)=b+sumUp(toll,n)` for every natural toll, b, and n, including zero. |
| `triangle_le_scaled_toll_sum` | From `∀ k≥N, k≤D*toll(k)`, derive `Q(n)≤D*sumUp(toll,n)+Q(N)` for every n. D need not be positive, and n need not be at least N. |
| `doubling_base_lower` | `b*2^n≤F(2,toll,b,n)` for all natural tolls, b, and n. |
| `factorial_base_lower` | `b*n!≤F(id,toll,b,n)` for all natural tolls, b, and n. |

Here `sumUp(toll,n)` is only a document shorthand for the native sum over
`Finset.Ico 1 (n+1)`. Index zero is excluded. All finite arithmetic remains in
Nat; growth statements cast those natural quantities to the reals.

`Resources.positive_linear_bound_of_isBigO` turns an eventual O(id) toll into
one positive natural coefficient C satisfying `toll(n+1)≤C*(n+1)` for every n.
The coefficient precedes the entire positive-index quantifier. The theorem
requires neither monotonicity nor a bound on toll(0). Its proof uses the pinned
`Asymptotics.bound_of_isBigO_nat_atTop` interface, then chooses a larger natural
coefficient. A private comparison lemma reuses `affine_fold_le` to compare the
arbitrary toll with the accepted linear-toll fold at the same base.

| New growth theorem | Hypotheses and result | Upper coefficient / threshold | Reverse coefficient / threshold |
| --- | --- | --- | --- |
| `additive_toll_recurrence_isTheta` | Any fixed b, toll Θ(id); fold Θ(n²) | b+C / 1 | 4D / 2N |
| `doubling_toll_recurrence_isTheta` | Fixed b>0, toll O(id); fold Θ(2^n) | b+2C / 0 | 1 / 0 |
| `factorial_toll_recurrence_isTheta` | Fixed b>0, toll O(id); fold Θ(n!) | b+3C / 1 | 1 / 0 |

C is a global positive upper toll coefficient. For the additive reverse bound,
D and N are fixed lower-tail witnesses before the growth index. The proof keeps
the reserve Q(N) until it can be absorbed at n≥2N. The positive-base exponential
and factorial results allow zero toll. The earlier RA positive-linear-toll
results continue to allow base zero under their own hypotheses.

### Discriminating cases

`finite_prefix_toll_contract` uses toll(0)=999, toll(1)=100, and toll(k)=k for
k≥2. With base zero its prefix values are `[0,100,102,105,109]`. It retains a
positive-index coefficient of 100, proves that no coefficient bounds toll(0)
by a multiple of zero, and gives the exact formula Q(n)+99 for n≥1. The same
case checks the finite reserve with D=1,N=2, invokes the arbitrary-toll Theta
theorem, and retains upper (100,1) and reverse (4,4) witnesses.

`positive_sum_zero_index_boundary` gives every positive-prefix sum as zero for
a function supported only at index zero. Its value 999 at zero cannot be bounded
by any of those sums, so the term-in-sum premise `1≤k` matters.

`zero_toll_base_boundary` proves the all-n identities 2^n and n! at base one,
and zero at base zero. It applies both new positive-base Theta theorems and
proves the two base-zero Theta conclusions false for arbitrary eventual
coefficients and thresholds. The supplied C=1 upper witnesses remain 3 at
threshold zero and 4 at threshold one; both reverse witnesses are 1 at zero.

`pointwise_bounds_do_not_control_sum` contrasts `∀ k≥1, ∃ Ck>0, k²≤Ck*k`
with the false cumulative claim `sumUp(k↦k²,n)=O(n²)`. Given any proposed
coefficient C and threshold N, the proof uses n=N+6C+1 and the accepted cubic
lower bound for the square sum. The result is a universal counterfamily.

The two new source cases use the existing composed pair scanner with ordered
indices `((1,2),(3,4))`, base one, and opposite endomorphisms:

| Source case | Native fold and complete decoded inclusive prefix list |
| --- | --- |
| `GeneralRecurrences.example@203` | Weight 2, toll id, n=4 gives 42; `[1,3,8,19,42]`. |
| `GeneralRecurrences.example@204` | Weight id, toll k/2, n=4 gives 42; `[1,1,3,10,42]`. |

The second case uses Nat division. Both proofs connect the actual scanner to
`inclusive_affine_prefixes` using exact ordered flattening. Their equal final
value does not replace the different full traces.

### Actual measured init/last fold

`foldlViaInit_value_and_isTheta` uses the existing
`Resources.ListExecution.foldlViaInit`. For arbitrary value types in independent
universes, fixed natural combine price c, arbitrary combining function and seed,
and any input family with length n, it preserves the ordinary fold value and
proves that the executor's actual charged-work projection is Θ(n²).

The exact work is `1+3*Q(n)+c*n`. A private finite identity identifies it with
the base-one arbitrary-toll fold whose transition toll is `3*k+c`; the new
additive Theta theorem then supplies the growth result. C=3+c,D=1,N=0 retain
upper (4+c,1) and reverse (4,0) witnesses. No c>0 assumption is added.
At c=1 the work values for lengths 0 through 3 are `[1,5,12,22]`; addition with
seed zero on `[1,2]` returns the actual value/work pair `(3,12)`.

These charges use the existing dispatch, cell, and combine model. They do not
assert arithmetic bit cost, elapsed machine time, or parallel span. RC extends
this actual setup with the repeated pipeline described below.

## RC: uniform two-parameter recurrences

RC adds four finite theorems, five filter/growth interfaces, and fourteen public
client/counterfamily/scanner theorems. One private lemma establishes the measured
client's base and successor hypotheses. The source's four definitions are native
expressions or standard filter/asymptotic correspondences; no compatibility
recurrence, growth predicate, evaluator, or scanner subsystem is introduced.

For exposition, let `G(m,n)=m*n+n*n`. The uniform filter is
`Filter.comap Prod.snd Filter.atTop`, equivalently `⊤ ×ˢ atTop`. It retains every
first coordinate, including `m=0`. The new `eventually_comap_snd_atTop` exposes
exactly `∃ N, ∀ m n, N ≤ n → p (m,n)`. The natural-count BigO bridge exposes
`∃ C N : Nat, 0 < C ∧ ∀ m n, N ≤ n → f m n ≤ C*g m n`.
The coefficient and threshold precede both varying parameters. The Theta bridge
preserves two independent directions, each with its own positive natural
coefficient and threshold. Standard `Asymptotics` statements cast the natural
quantities to the reals.

### Native models and finite comparisons

| Source notion | Native correspondence |
| --- | --- |
| `GeneralRecurrences.NatO2` | `Resources.isBigO_natCast_comap_snd_iff`, on the uniform filter above. |
| `GeneralRecurrences.NatTheta2` | `Resources.isTheta_natCast_comap_snd_iff`, with both independent BigO directions. |
| `GeneralRecurrences.twoRun base toll m n` | `(List.range' 1 m).foldl (fun x _ => x + toll n) (base n)`. |
| `Recurrences.twoParam b c m n` | The same fold at base `b*n*n` and constant toll `c*n`. |

`constant_toll_exact` proves `fold=b+m*c` for every natural b,c,m, including
the empty fold. It reuses RB's `additive_toll_exact`. The client contains exact
universal zero, successor, and closed-form connections for both twoRun and
twoParam. Their source definitions are not reproduced as aliases.

`constant_toll_bounds` gives `G≤twoParam` and
`twoParam≤(b+c)*G` for positive b,c and **all** m,n. At n=0 the corrected model
is zero for every m. The client retains separate failures of the lower bound
when b=0 or c=0. `constant_toll_comparison` sandwiches an arbitrary
`T : Nat → Nat → Nat` between independent lower and upper native folds from
separate base and successor premises. It needs no positive-coefficient premise
and calls the retained two affine comparison directions.

For the general eventual theorem, fixed natural B,D,C,E,N satisfy

```text
n*n ≤ D*T(0,n)                 T(0,n) ≤ B*(n*n)
E*T(m,n) + n ≤ E*T(m+1,n)      T(m+1,n) ≤ T(m,n) + C*n
```

for every m and every n≥N. `two_param_eventual_bounds` requires only E>0 and
concludes `G≤(D+E)*T` and `T≤(B+C)*G`. It applies the existing affine comparisons
to E*T and T, retaining the initial contribution and cumulative toll separately.
Only the positive multiplier E is cancelled. The Theta wrapper additionally
names B>0 and C>0; it does not add D>0 or assume the desired asymptotic conclusion.

| Uniform growth theorem | Independent input hypotheses | Upper coefficient / threshold | Reverse coefficient / threshold |
| --- | --- | --- | --- |
| `two_run_recurrence_isTheta` | base Θ(n²), toll Θ(n), with their own witnesses | B+C / NB+NC | D+E / ND+NE |
| `two_param_recurrence_isTheta` | The arbitrary-T base and successor inequalities above; B,C,E>0 | B+C / N | D+E / N |

The arbitrary-T theorem allows successor work to depend on m. It is stronger
than the exact model with an n-only toll and is not replaced by that model.

### Fractional slopes and uniform counterfamilies

The half-toll family `T(m,n)=n*n+m*(n/2)` uses **natural division**.
`fractional_two_param_hypotheses` establishes B=D=C=1,E=3,N=2, and
`fractional_two_param_bounds` derives `G≤4*T` and `T≤2*G` for n≥2.
At m=0,n=3 the scaled lower step is `30≤30`, while the unscaled step
would be `12≤10`. At m=3,n=4 the value is 22 and G is 28. These cases retain
the reciprocal lower multiplier rather than weakening the source obligation.

Three symbolic distinctions accompany the positive results:

| Family | Established distinction |
| --- | --- |
| `(m+1)*n*n` | For each fixed m it is Θ(G), with coefficients m+1 and 1 beyond n=1. There is no uniform BigO: for any proposed C,N, choose n=N+C+1 and m=n*n. |
| `if m=0 then n*n*n else G(m,n)` | It is Θ(G) on ordinary pair-atTop, which eventually excludes the zero fiber using threshold(1,0). On the required uniform filter no BigO bound holds: retain m=0 and choose n=N+C+1. |
| Printed m-toll, unit b=c=1 | Its exact value `n*n+Q(m)` is not uniformly O(G); choose n=N+1 and m=4*C*n+n+1 and use the triangular lower bound. |

The printed-toll **exact** formula `b*n*n+c*Q(m)` remains universal in b,c,m,n
and reuses `additive_exact` through a checked anonymous specialization. Its
negative growth theorem has the stated unit coefficients; it makes no such
negative claim for c=0. At b=c=n=1,m=4, the printed value 11 differs from the
corrected value 5. This is a distinction between the retained source obligations,
not a newly verified textbook or official erratum.

### Actual repeated measured folds

The repeated client binds the actual `foldlViaInit 1` setup to the existing
`Resources.run` over `List.range m`. Pass i executes the actual
`ListExecution.foldl (1+i%2)` on the previous returned state. The combining
function, seed, and element/state types are arbitrary, with independent
universes. The value projection is the ordinary initial fold followed by m
ordinary folds of the same input.

For an input of length n, the exact setup work is `1+3*Q(n)+n`, and pass i costs
`(2+i%2)*n+1`. `repeated_fold_succ` derives the actual next command at index m
from `run_append` and bind associativity. The private hypothesis lemma uses
B=5,D=1,C=4,E=1,N=1; `repeated_fold_value_and_isTheta` then proves both
`G≤2*T` and `T≤9*G` for n≥1 and the uniform Theta result for the **actual work
projection**. The value law is retained alongside those work statements.

On `[1,2]` with addition and seed 0, setup returns `(3,12)`, the three pass costs
are `[5,7,5]`, the successive values are `[3,6,9,12]`, and the composed result is
`(12,29)`. At constant price 1, the exact work specializes to
`1+3*Q(n)+n+m*(2*n+1)`. For an empty input the full pair is `(e,1+m)`;
in particular m=3 gives `(0,4)` at seed 0. Since G(m,0)=0, the positive-input
threshold is retained. These charges follow the existing executor model;
they introduce no extra construction, modulo, dispatch, bit-cost, machine-time,
or parallel-span assertion.

### Actual scanner cases and development evidence

All three source cases use existing scanners with opposite endomorphisms and
exact ordered flattening. The first and third use composed pair plans; the
half-toll case uses a product of a pair and a leaf.

| Source case | Native value | Complete decoded inclusive prefix list |
| --- | ---: | --- |
| `Recurrences.example@214`, b=2,c=3,m=4,n=5 | 110 | `[50,65,80,95,110]` |
| `GeneralRecurrences.example@205`, base n², toll n/2,m=3,n=4 | 22 | `[16,18,20,22]` |
| `RecurrenceDerivations.example@164`, b=c=1,m=4 | 11 | `[1,2,4,7,11]` |

## Ten separately qualified contexts

The context ledger preserves the following limits; RA, RB, and RC do not close
these contexts collectively. Errata descriptions are retained source attributions.

| Context ID | Qualification |
| --- | --- |
| `2.1-cautions` | Theta is not function equality; RB demonstrates one summation coefficient; RC retains uniform two-parameter witnesses and counterfamilies. Exercise 2.2 cancellation remains with GROWTH. |
| `2.2-cost-model` | RA scanner values carry no priced-work conclusion; RB analyzes the existing measured executor; RC composes that setup with actual alternating-price folds. Only the declared executor charges are claimed. |
| `2.2-recurrence-linear-toll` | RA exact c*k and RB eventual Θ(id) have distinct hypotheses; finite exceptional prefixes and positive-index reserves remain explicit. |
| `2.2-recurrence-double` | Independent base and exponential conclusion are retained; RB adds positive-base O(id) tolls and zero-base boundary counterexamples. |
| `2.2-recurrence-factorial` | Native factorial and finite normalization are retained; RB adds positive-base O(id) tolls, without an infinite-series or Stirling claim. |
| `2.2-series` | Reuse half-sum arithmetic and finite reciprocal indexing; separate factorial-prefix obligations retain their existing owner. |
| `exercise-2.8` | The reported corrected n-toll and printed m-toll remain distinct source obligations. RC connects each to its exact native expression and retains the source attribution. |
| `2.8-corrected` | RC establishes uniform Θ(mn+n²) and eventual finite bounds, retaining the positive reciprocal lower multiplier, unrestricted m, and independent base/toll witnesses. |
| `2.8-printed-distinction` | RC retains the universal printed-toll exact solution and symbolic failure of the uniform comparison at b=c=1. It asserts no such negative result for c=0. |
| `ch02-base-coefficient` | The independent base contributes 2^n*b; the empty case rejects an extra factor c. |

## Source correspondence and remaining scope

The [declaration ledger](adwh-recurrences-provenance.tsv) maps 61 selected source
commands and ten qualified context rows to the maintained owners. It retains
source identities, statements, native expressions and mathematical qualifications.
RA denotes finite affine recurrences, RB arbitrary eventual tolls, and RC
uniform two-parameter recurrences. These are coverage groups, not independent
runtime or approval protocols.

The source is checkpoint 335's GeneralRecurrences, RecurrenceDerivations and
Recurrences modules. Its [intake record](adwh-checkpoint-335-intake.md) identifies
the archive. The textbook PDF and a standalone official erratum were not freshly
inspected; the printed/corrected-toll distinction retains its supplied-source
attribution. No complete chapter, whole book, Haskell runtime, scheduler or
machine-performance claim follows from the finite and asymptotic results.

The current source and connected cases participate in conaled's public-entrypoint
build and exhaustive proof audit. Validation and review apply to the integrated
candidate, independently of the retired cloud capture and recovery workflow.
