# Discrete scales, harmonic bounds and actual algorithm observations

This adaptation connects finite natural logarithm, square-root and factorial
estimates, rational harmonic sums, and positive weighted floor-log sums to the
existing conaled algorithms. Shared finite arithmetic lives in
[`SquareKit/DiscreteScales.lean`](../../SquareKit/DiscreteScales.lean),
[`SquareKit/HarmonicBounds.lean`](../../SquareKit/HarmonicBounds.lean) and
[`SquareKit/LogarithmicSums.lean`](../../SquareKit/LogarithmicSums.lean).
The growth consequences, boundary cases and existing-algorithm connections live
in [`Examples/DiscreteEstimates.lean`](../../Examples/DiscreteEstimates.lean).

The source ledger records the selected contracts and maintained destinations.
The public entrypoint includes these modules in the normal build and exhaustive
axiom audit; historical cloud checks do not replace current validation.

## Source surface and native representations

The [source ledger](adwh-discrete-estimates-provenance.tsv) contains exactly
**67 entries: five definitions, 53 named theorems and nine anonymous source
cases**. The eleven context records below are separate from that count.

| Supplied module | Definitions | Theorems | Cases | Total |
| --- | ---: | ---: | ---: | ---: |
| `HarmonicEstimates` | 2 | 14 | 3 | 19 |
| `LogarithmicScales` | 2 | 20 | 3 | 25 |
| `LogarithmicSums` | 1 | 19 | 3 | 23 |

Five source definitions use native representations:

| Source representation | Destination meaning |
| --- | --- |
| `LogScale l` | `∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1)` |
| `RootScale s` | `∀ n, 1 ≤ n → s n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1)` |
| `harmonic n` | The existing global rational `harmonic n`, with native zero and successor equations |
| `reciprocalBlock m k` | `∑ j ∈ Finset.range k, (((m + j + 1 : ℕ) : ℚ)⁻¹)` |
| `weightedLog n` | `∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k` |

There is no copied band predicate, harmonic recursion, reciprocal-block
recursion or weighted-sum function. The `halfOffsetLog` and `halfOffsetRoot`
functions are concrete band fixtures with independently chosen zero values;
they do not replace the arbitrary-function hypotheses.

Native-only theorem dispositions are intentional. The logarithm brackets and
monotonicity, square-root brackets and characterization, exact logarithm of a
power of two, reciprocal sign/order facts, and factorial positivity,
monotonicity, power upper bound and block lower bound retain their existing
owners. They do not require new aliases or a wrapper for each source row.
The ledger distinguishes these absorptions from new shared estimates and
application consequences.

## Natural scales and their boundaries

Write `L(n)=Nat.log2 n` and `S(n)=Nat.sqrt n` in this note. Both are integer
floor operations. For positive `n`, the native logarithm satisfies
`2^L(n) ≤ n < 2^(L(n)+1)`. The lower inequality needs positivity: at zero,
`L(0)=0` but `2^L(0)=1`. Native monotonicity and the upper bracket include zero.
The native root brackets `S(n)^2 ≤ n < (S(n)+1)^2`, the equivalence
`k ≤ S(n) ↔ k*k ≤ n`, and `S(n*n)=n` also include zero.

`DiscreteScales.square_le_two_pow` retains `k*k ≤ 2^k` for `k ≥ 4`.
`log2_le_sqrt` combines this result with the logarithm bracket and `Nat.le_sqrt`
to obtain `L(n) ≤ S(n)` for `n ≥ 16`. The retained comparisons have their source
thresholds; the adaptation does not assert that every threshold is minimal.
The connected cases distinguish `9 > 8` at `k=3`, `L(8)=3 > 2=S(8)`, equality
at `n=16`, and the odd input `n=17`.

`Nat.log2_two_pow` gives `L(2^(2*k))=2*k` directly.
`DiscreteScales.sqrt_two_pow_even` gives `S(2^(2*k))=2^k`, including `k=0`.
The exact powers supply symbolic witnesses below; they are not numerical
approximations or an enumerated family of enormous examples.

The all-natural cubic estimate is

```text
n*n*n ≤ n*n*n + n*n + n*L(n) ≤ 3*(n*n*n).
```

Its zero case remains connected to the public theorem. The natural growth
clients use the existing `Resources.isBigO_of_nat_bound`: coefficient one and
threshold 16 for `n*L(n)` against `n*S(n)`; coefficient one and threshold one
for `2^L(n)` against `n`; and coefficients three/one at threshold zero for the
cubic comparison. These are standard real-cast norm statements with explicit
natural witnesses, without a new natural growth relation.

## Arbitrary rational bands and universal failure

The interval hypotheses quantify arbitrary `l,s : ℕ → ℚ` and constrain only
positive indices. Values at zero can be negative. They imply

```text
n ≥ 2  ⇒  L(n) ≤ l(n) ≤ 2*L(n)
n ≥ 1  ⇒  S(n) ≤ s(n) ≤ 2*S(n)
n ≥ 16 ⇒  n*l(n) ≤ 2*(n*s(n)),
```

with natural quantities cast to `ℚ`. The source's eventual-order constants
remain explicit in the native norm consequences. `logBand_isTheta` uses
forward coefficient two and reverse coefficient one at threshold two;
`rootBand_isTheta` uses the same coefficients at threshold one. The product
comparison uses coefficient two at threshold 16.

Every use of `Resources.isBigO_rat_iff_eventually_le_mul` supplies eventual
nonnegativity of both actual functions. This justifies transport between the
source rational order comparison and standard norm Big O. It does not impose
global nonnegativity on the bands. The floor functions and the half-unit-offset
fixtures satisfy the interval hypotheses. Their independently negative zero
values are retained in the finite and norm clients. An admissible log band
with value one at one demonstrates why the twice-floor upper bound cannot
start at one.

The negative statement retains the full quantifier order:

```text
∀ C : ℚ, 0 < C → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
  C * ((S(n) : ℚ) * (L(n) : ℚ)) < (n : ℚ) + S(n).
```

`DiscreteScales.sqrt_log2_counterexample` selects a natural `k ≥ 4`, `k ≥ N`
and `k > 2*C`, then uses `n=2^(2*k)`. Its proof uses exact power identities
and the finite square/power inequality. `band_counterexample` retains every
admissible pair `l,s`; a proposed coefficient `C` reduces to the floor
counterfamily with coefficient `4*C` beyond `max N 2`.

The corresponding native norm non-Big-O declarations consume these universal
families through the sign-qualified rational bridge. Thus the conclusion
excludes standard real norm constants as well as positive rational source
coefficients. C6 uses that universal result, not a finite numerical test.
Rational bands still do not identify rational numbers with irrational real
logarithms or roots; the exact-section interpretation remains separate.

## Harmonic sums and finite blocks

The existing rational harmonic number is used literally. A shifted block has
exactly `k` positive denominators `m+1,…,m+k`. At `k=0` it is empty; at `m=0`
it begins at one. The native reciprocal nonnegativity statement includes the
totalized value `1/0=0`, while reciprocal antitonicity retains its positive
premise. In particular, totalized division does not justify removing the
positive comparison parameters from the block theorems.

The shared finite statements preserve:

```text
0 ≤ H(n),  0 ≤ B(m,k)
H(m+k) = H(m) + B(m,k)
m ≤ n ⇒ H(m) ≤ H(n)
b > 0 ∧ m+k ≤ b ⇒ k/b ≤ B(m,k)
a > 0 ∧ a ≤ m+1 ⇒ B(m,k) ≤ k/a
m > 0 ⇒ 1/2 ≤ B(m,m) ≤ 1
1 + k/2 ≤ H(2^k) ≤ 1 + k                  (all k)
n ≥ 1 ⇒ L(n)/2 ≤ H(n) ≤ L(n)+2.
```

All divisions here are rational. The dyadic proof uses finite doubling blocks,
including `H(1)=1` at `k=0`; it does not substitute an analytic logarithm bound
for the finite argument. The zero doubling block refutes its positive lower
bound, and a zero upper comparison denominator refutes the corresponding
upper-bound claim. These are retained boundary cases.

For `n ≥ 2`, the shared coefficient statements give
`(1/2)*L(n) ≤ H(n) ≤ 3*L(n)` and the same coefficients after multiplication
by the nonnegative index. Every admissible log band additionally satisfies
`(1/4)*l(n) ≤ H(n) ≤ 3*l(n)` from two. The application consequences are native
rational `IsTheta`, using forward/reverse Big-O coefficients three/two for
`H` and `n*H`, and three/four for arbitrary log bands. Their use sites prove
the actual eventual signs before invoking the accepted rational bridge.

Mathlib's real natural-log estimates for the same harmonic numbers are not
used as a substitute for these finite contracts. Base-two exact logarithm
interpretation and its observation bridge remain obligations of the separate
EXACT work.

## Factorial logarithms and weighted floor-log sums

Natural halving remains floor division; no even-input restriction is added.
`log2_half` starts at two. For `n ≥ 4`, `half_scale_bounds` preserves all three
facts `n ≤ 3*(n/2)`, `L(n) ≤ 2*L(n/2)` and `1 ≤ L(n/2)`.

The half-power bound `(n/2)^(n/2) ≤ n!` holds for every natural input. At zero
and one, the left side is the native `0^0=1`. It consumes the exact existing
block owner `Nat.factorial_mul_pow_le_factorial`, together with native
factorial positivity and monotonicity. The lower log-power inequality keeps
`a ≥ 1`; the upper inequality `L(a^k) ≤ k*(L(a)+1)` covers all `a,k`, including
zero bases and exponents.

From index four, the finite factorial estimate is

```text
n*L(n) ≤ 6*L(n!)    and    L(n!) ≤ 2*(n*L(n)).
```

The native real-cast `factorial_log2_isTheta` retains upper coefficient two,
reverse coefficient six and inclusive threshold four through the existing
natural-bound adapter. No Stirling approximation, constants involving π/e,
or exact-real logarithm theorem is asserted.

For the weighted sum `W(n)=∑ k∈Ico 1 (n+1), k*L(k)`, the generic natural
helpers retain arbitrary `f`. A constant bound uses exactly the `n` positive
indices, and inclusion preserves the nonnegative sum. The shifted lower-block
statement retains the **preceding prefix**:

```text
(∀ i, 1 ≤ i → i ≤ k → B ≤ f(m+i)) ⇒
  prefix(m) + k*B ≤ prefix(m+k).
```

Native interval splitting at `m+1` and the exact block cardinality supply this
claim. Arbitrary `f(0)` is excluded. A fixture with `f(0)=7` and all positive
values one makes that distinction explicit. A constant-block specialization
retains the prefix at all `m,k`, including zero.

For every `n`, the shared bounds are

```text
W(n) ≤ n*n*L(n)
(n/2)*(n/2)*L(n/2) ≤ W(n).
```

The half block has exactly `m=n/2` terms, each at least `m*L(m)`. Its zero case
needs no added positivity premise. From four, two factors of `n≤3m` and one
factor of `L(n)≤2L(m)` give the reverse constant `3*3*2=18`:
`n*n*L(n) ≤ 18*W(n)`. The real-cast Theta consequence retains forward one,
reverse eighteen and threshold four. `W(0)=W(1)=0` follows through the general
upper theorem. These are floor-log weights, not the exact irrational weighted
sum required for complete Exercise 2.7.

## Connections to existing algorithms

### Random-access execution

The M1 clients quantify arbitrary universe-generic elements and a represented
random-access list satisfying `Inv`. With represented length
`n=(fromRA ds).length ≥ 16`, they compose the existing logarithmic work bounds
with `L(n)≤S(n)` to obtain:

```text
(fetchRARun k ds).2 ≤ 2*S(n)+3
(updateRARun k x ds).2 ≤ 2*S(n)+3
(bulkRun ds us).2 ≤ us.length*(2*S(n)+4).
```

The value projections remain the existing optional lookup, `List.set`, and
ordered fold of updates on the preceding result. The bound uses represented
length, not the request index or raw digit count. `Inv` retains the tree
perfection and representation conditions, including the no-trailing-zero
condition. Out-of-range requests remain covered by the totalized value
semantics.

The rank-four `sparse 4 (perfectTree 7 4)` fixture represents length 16. The
source clients retain lookup value seven with charge ten and bound eleven;
updates to eight then nine at the same index retain the sequential final value,
charge 22 and bound 24. The out-of-range lookup case retains `none`. Charges
come from existing structural branch visits and loop visits. This adds an
upper bound to the actual model, without a physical runtime, bit-complexity or
pointwise lower-bound assertion.

### Permutation occurrence counts

M2 uses `Examples.PermutationSearch.count_factorial` on the actual
`FiniteSearch.count`, with arbitrary element type, remaining list and stored
chosen prefix. For `n=remaining.length ≥ 4`, the factorial-log bounds apply to
the actual count. No decidable equality, input distinctness or empty-prefix
premise is added. Equal results remain separate occurrences.

The retained public cardinality chain passes through `count_eq_length`,
`enumerate_selection`, `bySelection_length` and `insertion_length`.
An eight-entry repeated input has 40320 occurrences and floor logarithm 15,
independently of its stored prefix. The source C7 equation is connected through
that actual counter. Its proof uses the public factorial equation before small
native arithmetic and does not enumerate 40320 output lists. Empty remaining
input has one current-state occurrence and logarithm zero for every prefix.
These are occurrence-count observations, not distinct-result counts, total
work bounds or comparison-decision-tree lower bounds.

### Inclusive harmonic and weighted prefixes

M3 composes the existing `Scanner.inclusive_correct` with
`SquareKit.ListFusion.scanl_prefix_values`. The generic theorem quantifies
`A : Type u` with `[AddCommMonoid A]`, an arbitrary existing scanner, shape and
input. Its adequacy premise describes only the flattened input as the supplied
length-`n` list of additive values. It concludes the actual inclusive sequence
of finite prefix sums, including the initial zero; it does not assume those
outputs.

The rational harmonic specialization uses successor reciprocals. The composed
pair plan on `[1,1/2,1/3,1/4]` yields
`[0,1,3/2,11/6,25/12]`; the second noninitial and final positions connect C1 and
C2. Finite dyadic/logarithmic bounds apply to the actual returned total. The
weighted specialization uses `[0,2,3,8]`, yields `[0,0,2,5,13]`, and connects C8
to the same positive-interval expression as the shared weighted bounds. Both
empty plans return `[0]`. The generic endpoint theorem also carries the weighted
coefficient-eighteen estimate to the actual run. These are semantic and exact
arithmetic results; no parallel scheduler, work/span, floating error or machine
timing result is added.

## The nine source cases

Names in this table have prefix `Examples.DiscreteEstimates.`. Their actual
contracts and destination declarations are recorded in the source ledger.

| Case | Source coordinate | Public connection |
| --- | --- | --- |
| C1 | `HarmonicEstimates.example@154` | `harmonic_two`, through `harmonic_four_prefixes` and the generic actual-prefix theorem |
| C2 | `HarmonicEstimates.example@155` | `harmonic_four`, through the same actual scanner endpoint |
| C3 | `HarmonicEstimates.example@156` | `reciprocal_block_eight_bounds`, using the general positive doubling theorem |
| C4 | `LogarithmicScales.example@212` | `source_log2_twenty`, using native `Nat.log2_two_pow` |
| C5 | `LogarithmicScales.example@213` | `source_sqrt_twenty`, using `sqrt_two_pow_even 10` |
| C6 | `LogarithmicScales.example@214` | `source_floor_not_isBigO`, using the universal counterfamily and standard norm bridge |
| C7 | `LogarithmicSums.example@194` | `factorial_eight_log2`, through `permutation_repeated_eight` and the actual count owner |
| C8 | `LogarithmicSums.example@195` | `weighted_four`, through the actual weighted inclusive prefixes |
| C9 | `LogarithmicSums.example@196` | `weighted_sixteen_bound`, directly using the general bound at 16; `weighted_sixteen_value` separately records 389 |

The independent value for C9 is obtained from dyadic blocks:
`0+5+44+276+64=389`. The source inequality still consumes the general theorem;
that arithmetic check does not replace the quantified bound.

## Eleven separate source contexts

All eleven records retain their original IDs, JSON pointers, group ownership,
source statements and qualifications from the supplied Chapter 2 ledger,
SHA-256 `a8f205eac08b753c283171d172507b55358af369da09f7173e53df755c626ff1`.
The first three are direct selected-group contexts; the other eight are
supporting associations with their original owners. **Every context remains
partial/supporting.** Statements that the reference itself completed an exercise
are retained as source attribution, not inherited as conaled completion.
Printed/PDF coordinates below are supplied ledger coordinates. The PDF was not
available or visually inspected.

| Context | Pointer | Printed / PDF pages | Selected portion and remaining boundary |
| --- | --- | --- | --- |
| `2.2-cost-model` | `/body_items/5` | 27,28 / 44,45 | Actual M1 charges, M2 occurrence semantics and M3 semantic observations are distinguished. Broader demand/accounting contexts keep their original owners; mathematical growth is not automatically runtime. |
| `exercise-2.7` | `/exercises/6` | 39,41 / 56,58 | Positive weighted floor-log upper and half-interval lower bounds support EXACT. The complete exact weighted-log exercise remains separate. |
| `2.7-growth` | `/exercises/6/subquestions/0` | 39,41 / 56,58 | Retain the common upper and half-block lower estimates; no exact-log interpretation or whole subquestion closure is inferred. |
| `2.1-growth-examples` | `/body_items/1` | 25,26 / 42,43 | Cubic and `n*H(n)` estimates supply the discrete portion. Polynomial sums keep their SUMS owner; exact logarithm meaning keeps its EXACT owner. |
| `exercise-2.5` | `/exercises/4` | 39,40,41 / 56,57,58 | Five discrete log/root/harmonic/factorial portions support the exercise. This tranche does not resolve all seven assertions or their exact-expression interpretation. |
| `2.5-log-sqrt` | `/exercises/4/subquestions/2` | 39,40,41 / 56,57,58 | Integer and arbitrary rational-band comparison retained; exact analytic/section transport remains separate. |
| `2.5-false-root-log` | `/exercises/4/subquestions/3` | 39,40,41 / 56,57,58 | Every rational coefficient and threshold and the standard norm consequence are retained. The exact-expression coefficient model remains an EXACT obligation. |
| `2.5-harmonic` | `/exercises/4/subquestions/4` | 39,40,41 / 56,57,58 | Literal rational harmonic values and finite floor-log estimates are retained. Transfer to the exact base-two logarithm remains separate. |
| `2.5-exp-log` | `/exercises/4/subquestions/5` | 39,40,41 / 56,57,58 | The positive bound `2^floor(log2 n)≤n` is retained; it is not the exact real exponent/logarithm identity. |
| `2.5-log-factorial` | `/exercises/4/subquestions/6` | 39,40,41 / 56,57,58 | Finite products and integer-log order are retained; exact-log transport remains separate. |
| `context-1` | `/explicit_context_dispositions/0` | No pages assigned by this record | Full Stirling expansion is cited stronger background. It is not required for the finite log-factorial target and is not claimed here. |

## Source identities, recovery and evidence boundary

The selected source payloads are the three exact ADWH335 archive members:

| Member under `project/adwh-lean/ADWH/Chapter02/` | Bytes | SHA-256 |
| --- | ---: | --- |
| `HarmonicEstimates.lean` | 6,263 | `9f1a4b93e8d89932789e06e789ba796b55c4b876f077a26fb67fd88639d307d0` |
| `LogarithmicScales.lean` | 8,318 | `e816b3cefe8e48732a786f7210de682143a9d246e3b75019e6520b01ef264090` |
| `LogarithmicSums.lean` | 7,199 | `3eec8a6a73499b79c4282620844121ebe722d88b1a03f56baac5f0ffdc9cdc7c` |
