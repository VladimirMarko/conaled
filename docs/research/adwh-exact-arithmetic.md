# ADWH exact arithmetic through native relational compilation

## Scope and source authority

This development implements the released exact-arithmetic slice of
Chapter 2: all **89 source commands**. The 66 commands of
`ADWH.Chapter02.ExactGrowthSemantics` comprise 12 definitions, one inductive
declaration, 48 theorems and five source cases. The 23 commands of
`ExactGrowthClaims` comprise seven definitions, 11 theorems and five source
cases. The native consumers are M1 stack execution, M2 interval compilation,
M3 positional-search population and M4 weighted prefix scanning, together with
E5's fixed-coefficient correspondence. These counts describe source commands,
not quotas for new native declarations. Ordinary rational division, set
inclusion and standard norm asymptotics use existing mathematics; the expression
grammar maps into the existing typed frontend.

The [row provenance table](adwh-exact-arithmetic-provenance.tsv) also retains
all 89 implemented commands and **ten separately qualified context rows**.
It records source command spans, hashes, actual native owners,
contract qualifications. Supplemental
compiler and client theorems do not increase the original source-row count.

## Ownership and interpretation

| Native owner | Responsibility |
|---|---|
| `SquareKit/NonnegativeArithmetic.lean` | Rational witness sets, ordinary rational closure, strict partial values, relation certificates, attained bounds, precision and order. |
| Existing `FirstOrderCompiler.Term`, `eval` and `compile` | Typed syntax, variables, unit, products and shared bindings; evaluation and compilation are reused. |
| Existing `FirstOrderRelations` | Encoded environment/result carriers, the primitive certificate interface and universal relational preservation. |
| `Applications/Intervals/ExactArithmetic.lean` | Real-point enclosure by the existing rational interval operations and a strict optional interval interpretation. |
| `Examples/ExactArithmeticPipeline.lean` | The actual stack compiler, arbitrary stack-tail preservation, source observations, boundary cases and interval/stack composition. |
| Existing `Applications/Resources/Growth.lean` | One reusable NNReal-to-real norm-growth equivalence with positive natural coefficients. |
| `SquareKit/ExactGrowthBounds.lean` | Sharp raw logarithm bounds and finite real estimates derived from the existing discrete bounds; no application imports. |
| `Examples/ExactGrowth.lean` | Partial-value growth correspondence, the seven native term families, attained weighted bounds, all source Claims, qualified norm growth and irrational-coefficient cases. |
| `Examples/ExactGrowthApplications.lean` | Exact logarithms of the actual positional counter and every actual weighted scanner prefix, with value/section and boundary cases. |

The small `Prim` vocabulary has four constant families and two binary
operations. Its value carrier is the existing `WithBot NNReal`. A negative
rational, `logarithm 0` or `exponentiatedLogarithm 0` is invalid; every natural
square root is valid. `strictAdd` and `strictMul` explicitly use `WithBot.map₂`.
Both operations propagate invalidity, including when the other operand is
valid zero. Existing Ring arithmetic interfaces retain their original domain.

For a natural `n`, the raw sets retain the original finite natural witnesses:

```text
logApprox n = {p/q | p,q : Nat, q>0, 2^p <= n^q}
rootApprox n = {p/q | p,q : Nat, q>0, p*p <= n*q*q}
expLogApprox n = {r/s | p,q,r,s : Nat, q>0, s>0,
                         2^p <= n^q, r^q <= 2^p*s^q}
```

Fractions here are ordinary rational division. Representation independence
retains positive denominator premises and all natural radicands, including
zero. The log/root upper-bound laws retain their supplied finite power/square
hypotheses; floor lower bounds are actual raw members.

`closedSection A` is `closure (lowerClosure A : Set ℚ)` in the ordinary rational
topology. For every set `A` and every rational query `a`, its membership theorem
is equivalent to the original positive-rational tolerance observation:
for every rational `ε>0`, some `b∈A` satisfies `a≤b+ε`.

`Rel A ⊥` means `A=∅`. Relating `A` to a finite nonnegative real requires every
raw member to be nonnegative and every rational query in its closed section to
be exactly a lower bound on that real value. The real-image least-upper-bound
proofs justify this characterization and its preservation by actual
`Set.image2` addition and multiplication. Empty sets and valid zero have
separate cases.

`rawPrimitives` contains the six concrete certificates. For every typed term,
`rawTerm` is the implementation component of the existing
`FirstOrderCompiler.compile` into `FirstOrderRelations.target`; `valueTerm` is
the existing `eval`. `rawTerm_related` preserves their relation for every
context, result type and related encoded environment. The six constructor
equations and the native let equation expose the actual compiled operations.
There is no extra recursive expression evaluator.

For every closed term, raw emptiness, closed-section emptiness and invalidity
are equivalent. For **all rational queries**, section membership is the
existence of a finite value above that query. Section inclusion is exactly the
existing partial-value order. General native terms may discard an invalid
component: `let x = logarithm 0 in rational 1` has value one. A traversal that
required every leaf to be valid would misstate this semantics.

## Attainment, precision and endpoint distinctions

`RawBounds A lo hi` and the closed-term `Bounded` interface retain both
`lo∈A` and the universal raw upper bound `A⊆Iic hi`. This supplies actual lower
attainment in addition to real enclosure. Addition, multiplication and natural
scaling preserve these contracts with their original hypotheses.

Positive `n` has log value `Real.logb 2 n`; all natural `n` have square-root value
`NNReal.sqrt n`. Positive ExpLog has value `n`, with a separate positive-domain
`Real.rpow_logb` identity and a finite-witness cofinality proof. ExpLog at zero
remains invalid even though the totalized real expression is one.

For every positive natural denominator `q`, the prescribed log/root lower
endpoints are attained raw observations, the upper endpoints are the next
rational grid points, and their width is `1/q`. The arbitrary-precision
theorems choose a denominator whose reciprocal is **strictly** below the
requested positive rational tolerance. The q10 example explicitly records
that a width of `1/10` is not strictly below a tolerance of `1/10`.

The checked boundary cases distinguish raw observations from closure:

| Case | Raw and closed behavior |
|---|---|
| `sqrt(2) * sqrt(2)` | Raw endpoint `2` is absent; closed endpoint `2` is present. |
| `ExpLog(3)` | Raw endpoint `3` is absent; the closed section is exactly `(-∞,3]` on rational queries. |
| `ExpLog(4)` | Raw endpoint `4` is attained by finite witnesses. |
| `0 * logarithm 0`, either operand order | Empty raw set, empty section, invalid value and absent interval. |
| `0 * sqrt(2)` | Raw singleton `{0}`, every nonpositive rational in the section, valid zero and interval `[0,0]`. |
| Negative rational atom | Invalid with empty observations, including negative queries. |
| Rational zero, root zero and log one | Valid zero; every nonpositive rational query belongs to the section. |

## Actual stack and interval clients

`stackCode` invokes the existing `StackMachine.target` through the same compiler;
`stackRun` invokes the existing machine. Its correctness theorem covers every
typed term, environment, result type and arbitrary typed stack tail. The raw
and interval relations then compose with that actual stack result.

The shared example is the existing native let term
`let x = sqrt(2) in x*x+x`. Its exact value is `2+sqrt(2)`, with a proof of
irrationality and an all-rational section characterization. The stack client
returns that value and preserves every supplied tail.

The interval module observes real points between rational endpoints. It proves
enclosure for the existing singleton, addition and four-corner multiplication
operations, allowing arbitrary enclosing intervals, including negative
endpoints. Its optional relation preserves validity exactly. For every `q>0`,
the four atom certificates and two strict operations instantiate the existing
relational compiler, giving `compile_contains` for all typed terms and related
environments.

| Actual q10 compiled term | Rational interval output |
|---|---|
| `sqrt(2)` | `[7/5, 3/2]` |
| `sqrt(2) * sqrt(2)` | `[49/25, 9/4]` |
| Shared `x*x+x` | `[84/25, 15/4]` |
| `logarithm 3` | `[3/2, 8/5]` |
| `ExpLog(3)` | `[29/10, 3]` |

The final shared-term theorem composes this actual interval output with the
actual stack run, so `[84/25,15/4]` encloses `2+sqrt(2)`. A separate negative
endpoint case squares `[-1,2]` with the existing multiplication, obtains
`[-2,4]` and proves it encloses two. For general `q>0`, root zero and log one
retain their prescribed `[0,1/q]` intervals, rational zero yields `[0,0]`, and
discarding an invalid let-bound value yields `[1,1]`.

## Fixed coefficients and qualified norm growth

Source Big O is expressed directly as an existential positive natural
coefficient and an eventual comparison in the existing partial-value order.
Section inclusion, threshold form and the two independent directions of Big
Theta are proved equivalent. These correspondences cover arbitrary closed-term
families, including invalid values.

`growth_iff_exact_coefficient` proves the full equivalence with one fixed exact
term coefficient `c` and attained rational bounds `lo,hi` satisfying `0<lo`.
The coefficient and bounds are chosen before the eventual index. In the reverse
direction, `bounded_multiplier_dominated` uses the explicit positive natural
coefficient `(ceil hi : Int).natAbs + 1`. That domination lemma itself does not
require a positive lower bound and applies to every multiplied expression,
including an invalid one.

The standard norm Big O/Theta bridge is separately qualified: both families
must eventually have their actual finite NNReal values on a common filter
event. It applies to an arbitrary index universe and filter. The zero-default
variant proves equality to an explicitly NNReal-typed `WithBot.unbotD` on the
validity event. The constant valid-zero and invalid-log-zero families show why
discarding this premise changes source growth despite both real defaults being
zero.

The irrational coefficient `sqrt(2)` has attained bounds `[7/5,10/7]` and a
positive lower endpoint. It supplies a nonvacuous unit-growth example. The
separate finite `n=64` case has left value `72` and right bounds
`[336/5,480/7]`, whose upper endpoint is below `72`. The universal refutation now
uses the symbolic discrete counterfamily separately: for every positive natural
coefficient `C` and every threshold `N`, the existing discrete result at rational
coefficient `4*C` and threshold `max N 2` supplies an index where the real
`C*sqrt(n)*log₂(n)` is strictly below `n+sqrt(n)`. Real floor bounds justify the
transport. This yields the source natural-coefficient negation, the full fixed
bounded-positive-exact-coefficient negation and the standard real norm negation.
The coefficient and its finite bounds precede the eventual threshold in each
exact-coefficient statement.

## Exact families and finite growth witnesses

The seven builders use the existing `ClosedTerm` constructors. In particular,
`weightedLogExpr n` is a left fold over `List.range n`, beginning with rational
zero and adding `(j+1)*logarithm(j+1)`. The zero index is excluded from each
logarithmic summand. Its successor equation, actual finite value and all-rational
section characterization connect this syntax to
`Y(n) = ∑ k ∈ Ico 1 (n+1), k*Real.logb 2 k`.

| Family | Actual real value on its valid domain | Domain |
|---|---|---|
| `nLog` | `n*log₂(n)` | `n ≥ 1`; invalid at zero. |
| `nRoot` | `n*sqrt(n)` | Every natural `n`. |
| `nPlusRoot` | `n+sqrt(n)` | Every natural `n`. |
| `rootLog` | `sqrt(n)*log₂(n)` | `n ≥ 1`; invalid at zero. |
| `nSquareLog` | `n²*log₂(n)` | `n ≥ 1`; invalid at zero. |
| `cubicLowerTerms` | `n³+n²+n*log₂(n)` | `n ≥ 1`; invalid at zero. |
| `weightedLogExpr` | `Y(n)` | Every natural `n`, including the empty zero fold. |

The sharp raw logarithm theorem retains `Bounded (logarithm n) floor (2*floor)`
for `n ≥ 1`. The log-one case has the exact attained interval `[0,0]`.
Induction on the actual weighted fold then gives attained raw bounds `[W,2*W]`,
where `W = ∑ k ∈ Ico 1 (n+1), k*Nat.log2 k`. This is distinct from the real
enclosure `W ≤ Y ≤ 2*W`: the raw theorem also proves that `W` is an actual member.
Both the empty and one-term weighted folds have attained bounds `[0,0]`.

The finite section comparisons preserve the prescribed coefficients and domains:

| Comparison | Forward coefficient | Reverse coefficient | Threshold |
|---|---:|---:|---:|
| `n*log₂(n)` and `n*sqrt(n)` | 2 | — | 16 |
| `harmonic(n)` and `log₂(n)` | 3 | 4 | 2 |
| `n*harmonic(n)` and `n*log₂(n)` | 3 | 4 | 2 |
| Positive exponentiated logarithm and `n` | 1 | — | 1 |
| `log₂(n!)` and `n*log₂(n)` | 4 | 12 | 4 |
| `Y(n)` and `n²*log₂(n)` | 2 | 36 | 4 |
| `n³+n²+n*log₂(n)` and `n³` | 6 | 1 | 1 |

Each comparison first supplies actual finite NNReal payloads and their displayed
real values. The eight standard real `IsBigO`/`IsTheta` conclusions, including
the unrestricted negative result, use both eventual finite-value events through
the accepted growth equivalence. The two NNReal defaults used internally are
identified with actual values on those events. No equivalence based on arbitrary
zero-defaulted invalid terms is asserted. The five source examples are retained
as named consumers of the public general claims.

## Native search and weighted scan consumers

M3 uses `FiniteSearch.count PermutationSearch.next remaining.length
(chosen, remaining)` itself. The existing factorial theorem applies to an
arbitrary element universe, input list and stored prefix, without distinctness
or a decidable-equality premise. Its exact logarithm has the finite semantic
value and section equivalence for every rational query. For length at least four,
the finite coefficients 4 and 12 hold both over the real count logarithm and in
the actual term's section order.

Eight repeated equal entries count 40,320. Integer power comparisons give
`15 < log₂(40320) < 16`; the exact section accepts 15 and rejects 16, and the
value differs from the discrete floor 15. Empty remaining input at depth zero
counts one and has valid log value zero. Positive depth on empty input counts
zero and has an invalid logarithm and empty section. These theorems concern
population magnitude, without enumerating outputs or asserting execution time
or a decision-tree bound.

M4 specializes the existing generic finite-prefix theorem to `Multiplicative ℝ`
and any actual `Scanner`. Its premise describes the flattened input as the
positive weighted sequence. Its conclusion gives all `n+1` actual prefixes.
For every `k ≤ n`, the indexed output equals a finite value of `weightedLogExpr k`,
with the same closed-section observation for every rational query. The final
total follows from the existing scanner total theorem.

The actual composed pair/pair plan takes `[0, 2, 3*log₂(3), 8]` and produces
`[0, 0, 2, 2+3*log₂(3), 10+3*log₂(3)]`. The integer inequalities `16 < 27 < 32`
give a final value strictly between 14 and 15, so the exact section accepts 14
and rejects 15. Separately, the weighted-four raw bounds remain `[13,26]`, with
13 attained; the actual total is not 13. The empty actual scan produces `[0]`
and the empty weighted term has finite value zero. No work/span or floating-point
accuracy guarantee is inferred.

## Qualified context obligations

All 89 selected source commands and M1–M4 now have native implementations.
That accounting does not automatically close the ten source-ledger contexts.
Their exact coordinates and shared ownership remain unchanged, and formal
acceptance is separately recorded after the prescribed gates. In particular,
neither the coarse factorial-log equivalence nor the search client proves full
Stirling asymptotics.

| Context row | Remaining qualification |
|---|---|
| `2.1-growth-examples` | Exact cubic and harmonic/n-harmonic growth are implemented. Polynomial portions retain SUMS ownership; no whole-context closure is inferred. |
| `2.2-cost-model` | M1–M4 give mathematical semantic composition and actual count/scan observations, with no new charged-operation, CompositionDemand, execution-time or cost claim. Preserve every shared group. |
| `exercise-2.5` | Five exact subitems are implemented and remain distinct from the two SUMS polynomial subitems. Whole-exercise closure requires their separate accounting and source qualifications. |
| `2.5-log-sqrt` | The exact coefficient-2 threshold-16 section bound and its qualified real norm conclusion are implemented; retained source/PDF qualifications remain. |
| `2.5-false-root-log` | The universal natural and fixed finite exact coefficient refutations and standard norm negation are implemented. The coefficient/bounds precede the threshold; finite64 is a separate case. |
| `2.5-harmonic` | Exact harmonic/log and n-harmonic/n-log coefficients 3/4 from two are implemented, preserving actual finite values and positive log domains. |
| `2.5-exp-log` | The exact coefficient-1 threshold-1 assertion is implemented with guarded value/rpow identity. Invalid zero and the raw/closed endpoint distinctions remain. |
| `2.5-log-factorial` | Coefficients 4/12 from four and actual M3 are implemented; no full Stirling, output enumeration, runtime or decision-tree claim. |
| `exercise-2.7` | DISCRETE `W`, actual exact `Y`, attained raw bounds, exact growth and actual M4 are accounted for separately; no automatic whole-exercise closure. |
| `2.7-growth` | Exact coefficients 2/36 from four, attained raw `[W,2W]` and all actual M4 prefixes are implemented. No work/span or floating-point guarantee. |
