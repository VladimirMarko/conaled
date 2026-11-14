# Affine upper bounds for contracting recurrences

This is a shared arithmetic unit for the whole-book FDSA reconstruction.
At the 4 November 2026 receiving-preparation snapshot, both independent source
assessments of the original draft were complete with no new XR source findings;
the unit had no compiler, expanded-type, guarded-full-check or audit result.
Current receiving validation and acceptance are recorded in the local
`fdsa-control` review and acceptance evidence. This unit prepares a reusable
argument for later chapter work while preserving the chapter acceptance order.

## Source and scope

The primary source is *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, July 27, 2026 edition, printed pages 41–43, particularly
Theorem 3.9 and its natural-valued corollary. The
[official PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.

The companion reference is Manuel Eberl's
[`Selection.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Selection.thy),
at Isabelle revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, with SHA-256
`c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8`.
Its relevant declarations are `akra_bazzi_light_aux1`,
`akra_bazzi_light_aux2`, `akra_bazzi_light`, and `akra_bazzi_light_nat`.
The pinned Isabelle distribution's top-level license is BSD-3-Clause. That
revision postdates the PDF and is a statement/proof reference, rather than a
claim about the exact source used to generate the book.

The book uses rounded affine child sizes and explicit real quotient witnesses.
The present unit abstracts the child maps and uses a division-free existence
argument. This permits an ordered commutative ring as the scalar carrier and
allows signed function values and signed toll coefficients. The exact source
rounding and prescribed quantitative constants remain separate obligations.

The implementation uses Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, as pinned by the project. The
pre-existing [`Growth.lean`](../../Applications/Resources/Growth.lean) interface
converts a supplied natural bound into a real-cast Big-O statement. The new
arithmetic theorem supplies the preceding recurrence argument; it leaves that
interface unchanged and imports no asymptotic or real-analysis development.

## Public statement

[`Resources.AffineRecurrence.exists_affine_bound_of_two_branch`](../../Applications/Resources/AffineRecurrence.lean)
has scalar requirements

```lean
[CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]
```

For fixed functions `f : Nat → R`, `left right : Nat → Nat`, a natural cutoff
`n0`, and fixed `rho K C D : R`, its assumptions are

```text
rho < 1
for every n > n0:
  left(n) + right(n) <= rho*n + K
  f(n) <= f(left(n)) + f(right(n)) + C*n + D.
```

Natural sizes in scalar expressions are explicitly cast into `R`. The
conclusion is

```text
there exist A B : R with A >= 0 and B >= 0 such that
  for every natural n, f(n) <= A*n + B.
```

The constants are chosen before the input `n`. All inputs are covered, including
zero and the finite prefix where neither recurrence premise applies. Neither
the function nor its child maps must be monotone. No sign assumptions are
made on `f`, `K`, `C`, or `D`; the only explicit restriction on `rho` is strict
contraction. Children have natural domains and hence nonnegative cast sizes.

This theorem concerns an already given total scalar function. Its later proof
cutoff cannot justify a recursive definition that fails to decrease at its
own branch cutoff. A measured algorithm also needs its own theorem connecting
the actual cost observation to this scalar function.

## Division-free witnesses and induction

Write `delta = 1-rho`, which is positive. `Archimedean.arch` chooses a natural
`M` satisfying `2*K <= M*delta`. Set `N = max n0 (max 1 M)`. Thus the cutoff
covers the original base domain, contains at least one, and satisfies
`2*K <= delta*N`.

The prefix maximum is the standard nonempty finite supremum

```text
prefixMax = (Finset.range (N+1)).sup' prefix_nonempty f
B = max 0 prefixMax.
```

`Finset.le_sup'` supplies the bound for every `n <= N`. The prefix is nonempty
because it contains zero. The nonnegative intercept is a convenient choice
for this proof; it does not assert that the book's separate prefix maximum
must be nonnegative.

A second use of `Archimedean.arch` chooses a natural `a` with

```text
2*(max 0 C + max 0 D + B) <= a*delta.
```

The slope `A` is the cast of `a`. Both choices use natural multiples, with
`nsmul_eq_mul` supplying their ring interpretation. There is no division,
floor, completeness or field requirement in the core.

For an input above `N`, the size assumption gives

```text
2*(left(n)+right(n)) <= (1+rho)*n < 2*n.
```

Nonnegative child sizes then imply that each child is strictly below `n`.
`Nat.cast_lt` reflects those inequalities back to naturals before
`Nat.strongRecOn` uses the two induction hypotheses.

The slope choice and `n >= 1` give the absorption inequality

```text
2*(C*n + D + B) <= A*(1-rho)*n.
```

The proof obtains this from explicit multiplication inequalities, using the
positive parts of `C` and `D` and the nonnegative intercept. Combining it with
the two child bounds and the recurrence yields

```text
2*f(n)
  <= 2*A*(left(n)+right(n)) + 4*B + 2*C*n + 2*D
  <= A*(1+rho)*n + 4*B + 2*C*n + 2*D
  <= 2*(A*n+B).
```

Ordered-ring arithmetic finishes the step. The public interface is one ordinary
theorem over functions. Its witness construction and induction calculation
remain internal proof details.

## Connected cases and statement review

The retained clients are in
[`Examples.AffineRecurrence`](../../Examples/AffineRecurrence.lean). At the
4 November 2026 receiving-preparation snapshot, these clients had not been
compiled; the following records their intended mathematics and connections.

### A terminating natural quarter recurrence

`quarter` defines

```text
Q(n) = 1                         when n <= 1
Q(n) = 2*Q(n/4) + n + 1          when n > 1.
```

Its well-founded definition uses `Nat.div_lt_self` at the actual branch cutoff.
The public branch equations support independently calculated values:

| Input | Expected value | Calculation |
| --- | --- | --- |
| 0 | 1 | Base branch |
| 1 | 1 | Base branch |
| 2 | 5 | `2*Q(0)+2+1` |
| 4 | 7 | `2*Q(1)+4+1` |
| 8 | 19 | `2*Q(2)+8+1` |
| 16 | 31 | `2*Q(4)+16+1` |

`quarter_affine_bound` applies the generic theorem to the rational cast of this
defined function with `rho=1/2`, `K=0`, `C=1`, `D=1`, and both child maps equal
to natural division by four. `Nat.div_mul_le_self` establishes the size premise
for all inputs, including those not divisible by four. The actual branch
equation supplies the cast upper recurrence. This is a scalar recurrence
example; it does not claim a cost correspondence with median-of-medians or
with Lean's runtime evaluation of `quarter`.

### Signed integer values and tolls

`signed n = -(n : Int)-1` has negative base value `-1` and satisfies

```text
signed(n) = signed(0) + signed(0) + (-1)*n + 1.
```

Its child maps are zero; `rho=0`, `K=0`, `C=-1`, and `D=1` satisfy the generic
premises. The local toll is `1-n`, which becomes negative. The independently
expected inequality is `signed n <= 0`, retained as `signed_nonpositive`.
`signed_affine_bound` obtains an all-input affine bound through the shared
theorem over `Int`, exercising the absence of a field or nonnegative-function
requirement.

`negative_square_upper` separately retains `-(n:R)^2 <= 0` under ordered-ring
assumptions. At the concrete integer input two, the absolute value is four.
This illustrates why the one-sided conclusion is not an absolute-value bound.
The unit exports no signed-function Big-O theorem. Natural-cost asymptotics
need their nonnegative cast and cost correspondence when using `Growth.lean`.

### Parameters remain outside each invocation's constants

`parameterwise_affine_bound p` applies the theorem to the constant integer
function `f(p,n)=p`, with zero child maps and zero toll. The recurrence parameters
are common, but the finite prefix depends on `p`, so the conclusion has order
`forall p, exists A B, forall n`.

`no_uniform_natural_family_bound` rules out
`exists A B : Nat, forall p n : Nat, p <= A*n+B` by selecting `n=0` and
`p=B+1`. `no_uniform_integer_family_bound` also rules out arbitrary integer
coefficients, choosing a natural `p` above the proposed integer intercept via
`exists_nat_gt`. These witnesses prevent exchanging the parameter and constant
quantifiers without additional uniform prefix information.

## Remaining chapter obligations

The full Chapter 3 ledger still retains the exact natural-ceiling bridges with
negative offsets; the source's displayed child thresholds; its sharper
constant choices, including a possibly negative intercept in C03-041/042;
the actual median-of-medians scalar recurrence and uniform selector-to-cost
correspondence; generalized grouping; and the genuine noncontracting halving
counterexample. A successful check of this shared theorem would not discharge
those items. In particular, the chosen nonnegative `B` and division-free
witnesses do not replace the source's quantitative constant-choice argument.

The theorem supplies a sufficient contraction condition. It neither proves
that every linear recurrence must contract in this way nor subsumes exact
constant-toll tree recurrences whose child sizes sum to `n-1`. Those remain
their direct chapter-specific induction arguments.

## Validation boundary

The frozen shared-unit requirements and source preflight are preserved in the
external `fdsa-control` checkpoint directory. No compiler was run during the
original draft while the earlier Chapter 1 full gate remained active. Static
source and API inspection is not Lean elaboration, an axiom audit or independent
approval. The coordinated workflow requires focused compilation, public-root
integration, the full applicable guarded candidate check and exhaustive audit,
both retained review axes, and immediate final candidate identity verification.
