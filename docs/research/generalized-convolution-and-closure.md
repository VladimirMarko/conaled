# Generalized convolution and weighted closure

Research date: 2026-11-23. Repository inspected at `e308b692`; Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. This is a research proposal, not an
architecture decision or a claim that the proposed bridges have been proved.
The calculations below are mathematical arguments, not new Lean-checked results.

The most useful extensions appear to be proper weighted word closure, a shared
finite-decomposition convolution construction, and finite-support monoid
algebras. These solve different problems. Arbitrary-monoid multiplication does
not automatically supply star, and star does not require arbitrary infinite
summation when the input prevents infinitely many contributing decompositions.

## What can be reused

[Series.lean](../../Applications/Convolution/Series.lean) already supplies
executable word convolution over any semiring, including noncommutative
coefficients. `convolution_splits` identifies the implementation with the sum
over prefix/suffix splits. Its semiring laws, `derivative_mul`, and
`mapCoefficients` are the existing contracts to preserve.
[Polynomial.lean](../../Applications/Convolution/Polynomial.lean) supplies a
redundant finite representation with meaning-preserving multiplication and
normalization. Generalizing its indexing monoid would extend this finite
representation independently of all-function convolution.

[ADR 0004](../adr/0004-convolution-and-languages.md) distinguishes coefficients,
Boolean recognition, and parse witnesses. The proposed extensions retain that
distinction. In [Witnesses.lean](../../Applications/Languages/Witnesses.lean),
`nullableStarIso` identifies empty-word star parses with lists of empty parses;
`derivativeStarIso` retains those empty parses before a consuming parse. These
are stronger observations than mere nonemptiness. The existing
[ConvolutionBridge](../../Applications/Languages/ConvolutionBridge.lean) forgets
natural-number weights through `supportHom`; it does not establish a generic
weighted closure theorem.

Elliott's corrected extended manuscript provides three relevant constructions:
finite maps over arbitrary monoids (§5), weighted star differentiation
(Lemma 11), and heterogeneous `lift2` for operations whose input and output
index types differ (§11). Its `StarSemiring` assumes the two unfold equations;
those assumptions are weaker than Conway identities or Kleene induction. The
recursive Haskell default is not a Lean termination argument, and an unfold
equation alone does not establish a least or unique solution.
[Elliott, corrected extended version](https://conal.net/papers/convolution/convolution-long.pdf).

## Multiplication and closure have different hypotheses

For a monoid `M`, the intended coefficient formula is

```text
(f ⋆ g)(x) = ∑ over (u,v) with u*v=x, f(u)*g(v).
```

There are several ways to make this meaningful. The table states sufficient
regimes; it is not a list of necessary conditions.

| Representation or setting | Multiplication | Closure |
|---|---|---|
| Finite-support `M →₀ R`, arbitrary monoid | Finite sum over pairs of supported inputs | Generally leaves finite support |
| All `M → R`, finite binary factorization | Finite sum for each output | Needs additional control of repeated factorization |
| Word series with `f [] = 0` | Existing convolution | Each output needs only finitely many powers |
| Word series over a Conway semiring | Existing convolution | Coefficient star handles empty factors; word recursion handles consuming factors |
| All functions into a complete semiring | Arbitrary indexed sums with partition and distributivity laws | Sum of powers |
| Quantale-valued functions | Suprema over decompositions | Supremum of powers; addition is idempotent |
| Summable functions in a topological setting | Convergent sums under stated hypotheses | Requires additional convergence hypotheses |

Dongol, Hayes and Struth prove convolution lifting for relational monoids into
unital quantales (Theorem 4.8), and for finitely decomposable monoids into
semirings (Corollary 4.10). Their
[LMCS paper](https://lmcs.episciences.org/7164/pdf) links to Isabelle
formalizations; the [AFP entry](https://isa-afp.org/entries/PSemigroupsConvolution.html)
is a useful independent reference for the relational and quantale layer.

Several small calculations separate these regimes:

* On the additive group `ℤ`, every integer has infinitely many decompositions
  `n = k + (n-k)`. Constant natural-number series therefore have no finite
  convolution coefficient. Finite-support inputs still multiply normally.
* In the two-element group `{e,g}`, binary factorization is finite. Nevertheless,
  the proper series `δg` satisfies `(δg)^(2n)(e)=1` for every `n`. Thus properness
  at the identity does not make star coefficientwise finite on arbitrary monoids.
* Even on words, a natural-number series with `f []=1` cannot have a star
  satisfying the left unfold equation: its empty coefficient would satisfy
  `x=1+x` in `ℕ`. Enlarging coefficients or restricting operands changes this.
* A singleton nonempty word has a star with infinitely many supported words.
  A finite polynomial representation cannot generally be closed under star.

For an executable generalization, finite factorization should include an
enumeration with a correctness theorem. Abstract finiteness alone does not
provide an executable enumeration. A positive additive grading can bound the
number of nonidentity factors, but does not by itself make every binary
factorization set finite; these are separate obligations.

## Proper and nullable weighted word closure

Call a word series proper when `f [] = 0`. Define, for a word `w`,

```text
properStar(f)(w) = ∑ n in {0,...,length(w)}, (f^n)(w).
```

Every nonzero factor consumes at least one character, so powers above the
length bound contribute zero. At the empty word the term `n=0` contributes
one. This gives a direct finite specification for an executable recursive
implementation. A useful theorem is uniqueness of solutions to `x=f⋆x+r`
for proper `f`, rather than just a selected fixed point.

Bloom, Ésik and Kuich establish precisely this proper-series partial iteration
structure over arbitrary semirings (Corollary 5.9). Their Remark 5.11 explains
the extension from coefficient Conway or iteration semirings to all word
series. Thus proper closure can retain natural-number counting, while a total
star needs more structure on coefficients.
[Partial Conway and iteration semirings](https://arxiv.org/pdf/0712.2952).

For nullable operands with an appropriate coefficient star, the recursive
specification is

```text
f*([]) = (f([]))*
f*(w)  = (f([]))* * ∑ over w=u++v, u≠[], f(u)*f*(v)   (w≠[]).
```

The suffix is shorter, and the factor order matters for noncommutative
coefficients. The matching derivative law is
`Dₐ(f*) = scale ((f [] )*) (Dₐ f ⋆ f*)`, as in Elliott's Lemma 11.
The coefficient-star factor accounts for repeated empty pieces. Dropping it
would reproduce the information loss already excluded by `derivativeStarIso`.
[Elliott, Lemma 11](https://conal.net/papers/convolution/convolution-long.pdf).

Proposed checked cases are an ambiguous proper expression with a coefficient
greater than one, its Boolean support, and a nullable expression over an
explicit coefficient algebra supporting star. Counting arbitrary witness types
also needs finite fibers and weight assignments; the existing witness
isomorphisms alone do not provide finite cardinalities. A weighted automaton
with finitely many states and consuming transitions is another useful target:
on a fixed word its run sum is finite. Epsilon cycles require the same closure
analysis as nullable expressions.

## Generalizations that connect existing work

**Other monoids.** Additive natural numbers recover Cauchy multiplication of
ordinary series; finite products of natural numbers give multivariate indices.
Finite cyclic groups give cyclic convolution. A proposed connection to
[Parallel FFT](../../Applications/Parallel/FFT.lean) should prove the precise
transform/multiplication identity under its scalar and normalization
assumptions. It should distinguish cyclic convolution from ordinary convolution
with zero padding. The monoid interface alone proves neither FFT correctness
nor an efficient algorithm.

**Categories and intervals.** Replacing monoid elements by category arrows
allows convolution over factorizations of a fixed arrow. A finite path has
finitely many cuts, even when its graph has infinitely many edges. Locally
finite posets supply interval convolution; finite pair groupoids supply matrix
multiplication. Closure on paths and intervals can use decreasing length,
whereas matrix loops usually need coefficient or matrix star. This suggests a
later category-valued decomposition interface after the monoid specializations
have established which parts are shared.

**Witnesses and shuffle.** A shuffle product must specify whether it counts
interleavings. There are two interleavings of two identical singleton letters,
although both produce the same word. Boolean existence forgets this distinction.
The binomial coefficients in
[`Jets.jet_leibniz`](../../Applications/AD/Jets.lean) suggest a concrete target
for multiplicity-aware decomposition. Relating ordinary and exponential
generating series would additionally require justified factorial rescaling;
division is unavailable over arbitrary semirings. This is a proposed bridge,
not an identity established by the current convolution library.

**Coalgebra and heterogeneous operations.** Coassociative decomposition and
associative coefficient multiplication explain the shape of convolution laws.
Mathlib's linear-map convolution is a candidate comparison, but its module and
tensor requirements should not be imposed on the existing arbitrary-semiring
word API. Elliott's `lift2` also suggests finite-support pushforward along
`h : A → B → C`, connecting sized arrays and independent finite distributions.
It need not produce a semiring unless the indexing operation has the relevant
laws. These are opportunities for shared preservation proofs, not reasons to
replace every representation with one carrier.

## A boundary for relational decompositions

Cranch, Struth and Wagemaker's 2025 preprint develops recursive convolution star
using finite nonidentity decomposition, including Möbius categories and
relational generalizations. It is a useful source for the category extension.
Its Theorems 4.2 and 10.1 state general semiring/Conway liftings for catoids;
the following calculation identifies an assumption that must be checked before
using the non-idempotent relational claim.
[Generalised Möbius Categories and Convolution Kleene Algebras, v1](https://arxiv.org/html/2509.00168v1).

Take elements `e,a,b,c,p,q,r,z`, with `e` a two-sided identity. Set

```text
a∘b={p,q}     p∘c={z}     q∘c={z}
b∘c={r}      a∘r={z}
```

All other products of nonidentity elements are empty. Let every source and
target be `e`. Relational associativity holds: the only nonempty triple of
nonidentity elements is `(a,b,c)`, and both bracketings give `{z}`. Assigning
degrees `1` to `a,b,c`, `2` to `p,q,r`, and `3` to `z` bounds nonidentity
decomposition lengths; the carrier is finite. But natural-number convolution
gives

```text
((δa ⋆ δb) ⋆ δc)(z) = 2
(δa ⋆ (δb ⋆ δc))(z) = 1.
```

This is an unformalized counterexample to obtaining non-idempotent weighted
associativity from these relational axioms alone. It is not a review of every
result in the paper. A safe proposal uses functional composition, idempotent
coefficients, or explicit decomposition witnesses with a reassociation
bijection. The last option also preserves shuffle and parse multiplicities.

## Reuse in the pinned Mathlib

The following source inventory was checked against the pinned revision, not
inferred from current online documentation. Links name the same revision.

| Existing interface | Proposed use and limitation |
|---|---|
| [`Finset.HasMulAntidiagonal`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Order/Antidiag/Prod.lean) | Finite binary factorizations, including noncommutative multiplication; investigate before creating a parallel typeclass |
| [`MonoidAlgebra`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/MonoidAlgebra) | Finite-support semantics for arbitrary monoids; compare the redundant polynomial decoder against it |
| [`DiscreteConvolution`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Algebra/InfiniteSum/DiscreteConvolution.lean) | `ringConvolution_eq_sum_mulAntidiagonal` connects sums to finite antidiagonals; summability predicates exist, but no associativity theorem was found in this file |
| [`Algebra/Order/Kleene`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Order/Kleene.lean) and [`Algebra/Order/Quantale`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Order/Quantale.lean) | Reuse for idempotent semantics; Kleene algebra is not the interface for natural-number counting |
| [`Coalgebra/Convolution`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Coalgebra/Convolution.lean) | `WithConv` linear-map convolution supplies a comparison for coalgebraic decomposition |
| [`DayConvolution`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Monoidal/DayConvolution) | Related categorical machinery with explicit TODOs; not an already complete replacement for the word implementation |

## Transport contracts and proposed order of work

`mapCoefficients` already preserves finite convolution. A closure bridge needs
star preservation as well, or a proof from the proper finite construction.
For infinite sums, preserving finite addition does not imply preserving the
chosen summation operation. The support map also needs hypotheses excluding
cancellation and zero divisors if generalized beyond its current domain.

Transport of indices needs its own contract. Finite-support pushforward along a
monoid homomorphism sums colliding coefficients. For unrestricted functions,
its fibers may require infinite sums. Pullback need not preserve convolution:
restrict `δ₁` and `δ₋₁` from `ℤ` to `ℕ`. Their convolution on `ℤ` is nonzero at
zero, while the restricted second factor is zero. A suitable factorization
lifting property can justify particular pullbacks; monoid-homomorphism laws
alone cannot.

| Proposed step | Evidence to require before adoption |
|---|---|
| Proper word star | Finite specification, executable implementation, unfold and uniqueness proofs; ambiguous counting and support examples |
| Finite-decomposition convolution | Reuse antidiagonal API; prove current word operations specialize to it; add natural-number and finite-group cases |
| Finite-support monoid semantics | Decoder into `MonoidAlgebra`, multiplication and normalization preservation; collision example |
| Nullable weighted expressions | Explicit coefficient-star laws, nullable derivative theorem, finite weighted automaton interpretation |
| Category or witness decomposition | Path/interval or shuffle case; proved reassociation preserving multiplicities |
| Infinite or analytic convolution | Named summation/convergence contract and a client needing it; avoid importing these assumptions into finite clients |

A further route combines input monoids with restricted infinite summation.
Baudru et al. define pre-rational monoids by rational fibers of maps from finite
free monoids, and rationally additive semirings by partial countable summation
including geometric sums. Their Theorem 16 proves an automata/expression
equivalence under these assumptions. This can accommodate two-way and
tree-walking behavior. It is not an arbitrary-monoid theorem: `ℤ` fails the
pre-rational condition. Their effectiveness result additionally requires
computable fiber languages and coefficient operations. This is a later option
if such machines become a concrete client.
[Weighted Automata and Expressions over Pre-Rational Monoids](https://drops.dagstuhl.de/storage/00lipics/lipics-vol216-csl2022/LIPIcs.CSL.2022.6/LIPIcs.CSL.2022.6.pdf).

The first adoption decision should compare the caller obligations and proof
reuse of the proper-star and finite-decomposition prototypes against today's
word API. No change to ADR 0004 is needed to conduct that comparison.
