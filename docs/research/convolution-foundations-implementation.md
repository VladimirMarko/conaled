# Finite convolution, sparse monoid semantics and proper closure

This implements the first three capabilities in [#681](https://github.com/VladimirMarko/conaled/issues/681):
finite-decomposition convolution [#682](https://github.com/VladimirMarko/conaled/issues/682),
sparse monoid semantics [#683](https://github.com/VladimirMarko/conaled/issues/683),
and proper weighted word closure [#684](https://github.com/VladimirMarko/conaled/issues/684).
The [research report](generalized-convolution-and-closure.md) records the primary
sources and the separate assumptions needed for further extensions.

## Independent constructions

[Finite.lean](../../Applications/Convolution/Finite.lean) uses Mathlib's
`Finset.HasMulAntidiagonal` to enumerate every multiplication fiber. Associativity
is proved by reindexing the two finite sets of grouped triple factorizations.
Neither index multiplication nor coefficient multiplication must commute.
`Finite.Series` distinguishes convolution multiplication from pointwise
multiplication; its semiring instance and `Finite.mapCoefficients` use these
proved laws. Units use decidable equality on indices. `finiteAntidiagonal`
provides an explicit finite-carrier enumeration without installing an overlapping
global instance. It is not a closure hypothesis.

The executable word enumeration comes from the original `splits` list and its
proved absence of duplicates. `word_convolution` recovers the existing recursive
multiplication; `wordEquiv` bundles the specialization as a semiring equivalence.
The old word API, derivative laws and implementation remain unchanged. The
executable word adapter requires decidable letter equality; classical equality
can be selected for purely mathematical use. The original word implementation
still works without that requirement. No efficiency improvement is claimed for
enumerating a finset instead of using the old structural recursion.

[Sparse.lean](../../Applications/Convolution/Sparse.lean) uses executable lists
of monoid elements and coefficients, allowing duplicate keys and zero entries.
Its mathematical decoder is Mathlib's `MonoidAlgebra`. Multiplication needs a
monoid and semiring; normalization additionally needs decidable index equality.
The decoder is noncomputable, while the list operations themselves are
executable. Finite support permits multiplication even on infinite groups with
infinite full multiplication fibers.

`denote_mul`, `denote_normalize` and `normalizedMulSquare` provide the semantic
contracts. `denote_push` reuses Mathlib's monoid-homomorphism pushforward, which
adds coefficients when keys collide. `word_denote`, `word_mul`,
`word_normalize_eq` and `word_normalize` recover the old word representation and
its multiplication/normalization contracts without converting its lists.
`Finite.monoidAlgebra_mul` connects finite-support and all-function multiplication
when the index monoid supplies finite fibers. A finite polynomial representation
is not closed under star: even a single nonempty word generates infinitely many
supported words.

[Proper.lean](../../Applications/Convolution/Proper.lean) retains arbitrary
semiring coefficients and constrains only the operand by `Proper f`, meaning
`f [] = 0`. `properStar` specifies a coefficient as the sum of powers through the
output-word length. `pow_apply_eq_zero` proves that all higher powers contribute
zero. The separately defined `closureApprox` repeatedly unfolds `1 + f * x`;
`evalProperStar_correct` proves that this executable evaluator realizes the
finite-power specification. There is no asymptotic improvement claim.

Both unfold equations hold for proper operands. `proper_solution_unique` proves
uniqueness of `x = f*x + r`, and `eq_properStar_mul` identifies its solution with
`properStar f * r`. The result of closure has empty coefficient one and need not
be proper. The finite evaluator is defined on all inputs, but its closure and
uniqueness laws require properness. `no_nat_nullable_star` proves that an operand
with empty coefficient one cannot admit even a left-unfold star over natural
numbers.

## Preservation and combined clients

`map_properStar` shows that coefficient semiring homomorphisms preserve the finite
construction. `support_properStar` recovers language star from natural-number
coefficients; it relies on properness and retains the distinction between a
count and its nonzero test. No statement about cardinalities of arbitrary parse
witness types is inferred.

`derivative_properStar` gives the consuming derivative law.
`ClosureMachine.nextTerm` uses the existing weighted-language term and
concatenation machine after the first character. `run_nextTerm` derives its
observation from the existing coalgebra-morphism theorem. It makes no finite-state,
minimization, runtime sharing or full weighted-regex completeness claim. This is
a compositional interpreted client of the library law, not a new source frontend.

[GeneralizedConvolution.lean](../../Examples/GeneralizedConvolution.lean) retains:

- Cauchy coefficient four from the four decompositions of three.
- Finite-group convolution and a proper-at-identity operand whose square returns
  to the identity, separating binary finiteness from finite repeated factorization.
- Sparse multiplication on the infinite group of integers and a pushforward
  collision adding weights three and four.
- Recovery of the original word-polynomial product coefficient ten.
- Matrix coefficients that distinguish the two multiplication orders.
- Ambiguous proper closure with expected count seven, its Boolean support, and
  the same count through the existing compositional machine.
- `combined_unfold`, transporting closure's unfold law to generalized convolution
  through `wordEquiv`, and a coefficient interpretation preserving the combined
  construction.
- Empty and zero cases and the natural-number nullable-star obstruction.

These cases use the public preservation results. Exact numerical expectations
are checked by kernel reduction, without native-evaluation axioms.

## Adoption and remaining work

Adopt the finite-decomposition semiring, sparse monoid decoder and proper word
closure as separate library interfaces. Their combination reuses semiring
homomorphisms, an equivalence and existing squares; it needs no new universal
preservation record or duplicate language-machine proof. Direct library callers
supply the structures their construction uses. Machine clients still select an
initial series/term and its observation; an arbitrary nullable operator needs
additional laws.

There is some adapter cost: word indices use `FreeMonoid`, and executable finset
and normalization adapters need equality decisions. Keeping the original word
API avoids imposing these on old callers. General sparse terms share the old
list representation, so their word specialization needs no runtime conversion.
These checked clients establish reuse, not a general author-productivity result.

[#685](https://github.com/VladimirMarko/conaled/issues/685) retains coefficient-star
selection and nullable closure. [#686](https://github.com/VladimirMarko/conaled/issues/686)
retains category/witness decompositions, including the relational multiplicity
counterexample. The wider milestone in #681 remains open: this implementation
does not settle those two investigations, arbitrary infinite summation, analytic
convergence, or the later FFT and derivative-tower bridges. No shared-interface
mismatch requiring a retrofit under #235 was exposed by these clients.

## Validation scope

The three modules and retained examples are imported by `SquareApplications`.
Formal acceptance uses the repository's isolated candidate build and exhaustive
proof audit, followed by independent Standards and Spec review. Review receipts,
exact candidate identity and command outcomes belong to the task's review record;
the declarations above state the delivered mathematical contracts.
