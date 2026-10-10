# ADR 0005: Shape-directed scan and Fourier transforms

- Status: Accepted
- Date: 2026-10-10
- Scope: `Applications/Parallel/`
- Source: Conal Elliott, *Generic Functional Parallel Algorithms: Scan and FFT*
  (ICFP 2017), §§2–4.
- Inspected manuscript: [`generic-parallel-functional.lhs` at
  `9a94c8343ede7f96b3b05a47d0e839bd585333eb`](https://github.com/conal/generic-parallel-functional/blob/9a94c8343ede7f96b3b05a47d0e839bd585333eb/generic-parallel-functional.lhs).
- Rendered reference: [author-hosted PDF](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf).

## Context

The important contribution to preserve is composition of algorithms from
composition of container functors.  Replacing the manuscript by a list scan,
one fixed FFT butterfly, or an FFT whose implementation evaluates the direct
Fourier sum would fail to test that contribution.

The runtime representation is a nested product; its denotation is an ordered
sequence or an ordinary finite-indexed vector.  The representation tells us
which subcomputations can be built independently.  A commuting square relates
the result to a specification that does not use the implementation recipe.

## Decisions

### 1. Separate container shape from algorithm recipe

`Shape` contains empty structures, singleton structures, and products.
`Shape.subst outer inner` substitutes an inner structure at every outer leaf.
`Shape.join` and `Shape.split` give an explicitly proved representation change
between this product shape and the nested carrier
`outer.Data (inner.Data A)`.  Flattening forgets grouping but preserves order.

`ScanPlan` separately records product and composition nodes.  This distinction
is essential: expanding the product shape of two isomorphic constructions
can erase the algorithmic distinction between left-associated and
right-associated functor composition.  Plans preserve the choice and compile
recursively to `Scanner` values containing both the implementation and its
correctness proof.  `rightPow`, `leftPow`, and `bush` therefore remain different
recipes.  `Scanner.choice` and `Scanner.void` cover the dynamic sum and void
building blocks without pretending that a dynamic sum is a fixed-size array.

### 2. Use an independent sequential specification for scan

`sequential seed xs` is an ordinary left-to-right accumulator traversal that
returns exclusive prefixes and the final accumulator.  `sequential_total`
identifies its final component with `List.foldl`.

Product scan computes its two scans independently, retains the left prefixes,
left-multiplies every right prefix by the left total, and multiplies the two
totals.  The proof uses `sequential_product`, which is derived from the
accumulator specification and associativity.

Composition is Elliott's scan-of-scans construction: compute each inner scan,
scan the outer collection of inner totals, then adjust each inner prefix
collection by the corresponding outer prefix.  `scanNestedWith_correct`
accepts the two local correctness proofs and constructs the composite proof;
it does not assume the correctness of the composite algorithm.  `Scanner.compose`
also pastes the representation changes into this construction.

All scan proofs require a monoid only.  No commutativity is assumed, so the
proof fixes the direction of every adjustment and applies to ordered words
and endomorphisms as well as sums and products.

### 3. Keep Fourier factorization explicit and change the output shape

`Factor` has scalar kernels of sizes one and two and arbitrary composition
nodes.  `Factor.reverse` reverses the composition order recursively, as
Elliott's `FFO` associated functor does.  Data is materialized as nested finite
products through `tabulate`; transposition and indexing have proved laws.

At a composition node, the implementation transposes the input, performs the
first family of recursive transforms, multiplies by twiddle factors, performs
the second family, and transposes the output.  Larger nodes never call the
direct DFT specification.  The two-point kernel is
`(a + b, a + ω * b)`, with `two_butterfly` proving that the primitive root `-1`
gives the familiar `(a + b, a - b)`.

`twiddle_factorization` proves the Cooley–Tukey exponent calculation for
arbitrary natural numbers `m`, `n`, and indices, under `ω^(m*n) = 1`.
`fft_correct` then proves the complete recursive algorithm correct for every
factor tree.  `indexEquiv` proves a bijection with `Fin size`, including its
rank equation; `dft_eq_direct` converts the structured sum to the conventional
finite-indexed DFT.  `fft_decode` and `fftSquare` state the resulting commuting
square with that conventional denotation.

The executable factor vocabulary has only one- and two-point leaves, so all
its sizes are powers of two, with arbitrary association and bush structure.
The general factorization lemma is broader than this executable vocabulary.
No mixed-radix base kernels have been silently assumed.

### 4. Separate algebraic factorization from the choice of Fourier root

The factorization theorem works in any commutative semiring and needs only
`ω ^ size = 1`.  Such a root need not be primitive; a nonprimitive root still
has a well-defined weighted sum, though it is not an invertible Fourier
transform.  This weaker hypothesis is appropriate for the algebraic law.

`ComplexFFT.lean` supplies the usual exact primitive complex root
`exp (-(2 * π * I / size))`, proves its primitivity using Mathlib's theorem,
and instantiates the square.  The negative sign agrees with the forward DFT
convention used in the manuscript.  This makes the relationship to the
ordinary Fourier transform explicit, rather than substituting a
Walsh–Hadamard transform.

### 5. Translate the scan-derived applications as well

`sequential_replicate` proves that scanning a repeated element gives its
successive powers.  `Scanner.powers_correct` transports this through any
certified scan plan.  `evaluatePolynomial` forms powers by that scanner and
then takes a dot product with the coefficients; `evaluatePolynomial_correct`
proves equality with the ordinary coefficient-order polynomial sum.

## Alternatives considered

- **A single list implementation with a correctness wrapper.** Rejected
  because it would not preserve shape-directed composition or distinguish
  the algorithm families in the paper.
- **Only a four-point FFT example.** Rejected because it would not establish
  closure of the translation under further composition.
- **Assume DFT correctness in a kernel interface.** Rejected as the main
  theorem: the factorization and complete recursive algorithm are proved in
  code from semiring laws and the root equation.  Only the elementary
  one/two-point kernels are leaves.
- **Use ordinary function spaces as the runtime arrays.** The semantic
  interface is a function on `Fin`; the runtime is a materialized nested
  product.  This keeps the representation and the algorithmic nesting visible.
- **Use floating-point complex numbers.** Deferred.  Exact commuting squares
  do not prove numerical stability or a rounding-error bound.  A numerical
  implementation needs an error relation and a separate proof.
- **Copy the manuscript's work/depth claims directly.** Rejected.  Its
  optimized circuit counts include constant elimination and common
  subexpression elimination; neither transformation is implemented here.

## Consequences and limits

The applications use ordinary `Squares.Square` values, including shape-changing
FFT output representations, so further certified preprocessing/postprocessing
can be pasted with the existing square combinators.  The local scan-composition
theorem is reusable with any correctly specified inner and outer scanner,
rather than only the supplied tree implementation.

This development proves functional correctness, array bounds/index coverage,
shape changes, and the algebraic decomposition.  It does not prove a parallel
execution scheduler, a work/span semantics, an asymptotic runtime bound,
floating-point error bounds, inverse FFT normalization, Verilog generation,
or Elliott's circuit optimization counts.  In particular, exponentiation in
the twiddle implementation is exact scalar exponentiation; the manuscript's
optimized sharing of root powers is not claimed.  The primary tests of
generality are the theorems quantified over all scan plans, all monoids,
all factor trees, and all inputs, rather than just the executable examples.

## Proof entry points

| Concern | Checked declaration |
|---|---|
| Flattening commutes with map/zip | `Shape.flatten_map`, `Shape.flatten_zipWith` |
| Functor-composition representation | `Shape.flatten_join`, `Shape.flatten_split` |
| Product scan | `Shape.scan_correct`, `Scanner.product` |
| General composition from local proofs | `Shape.scanNestedWith_correct`, `Scanner.compose` |
| Every scan recipe | `ScanPlan.correct` |
| Dynamic choice | `Scanner.choice` |
| Powers and polynomial evaluation | `Scanner.powers_correct`, `evaluatePolynomial_correct` |
| Exact indexing | `Factor.indexEquiv_val`, `Factor.rank_lt` |
| Transpose involution | `Factor.transpose_transpose` |
| Cooley–Tukey calculation | `Factor.twiddle_factorization` |
| Every recursive FFT | `Factor.fft_correct`, `Factor.fft_decode` |
| Ordinary complex transform | `Factor.fourierRoot_primitive`, `Factor.fourier_correct` |

All mathematical obligations stated above are supplied as Lean proofs in the
listed modules.  The runtime and performance limits are deliberate scope
boundaries, not unproved axioms added to the formal development.
