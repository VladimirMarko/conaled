# Structural FFT counts and exact scalar rewrites

The realization preserves the existing `Factor` recipes and their reversed output shape. `runWith_erases` interprets addition and scalar multiplication back into a commutative semiring, with no primitivity requirement. `expressions_decode` then uses the existing root equation and `fft_decode` to reach the independent DFT sum. The scalar realization specializes to the exact complex Fourier root; its `lower_fourier` theorem applies to every factor tree and every input in either rewrite mode.

Structural butterfly sites are expanded two-point kernel invocations. Twiddle sites are the positive-index rectangle at each composition, excluding the kernel's own root multiplication. Their recursive column and row addresses retain occurrence identity. The recurrence is B(st)=|t|B(s)+|s|B(t), Q(st)=|t|Q(s)+|s|Q(t)+(|s|-1)(|t|-1). Singleton and pair Q are both zero. Under a primitive root these positive exponents are nonidentity; a supplied nonprimitive root can erase that distinction without invalidating the semiring correctness theorem.

The subtraction-free invariant is Q+N=B+1. For N=2^k the uniform natural-number formula is Q=(k*N/2+1)-N. Writing `(k*N/2-N)+1` fails at sizes one and two because natural subtraction truncates. Butterfly and twiddle counts are invariant under association; this does not make retained scalar work invariant.

Scalar gates have construction addresses, exact constant syntax and explicit input references. Reachable gates are counted once. Distinct arithmetic sites remain distinct even when their constants denote equal reals; no global algebraic CSE is performed. Wiring, copying, constants and signs are free. Each real addition/subtraction or nontrivial constant multiplication has unit work and latency. Arrival maps retain independently supplied times for both real components. This model does not count Lean exponentiation, allocation, scheduling, or machine time.

A generic constant complex multiplication uses four real products and two sums. Quarter turns use swaps and signs. Exact odd eighth-turns use two sums and two products, with quarter turns supplying the sign variants. The exp/trigonometric lemmas prove these coefficients and connect them to `ComplexFFT.fourierRoot`; the printed decimal constants in Elliott's circuits are not used as exact roots.

The kernel-checked size16 cost examples give: right and left trees have baseline (188,8), rewritten (176,8); the bush has baseline (176,6), rewritten (168,6). All have 32 butterfly and 17 nonidentity-twiddle occurrences. The distinction persists under the same declared cost model, independent of root-power generation.

Elliott's Fig.30 lists additions, subtractions and multiplications separately; its displayed totals also include literals. The arithmetic-only totals are 188 and 176. This exact reconstruction reproduces those arithmetic totals under the stated site/sharing policy; it does not claim identity of every generated floating circuit. See https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf , §4 and Fig.30.

A future scaled-transform candidate must retain an exact diagonal scaling vector, source/output permutations and direction, ordinary DFT observation, and necessary nonzero/invertibility assumptions. Composition must account for compensation, conversion and normalization work and arrival maps. Size alone cannot identify the candidate boundary. Johnson–Frigo's several mutually recursive scaled transforms illustrate why one cheapest unscaled implementation is an insufficient search state; this development does not implement their split-radix algorithm or claim a global optimum. See https://www.fftw.org/~athena/papers/newsplit.pdf , §§II–IV, eqs.(7)–(8), Algorithms2–3.


The code is in [MeasuredFFT](../../Applications/Parallel/MeasuredFFT.lean),
[FFTRoots](../../Applications/Parallel/FFTRoots.lean), and
[FFTScalar](../../Applications/Parallel/FFTScalar.lean). The
[closed cost proofs](../../Examples/FFTScalarCosts.lean) and
[public clients](../../Examples/MeasuredFFT.lean) exercise their interfaces.
The closed cost proofs use kernel reduction, not native evaluation axioms.
Boolean wire equality has a checked `LawfulBEq` bridge; it changes proof
computation cost without changing graph identity or arithmetic accounting.

A local rewrite's isolated block work is separate from the work of a graph
containing that block. The arbitrary-arrival theorems cover local replacement;
the finite size16 retained-gate theorems establish the whole-circuit comparison.
No claim of work monotonicity in every shared context is inferred from isolated
block savings.
