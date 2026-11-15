# Normalized FFT in the two-coordinate unitary model

Issue [#246](https://github.com/VladimirMarko/conaled/issues/246) formalizes
Ailon's entropy lower bound and the separate construction needed to attain it
with the repository's pair-composed FFTs. Every factor tree produces an exact
normalized Fourier program with `N log₂ N / 2` gates and `log₂ N` complete
matching rounds. The two lower bounds compare this construction with every
program admitted by the fixed-register machine.

## Machine and costs

`Applications/Parallel/FFTUnitary.lean` uses exactly `N` complex registers.
A gate applies an arbitrary 2×2 unitary matrix to two distinct coordinates.
Its frame is a bijection between the registers and the selected pair plus its
untouched complement. `Gate.exists_frame` and `Gate.ofPair` show that every
ordered pair of distinct coordinates can be selected. Frames introduce neither
copying nor workspace.

A round contains a list of gates with disjoint coordinate pairs. Competitors
may use partial matchings and idle coordinates. Register permutations are free
steps, while the gate count sums the matching sizes and the round count counts
matching steps. Every sequential two-coordinate program embeds using singleton
rounds. The unitary matrices are exact complex values; these costs make no
claim about implementation time, memory traffic, real multiplications, or
floating-point stability.

The Fourier target uses `exp(-2πik/N)` and the factor `1/sqrt N`. Its external
register order is explicit. A final permutation must be represented in the
program when needed to obtain this target. At size one the transform is the
identity, the empty program is feasible, and no admissible gate exists.

## Entropy lower bound

`FFTEntropy.lean` defines the entropy contribution of squared magnitude `x` as
`Real.negMulLog x / Real.log 2`. Mathlib's zero convention gives contribution
zero at `x=0`. For any nonnegative `a,b`, splitting the total `r=a+b` gives an
entropy between `h(r)` and `h(r)+r`. The total need not be at most one. The proof
uses Mathlib's binary entropy bounds and treats total zero separately.

A unitary matrix has row mass one. A two-coordinate gate preserves each
column's combined mass in the affected rows, whose total is two. Consequently,
`gate_entropy_change` bounds the absolute entropy change by two bits.
Permutations preserve entropy, and `program_entropy_le` telescopes the actual
program semantics to bound final entropy by twice the gate count.

`NormalizedFourier.lean` proves that every Fourier coefficient has squared
magnitude `1/N`. The resulting entropy is `N log₂ N`. For a factor tree,
`factor_gate_lower_bound` compares **every admitted exact program** with the
prerequisite's butterfly count. It does not restrict competitors to factor
trees or assume that their gates are butterflies. Existing natural-valued
amortized upper-bound lemmas in `Applications/Resources/Potential.lean` were
inspected; their contracts do not directly supply this real-valued lower bound.
The telescoping proof therefore stays local.

## Rounds and normalization

`FFTRounds.lean` proves that gates in a matching read their original pair of
inputs. Each output row after one matching depends on at most the union of two
previous row supports. Hence after `r` rounds an output depends on at most
`2^r` inputs. Every normalized Fourier coefficient is nonzero, so
`fourier_round_lower_bound` gives at least `log₂ N` rounds. This is a separate
argument from entropy and from the scalar work/depth model in #245.

`FFTNormalization.lean` supplies the normalized Hadamard gate, multiplicativity
of normalization, and a decoded matrix semantics theorem for the existing
`Factor.fft`. Its Cooley–Tukey coefficient identity reuses the original
`Factor.twiddle_factorization`; the original weak root-power correctness API
is unchanged. Exact complex roots supply the additional unitary specialization.

`FFTLayers.lean` proves that a complete matching absorbs a diagonal input phase
into each existing 2×2 block. Coordinates, completeness, and the gate count are
preserved. Completeness matters: an arbitrary phase on an idle coordinate
cannot be absorbed into a nonexistent gate. `FFTConstruction.lean` handles a
child with zero rounds by proving its size is one and its intervening twiddles
are identity. This covers syntactically composite singleton factors as well as
`.one`. The former may retain free permutations; they still have zero gates
and zero rounds.

`FFTNetwork.lean` lifts gates and matching rounds into independent register
slices and transports phases across leading permutations. `FFTConstruction`
uses these operations in the original factor recursion. Its
`normalizedProgram_correct`, count theorems, and completeness theorem establish
the exact target, costs, and matching structure together.

## Optimization contracts and checked cases

`FFTOptimality.lean` uses `Optimization.minimizers` over all admitted exact
programs. `FFTGlobalOptimality.lean` instantiates these contracts with the
constructed program for every factor shape. Both global minima are attained.
The size-one empty program is the base instance.

The construction is also connected to the measured prerequisite:
`normalizedProgram_compile_decode` equates its output with the normalized
evaluation of `Factor.compile`'s expression outputs, with the reversed output
shape made explicit. `normalizedProgram_gateCount_eq_compile` identifies its
gate count with that circuit's butterfly inventory length. Twiddle phases have
been absorbed into those gates; the scalar arithmetic costs from #245 retain
their separate meaning.

`Examples/FFTUnitaryBounds.lean` checks the size-two lower bounds and the
32-gate/four-round bounds for size 16 presented by right-associated,
left-associated, and balanced factors. `Examples/FFTNetwork.lean` checks the
constructed semantics and costs. `Examples/FFTUnitaryOptimality.lean` consumes
the public global minimizer theorems, including nested singleton factors and a
singleton factor composed with a size-16 factor.

## Source and statement review

Primary source: Nir Ailon, *A Lower Bound for Fourier Transform Computation in a
Linear Model Over 2×2 Unitary Gates Using Matrix Entropy*,
[arXiv:1305.4745v1](https://arxiv.org/abs/1305.4745v1), Theorem 2.1. The
[versioned PDF](https://arxiv.org/pdf/1305.4745v1) and
[TeX source](https://arxiv.org/src/1305.4745v1) were fetched and read. The paper's
sequential gate steps are called layers; our matching rounds require the
separate dependence proof above.
The fetched PDF has SHA-256
`b837aefb22a47ce8eef8dacb7dad7a46919140a2839386112526d8696637aac7`;
the decompressed TeX has SHA-256
`3123a811395bebac00147163f9fcb38b1d2d408733a372a2222d28bf0559e6a1`.
The concentrated-pair entropy display in the TeX proof omits a minus sign. The
formal proof uses the correct interval
`h(r) ≤ h(a)+h(b) ≤ h(r)+r` instead of copying that display.

The archived `scan-fft-optimality-chat.md` motivates the all-factor attainment
question but is not a proof source. Neither the source theorem nor the checked
lower bounds establish unrestricted FFT arithmetic optimality, minimum
real-operation counts, or a bounded-coefficient determinant theorem.

Statement review covers pair distinctness and representability, preservation
of unitary matrix semantics, zero-log behavior, free permutation costs,
nonzero Fourier coefficients, arbitrary competitor coverage, and the
separation of matching rounds from scalar depth. The positive size-one case
rules out vacuous feasibility at the base. The all-factor construction supplies
feasibility and attainment rather than leaving either as an assumed premise.
Focused builds of the construction and public applications passed. Integrated
build, exhaustive proof audit, and independent Standards and Spec acceptance
remain with the enclosing implementation workflow.
