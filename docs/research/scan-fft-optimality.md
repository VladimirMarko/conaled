# Scan and FFT optimality as clients of optimization

Assessment dated 2026-10-29, against local revision
`a0ec1cf0fe0885cd733bc0c3a20f11f44723742b`. The input was the supplied
[archived ChatGPT discussion](../history/scan-fft-optimality-chat.md). That discussion is
motivation, not a mathematical authority. This note records source checks,
local integration opportunities, and proposed work; it adds no Lean theorems
or runtime measurements.

The recommendation is to formalize selected developments, starting with
measured scan circuits and certified pruning. The discussion supplies concrete
clients for principles already developed in
[compositional optimization](compositional-optimization.md): semantic equality,
resource observations, and optimality over an explicit candidate set are
separate contracts. The new value is the scan timing counterexample, FFT
structural invariants, and lower bounds that can certify selected optima.

## Existing integration

Git history confirms the chronology. Commit `4835113` introduced compositional
scan and recursive FFT on October 10; `dc0e936` introduced optimization
specifications and transport on October 22; `94ce623` and `532cabb` added
thinning and resource observations on October 26. The inclusive-scan bridge
also arrived on October 26 in `0871aa3`. These dates come from
`git log --reverse --format='%h %ad %s' --date=short -- Applications/Parallel Applications/Optimization Applications/Resources`.

[ADR 0005](../adr/0005-parallel.md) deliberately retained algorithm recipes
separately from container shapes and explicitly deferred optimized circuit
counts. The code supports that account:

| Existing component | What can be reused | What remains to connect |
|---|---|---|
| [ScanPlan](../../Applications/Parallel/ScanPlan.lean), `Scanner.product`, `Scanner.compose`, `ScanPlan.correct` | Correctness for all plans over any monoid, including noncommutative ones | Explicit shared circuit construction and work/arrival observations |
| [Scan](../../Applications/Parallel/Scan.lean), `sequential_product`, `scanNestedWith_correct` | The block-combination and scan-of-scans laws | A bundled augmented-scan monoid or naturality API only if a client needs it |
| [InclusiveScan](../../Applications/Parallel/InclusiveScan.lean), `inclusive_correct`, `inclusive_fusion` | Connection to list scans and reachable-state fusion | Cost preservation is a separate obligation |
| [FFT](../../Applications/Parallel/FFT.lean), `fft_correct`, `fft_decode` | Recursive Cooley–Tukey correctness and shape reversal | Gate extraction, sharing, exact count interpretation |
| [ComplexFFT](../../Applications/Parallel/ComplexFFT.lean) | Exact primitive complex Fourier roots | Normalized unitary circuit realization and lower bounds |
| [Optimization.Basic](../../Applications/Optimization/Basic.lean) and [Transport](../../Applications/Optimization/Transport.lean) | `pareto`, `minimizers`, objective pullback, image/global transport | Choose the admissible circuit class and discharge cost and coverage premises |
| [Thinning](../../Applications/Optimization/Thinning.lean) | `Represents`, `pruneFold_refinement`, `minimizer_of_represents` | Prove that the proposed dominance relation survives each plan constructor |
| [Measured](../../Applications/Resources/Measured.lean) and [FoldCompiler](../../Applications/Resources/FoldCompiler.lean) | Value erasure, additive observations, explicit primitive charges | Parallel scheduling and sharing are not provided by additive writer sequencing |

The existing [circuit syntax](../../Applications/Circuits/Syntax.lean) has
Boolean gates, and [timing intervals](../../Applications/Timing/Intervals.lean)
model setup/hold constraints. Inspect and reuse their interpretation patterns,
but neither is already a generic monoid/complex circuit DAG with exact work
and arrival times. The current FFT also computes exact powers for twiddles;
counts for precomputed constants do not describe that execution automatically.

## Which claims survive scrutiny

Elliott's [paper][elliott] derives algorithms from functor composition and
reports optimized circuits. Its section 5 already proposes searching over
isomorphic functor shapes, so shape search continues the original paper. It does not prove that every generated circuit
is Pareto optimal. Its 16-input scan counts are `(32,4)`, `(29,5)`, and
`(26,6)` for right trees, bushes, and left trees; its four-by-four sequential
block scan has `(24,6)`. The transcript proposes additional competitors
`LBin 3 × RBin 3` with `(31,4)` and `RBin 3 ◦ Pair` with `(27,5)`.
These are useful finite acceptance cases for a checked circuit interpretation,
not existing local resource theorems.

The `(31,4)` derivation uses left work 11, right work 12, and 8 adjustments.
The left total arrives at depth 3 although some left prefixes arrive at 4;
the right outputs arrive at 3. Thus all adjustments finish at 4. This explains
why overall depth alone is an insufficient boundary observation. The `(27,5)`
derivation uses 8 pair totals, a 12-operation scan of totals, and 7 prefix
adjustments. Both derivations assume free wiring/copying, identity elimination,
shared block results, and all prefixes including the total.

For generic monoid circuits, the free monoid supplies a faithful correctness
test and elementary bounds `W ≥ n−1`, `D ≥ ceil(log₂ n)` for `n ≥ 1`.
These are bounds for algorithms correct uniformly over monoids, or for a
specified sufficiently nondegenerate interpretation. They cannot be asserted
for every fixed monoid: the singleton monoid admits constant outputs.

[Snir's Theorem 1][snir] proves `W+D ≥ 2n−2` for self-reducible prefix
problems in its stated circuit model. Applying it requires the dependency and
self-reducibility hypotheses; the name “monoid” alone is insufficient.
The four-by-four example attains `24+6=30`, hence minimizes `W+D` and is
Pareto optimal in a matching model. The elementary separate work/depth bounds
do not prove this mixed bound. A Lean proof should start with free-monoid
binary prefix circuits before attempting Snir's broader gate model.

For pair-composed FFTs, the transcript's recurrences give

```text
B(mn) = n B(m) + m B(n),                       B(2) = 1
Q(mn) = n Q(m) + m Q(n) + (m−1)(n−1),         Q(2) = 0
B(2^k) = k 2^k / 2
Q(2^k) = k 2^k / 2 − 2^k + 1.
```

These are structural derivations for two-point butterflies and nonidentity
twiddle occurrences under exact primitive roots. They express association
invariance, not minimum real arithmetic cost or costs after arbitrary common
subexpression elimination. The later [checked FFT development](fft-structural-costs.md) corrects the
natural-number form to `Q = B + 1 − N`: the displayed left-associated
subtraction also fails at size two, not only at size one. The local semiring FFT theorem needs only
`ω^N=1`; nonidentity-twiddle and unitary claims need stronger assumptions.

[Ailon's Theorem 2.1][ailon] gives the exact lower bound
`(N/2) log₂ N` for the normalized Fourier matrix in a model of `N` complex
registers updated by two-coordinate unitary gates. The matrix entropy starts
at zero, ends at `N log₂ N`, and changes by at most 2 per gate. Free
permutations preserve entropy. Extending the bound to free wiring is therefore
a deduction from the proof. Connecting every local factor tree to a network
attaining it still requires normalization, phase absorption, register discipline,
and output-permutation proofs. The transcript's connection is plausible and
worth proving; it is not already a theorem about `Factor.fft`.

Do not conflate that result with real-operation minimality. The 16-point FFT
arithmetic totals in Elliott's tables are 188 for trees and 176 for the bush,
with depths 8 and 6; literal nodes are excluded from those totals. The exact
identity, with `c = 1/√2`,

```text
(a + i b) exp(−iπ/4) = c(a+b) + i c(b−a)
```

uses two real multiplications instead of four. Counting sign variants and
free sign/wiring conventions consistently is necessary before claiming the
transcript's improved bush count `(168,6)`. It is a proposed checked example,
not a measurement of the current Lean implementation.
[Johnson and Frigo][split] independently establish the usefulness of scaled
subtransforms and cheaper effective twiddles. A search state retaining only
transform size and one cheapest unscaled implementation omits that possibility.

The transcript's bounded-coefficient determinant argument concerns the
unnormalized DFT, whereas the unitary argument concerns the normalized DFT.
The determinant proof cannot yield the same bound for a unitary determinant
of modulus one. Its lower bound follows in the explicitly restricted model
`u = αv + βw`, `|α|,|β| ≤ 1`: each added form grows the maximum available
minor magnitude by at most 2, and `|det F_N| = N^(N/2)`. This mathematical
argument does not establish an unrestricted arithmetic lower bound.

Depth also requires a declared constant policy. With twiddles available,
bounded fan-in gives a logarithmic lower bound and the recursive FFT gives
logarithmic depth. Charging staged twiddle generation is another model. The
transcript correctly solves `D_j = 2D_(j−1) + 2^j + O(1)` as
`O(j 2^j)`, or `O(log N log log N)` for bushes of size `N=2^(2^j)`.
No lower bound on inherent Fourier data depth follows from that staged upper
bound. Neither model establishes floating-point stability or wall-clock speed.

## Proposed formal development

1. **Measured scan realization.** Interpret existing plans into shared acyclic
   circuits, prove erasure to the existing scanner semantics, and state which
   identity simplifications and sharing transformations the count observes.
   Count each retained gate once. Preserve all output arrival information,
   including the total. Prefer an input-arrival-to-output-arrival map over
   times measured only with simultaneous inputs: composition can supply
   nonuniform arrivals. A pointwise comparison of such maps, plus work, is
   a candidate dominance relation for a restricted composition language.
2. **Certified finite search.** Use existing `Represents` and
   `pruneFold_refinement` after proving extension monotonicity. A fixed leaf
   count alone does not make `ScanPlan` syntax finite, since empty and unary
   wrappers can proliferate; bound syntax or enumerate canonical plans and
   prove the intended coverage. State optimum among enumerated plans, among
   a complete bounded grammar, and among all circuits as different results.
   Existing `thinBy` proves coverage and sublist origin, not a complete Pareto
   antichain. Shared-intermediate availability must enter the state if later
   rewrites can exploit it.
3. **Scan lower bounds and examples.** Check the three 16-input comparisons,
   noncommutative word semantics, empty/singleton conventions, and the early-total
   case. Prove elementary free-monoid bounds, then the mixed bound needed to
   certify `(24,6)`. Expose the result through existing `minimizers`/`pareto`.
   A bounded search alone cannot certify global optimality.
4. **FFT counts and local rewrites.** Prove the butterfly/twiddle recurrences
   over existing `Factor`, add exact complex scalar rewrite correctness, and
   connect counts to an explicit circuit interpretation. Check different
   associations at size 16. Represent scaling and permutations in candidate
   boundary contracts if exploring scaled variants; do not assume they are
   interchangeable at zero conversion cost.
5. **Separate Fourier lower-bound development.** Build the normalized unitary
   gate semantics and prove entropy progress, then show compiled networks attain
   the bound. The real-valued entropy argument does not directly reuse
   [Resources.Potential](../../Applications/Resources/Potential.lean), whose
   current theorems concern natural-valued upper-bound accounting. Extract a
   shared ordered telescoping lemma only if both clients justify it. Defer
   unrestricted FFT optimality and a full modified split-radix port.

This order first delivers a reusable connection between existing components,
then certifies stronger claims with independent lower bounds. It respects
ADR 0005's separation of recipes and shapes, preserves its weaker semantic
hypotheses, and adds resource contracts in separate modules. Future Lean work
needs example-driven statement review, integrated build/proof audit, and
independent review. This assessment makes no change to the library's current guarantees.

## Measured scan implementation (#242)

The assessment above describes the initial checkout. The subsequent
[measured scan module](../../Applications/Parallel/MeasuredScan.lean) now
implements the first step. `ScanPlan.runWith` interprets the existing recipes
using only an identity and a binary operation. Its naturality theorem connects
circuit evaluation to the existing scanner and sequential specification for
monoids in every universe, without assuming commutativity.

`Wire` names nodes by their complete expression structure. Equal names denote
one shared node. `SharedCircuit` retains the union of binary nodes reachable
from its output ports and charges each once. Input and identity nodes and
wiring/copying are free; dead gates are absent. Identity operands are bypassed
before constructing a binary node, with proved semantic preservation and
nonincreasing work and arrival time. The strict rank decrease along dependency
edges proves acyclicity. This representation allows structural common-expression
sharing across outputs and is not a model of Lean evaluation costs.

Timing records identity separately from an ordinary value arriving at zero.
`circuit_timing` derives every output arrival, including the total, through
the same plan fold for arbitrary input arrival times. The product and composition
equations reuse child results and combine binary inputs by maximum plus one.
They do not add the durations of independent children.

The [checked examples](../../Examples/MeasuredScan.lean) establish all six
sixteen-input counts above, the mixed product's early total and eight additional
gates, ordered-word semantics, and empty, singleton and nonuniform-arrival cases.
`canonical_correct` ties the circuits to the independent sequential specification;
`outputs_normal` establishes identity elimination for all compiled plans.

Optimality and certified pruning remain separate obligations. Because this
model shares structurally identical nodes, the work of a surrounding circuit
is a union cardinality. Comparing scalar work and output arrival maps alone
does not establish monotonicity of work in arbitrary sharing contexts. A
pruning client must prove its contextual preservation property for its declared
composition language. No theorem here identifies this structural representation
with every possible externally named DAG or asserts global circuit optimality.

## Bounded scan search (#243)

[ScanSearch](../../Applications/Parallel/ScanSearch.lean) implements an
executable search over a declared finite production grammar. A caller supplies
finite seed recipes, finite one-hole frames and a frame-count budget. Frames
cover left and right product placement and outer and inner composition
placement, each with a fixed sibling. `Production` and `Grammar` describe the
allowed derivations independently of the enumerator; `enumeration_iff` proves
soundness and completeness. The budget bounds syntax generation even when
identity wrappers preserve the input size. This is not enumeration of all
scan plans of a given size or all plans below a syntax-height bound.

Each candidate carries its remaining budget. `contexts` enumerates every
supported continuation up to that budget, including the empty continuation.
For each continuation, the profile compares the actual shared-node work and
the ordered output dependency paths. A path records an input port (or the
identity constant) and its delay. The decidable signature comparison implies
arrival comparison for every natural-valued input-arrival assignment; it does
not sample only simultaneous arrivals. Matching output ports also proves equal
input arity. `dominates_context` exposes these guarantees for ordinary circuit
work and arrival observations.

`extend_context` and `extend_covers` prove that applying any catalog frame
consumes one unit of budget and preserves every required future comparison.
Thus the profile accounts for sharing by measuring the completed circuits,
without assuming that child gate counts add. `search_represents` instantiates
`pruneFold_refinement`, retaining both origin and coverage through generation
and pruning. It prunes seeds, intermediate stages and final candidates.
`selected_work`, `selected_deadline` and `selected_weighted` use
`minimizer_of_represents`; `pareto_of_search` separately transports Pareto
membership. Adjacent thinning does not promise a complete antichain. The
selector chooses the first occurrence in the retained list on scalar ties,
which need not be the first original occurrence after pruning.

The [checked applications](../../Examples/ScanSearch.lean) use the six
sixteen-input recipes as an explicit catalog. They select work 24 without a
deadline, work 31 under depth 4, and different plans under weights `(1,1)` and
`(1,10)`. These are optima relative to that six-plan catalog. The universal
per-output arrival comparison conservatively retains all six distinct timing
profiles; scalar selection then chooses the requested optimum. The search
makes no efficiency claim: profiling enumerates future contexts and expands
input dependency paths, and its computational cost is distinct from the
circuit work being minimized.

The `Workload` specialization compares actual work and maximum arrival for a
fixed caller-supplied input-arrival map in every supported continuation. The
map may be nonuniform and also assigns arrivals to inputs introduced by frames.
It shares the proved context-reindexing and generation machinery with the
universal profile. Since all permitted continuations are measured explicitly,
this specialization can safely discard alternatives even when their individual
output timings cross. It prunes the sixteen-input catalog, certifies the same
three objective selections, and replaces the 32-gate right tree by the 31-gate
mixed plan before appending another leaf. Its guarantee applies to the declared
arrival map and context budget; the stronger universal profile specializes to
it through `Workload.of_universal`.

Two counterexamples are checked against the measured circuits. Eight-input
plans with equal `(11,4)` summaries have different total arrival times; coarse
tie pruning loses a depth-4 nine-input completion. The universal profile retains
both and selects the feasible completion through the public minimum theorem.
The declared simultaneous-arrival workload profile instead removes the inferior
completion before extension, with a checked preservation proof.
A three-input example shows that comparison at simultaneous input arrivals
fails when the first input arrives at time 2. Positive replacement cases remove
syntax-distinct identity wrappers before generation, prove safety for arbitrary
input arrivals, and cover all four frame placements with two nested extensions.
These tests establish useful conservative pruning, not completeness of the
signature comparison or global circuit optimality.

[elliott]: https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf
[snir]: https://snir.cs.illinois.edu/listed/J16.pdf
[ailon]: https://arxiv.org/abs/1305.4745
[split]: https://www.fftw.org/~athena/papers/newsplit.pdf


## FFT structural costs and local rewrites (#245)

The [FFT implementation record](fft-structural-costs.md) connects the existing
recipes to exact expression and scalar circuit interpretations. It proves the
structural recurrences, corrected natural closed forms and association
invariance, while preserving the semiring theorem's weak root hypothesis.
Exact root identities justify local scalar rewrites. Under the declared
precomputed-constant, free-sign and explicit-site-sharing model, the size16
bush changes from work/depth `(176,6)` to `(168,6)`; the trees change from
`(188,8)` to `(176,8)`. These are retained arithmetic gates and unit arithmetic
depths, not wall-clock measurements or unrestricted optimality claims.
