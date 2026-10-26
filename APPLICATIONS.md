# Application translations and what their composition establishes

## Result

This delivery extends the original Lean foundation with implementations and
proofs for all eight supplied source families. The coverage is explicit:
completed first-order and algebraic constructions are implemented as generic
libraries; the incomplete higher-order AD draft is represented by a full
higher-order curve theorem and a complete polynomial derivative-tower fragment.
This is an original formal reconstruction, not a transcription of the papers
or a port of the ConCat GHC plugin.

The main change to the framework is the addition of **relational squares**.
Exact representations still use decoding functions and ordinary commuting
squares. Enclosures, analytic derivatives, and signal stability also need
relations. They share one composition interface, with proved conversions to
witness squares when a literal four-arrow square is desired.

All correctness claims in this document name checked Lean declarations. The
ADRs describe decisions and restrictions; they are not substitutes for proofs.
The source and dependency provenance is in [docs/SOURCES.md](docs/SOURCES.md).
The historical [DESIGN.md](DESIGN.md) is preserved unchanged from
`foundation-v1`; its statements about missing backends and a dependency-free
build refer to that earlier delivery.

## 1. The common contract

An exact representation contains a runtime type, semantic type, and decoder.
A square contains the implementation and specification functions and proves

\[
\operatorname{decode}_B(\operatorname{impl}(r))
=\operatorname{spec}(\operatorname{decode}_A(r)).
\]

For a relation, the corresponding statement is

\[
R_A(r,s)\Longrightarrow R_B(\operatorname{impl}(r),\operatorname{spec}(s)).
\]

`SquareKit/Relations.lean` proves composition, identity and product laws,
function application and currying, and the graph/witness bridges. These
contracts describe different semantic claims:

| Application | Relation or decoder | Essential extra property |
|---|---|---|
| Stack execution | Forget the untouched stack tail | The stronger theorem preserves the entire tail. |
| Matrices | Coordinate interpretation as a linear map | Both coordinate conversion inverses are proved. |
| Incremental computation | Apply a finite change | Updated old output equals output on updated input. |
| Interval analysis | The interval contains the point | Every primitive and source operation preserves enclosure. |
| AD | Value and tangent/covector representation | The tangent is a genuine analytic derivative. |
| Languages | Weighted series, membership, or parse witnesses | Each selected interpretation has its own preserving operations. |
| Timing | Signals agree with values throughout their intervals | Timing is linear and independent of Boolean data. |

The original typed compilers remain unchanged. `SquareKit/FirstOrder.lean`
and `SquareKit/STLCRelations.lean` instantiate them with these contracts. The
latter handles every constructor of the existing full simply typed syntax,
including functions, products, sums, case, let, and captured environments.

### Higher-order runtime functions

The function relation says that related inputs produce related outputs:

\[
R_{A\to B}(F,f)\iff
\forall r,s.\ R_A(r,s)\Longrightarrow R_B(F(r),f(s)).
\]

This avoids assuming a decoder from arbitrary runtime functions to semantic
functions. `STLCRelations.compile_preserves` proves the fundamental theorem
for every source term. `compile_apply_preserves` exports the useful function
application consequence. Sum values must have matching tags.

The ordinary witness construction explicitly stores a semantic value together
with its representation witness. It supplies a correct square, but does not
establish erasure of that semantic data. In contrast, generalized AD stores
its analytic derivative witness only in `Prop`; its runtime contains the
selected derivative representation itself.

## 2. Coverage of the supplied works

| Work | Implemented translation | Principal proof entry points |
|---|---|---|
| *Compiling to Categories* | Original typed compiler plus circuit, matrix, AD, finite-change, and interval interpretations; higher-order relational extension. | `compile_sound`; `MatrixCompiler.compile_correct`; `Incremental.Compiler.compile_update`; `IntervalAnalysis.compile_contains`; `STLCRelations.compile_preserves`. |
| *Generic Functional Parallel Algorithms: Scan and FFT* | Generic monoid scans, product/composition recipes, powers, polynomial evaluation, recursive Cooley–Tukey transforms and exact complex DFT interpretation. | `ScanPlan.correct`; `Shape.scanNestedWith_correct`; `evaluatePolynomial_correct`; `Factor.fft_decode`; `Factor.fourier_correct`. |
| *The Simple Essence of Automatic Differentiation* | Analytically certified differentiable maps, forward seeds, reverse continuations, adjoints, and direct compilation into generalized derivative representations. | `DMap.derivative_eq_fderiv`; `FirstOrder.compile_hasFDerivAt`; `Generalized.compile_reverse_correct`; `Generalized.modes_agree`. |
| *Calculating Compilers Categorically* / *Compiling Gracefully* | Typed stack instructions and their execution; a compiler preserving an arbitrary tail; inspectable bytecode. | `StackMachine.run_append`; `StackMachine.compile_correct`; `compileSquare`. |
| *Generalized Convolution and Efficient Language Recognition* | Weighted series on finite words, semiring laws, sparse polynomials, normalization and coefficient/support homomorphisms. | `Convolution.conv_assoc`; `mapCoefficients`; `supportHom`; `Polynomial.denote_normalize`; `denote_mul`. |
| *Higher-order, Higher-order Automatic Differentiation* | Full source curve logical relation; captured higher-order functions; all-order polynomial jets and a tower compiler with product/composition operations. | `HigherOrder.eval_related`; `compileDual_hasDerivAt`; `Jets.jet_correct`; `jet_leibniz`; `compile_jet_correct`. |
| *Symbolic and Automatic Differentiation of Languages* | Boolean regex derivatives, productive finite trie observations, proof-relevant derivative isomorphisms, total parsing and an independent agreement theorem. | `recognize_correct`; `Machine.lookup_unfold`; `derivativeStarIso`; `Parser.parse_correct`; `recognizers_agree`. |
| *Timely Computation* | Stable signals, setup/hold interval semiring, linear timing maps/matrices, typed circuit compilation, exact adder timing and a reconvergent hazard. | `Digital.square_compose`; `timingMatrixSquare`; `Circuit.compile_matrix_stable`; `Adders.fullAdder_matrix`; `hazard_at_seven_tenths`. |

Namespaces in the table are abbreviated where unambiguous; each library's
module header and ADR give full names and definitions.

## 3. Automatic differentiation: certify the derivative, then change its representation

`Applications.AD.DMap E F` contains a primal function, a continuous linear
derivative at each input, and a `HasFDerivAt` proof. The identity, composition,
product, arithmetic and constant constructors discharge real analytic proof
obligations. The category/cartesian laws use uniqueness of derivatives.

A square that merely forgets the tangent would allow incorrect tangents.
`tangent_correct` and `compile_hasFDerivAt` establish the missing analytic
property against the independent source evaluator.

The forward implementation accepts arbitrary seed maps. Reverse mode uses
continuous linear maps on covectors. Sequential composition reverses order,
and pairing adds the two reverse contributions. The author's errata are
incorporated: `onDot` has an ordinary-function result type for an arbitrary
input function, and the projection/injection and pairing laws use the correct
cartesian/cocartesian variance. See [S3](docs/SOURCES.md#s3-automatic-differentiation).

`Applications.AD.Generalized` compiles directly to a selected `LinearModel`.
The two supplied models are ordinary continuous linear maps and reverse
continuations. The runtime operation returns a primal result and that model's
code. Its correctness field states the existence of a true derivative related
to the code. `modes_agree` compares independently compiled direct and reverse
programs for every source term, covector, and direction.

For the shared nonlinear source

```text
let z = x*y in z*z+x
```

the code proves the directional derivative

\[
(2xy^2+1)\,dx+(2x^2y)\,dy.
\]

The higher-order theorem tracks curves through the full source syntax. It
handles the variation of captured functions as well as arguments. For
`twice (lambda y => x*y+x) x`, the proved derivative is `3*x^2+2*x+1`.
This construction does not posit a normed-space or exponential structure on
all function spaces. Sum curves retain one constructor along the curve.

The all-order library represents a polynomial's entire derivative tower by
one finite polynomial. `jet_correct` identifies every component with analytic
`iteratedDeriv`. `towerMulSquare` implements the binomial convolution of tower
components, justified by `jet_leibniz`. No Taylor-convergence assumption is
needed. Arbitrary lazy smooth-function towers and reverse cotangents at
function types are outside this completed fragment of the incomplete draft.

## 4. Parallel shapes retain algorithm choices

Flattening a shaped container forgets its grouping. Scan correctness relates
the shaped implementation to an independent sequential prefix-and-total
specification. The theorem works over every monoid, including noncommutative
ones; examples scan words so that reordering would be observable.

`ScanPlan` retains product and functor-composition nodes separately. Different
recipes can have isomorphic shapes without being identified as algorithms.
`Scanner.compose` builds a correct nested scanner from any two correct local
scanners. Left powers, right powers and bushes preserve this distinction.

`Scanner.inclusive_correct` bridges the exclusive prefixes plus total to
standard `List.scanl`, preserving ordered monoid multiplication.
`Scanner.inclusive_fusion` interprets all states through a commuting law on
reachable states. The [textbook reconstruction record](docs/research/adwh-scan-bridge.md)
tracks provenance, retained arbitrary-accumulator fusion, and checked composed
plan clients for sums, ordered words and word lengths. Empty and singleton
plans and the source's failure of unrestricted fusion are checked as well.

FFT uses factor trees with leaves of sizes one and two and arbitrary
composition. The recursive implementation performs nested transforms,
transposition and twiddle multiplication. Its proof reindexes the result to
the direct DFT for every supported tree. `ComplexFFT.lean` supplies exact
complex primitive roots and the conventional negative-sign forward transform.
Finite-field executions exercise the same algebra without floating-point error.

The proved four-point result over `ZMod 17`, with root 4, is `[10,7,15,6]`.
The executed eight-point result with root 2 is `[2,8,14,6,13,3,12,1]`.
The development establishes functional correctness; work/span, scheduler,
root-power sharing and floating-point analyses are not formalized here.

## 5. Stack code, matrices, finite updates, and enclosures share a source

The stack instruction type records accumulator and stack effects. Its
operations are labeled primitives and explicit structural instructions;
there is no arbitrary-function instruction hiding a semantic interpreter.
`compile_correct` proves the result for every typed term and every tail. This
completes the first-order stack construction used here; closures, branching
bytecode and a physical instruction encoding are not supplied.

The matrix compiler's homs are actual finite matrices over any commutative
semiring. Coordinate types follow source products. The vocabulary contains
zero, addition and constant scaling, so every accepted term is linear. It
does not label nonzero constants or multiplication of variables as linear.

Finite-change compilation has a distinct contract. For multiplication it uses

\[
\Delta(xy)=x\,\Delta y+\Delta x\,y+\Delta x\,\Delta y.
\]

The final term is essential. `tangent_is_not_a_finite_change` proves a
counterexample to substituting an infinitesimal derivative. `Cache` keeps an
input, output and dependent correctness invariant; `advance_correct` preserves
it. The abstract update interface does not assume a change monoid or establish
an asymptotic speedup, and it does not cache every intermediate node.

Interval operations use exact rational endpoints, including four-corner
multiplication. Their relation is point containment. The full-STLC instance
then proves enclosure through arbitrary source lambdas, application and
captured case branches, provided the input values/functions are related.

The interval result can be imprecise. Compiling fourth power on `[-1,2]`
produces `[-8,16]`, a sound enclosure that includes negative values. Likewise,
pointwise `x + -x` equals zero while interval evaluation on `[-1,1]` gives
`[-2,2]`. Both facts are proved. Equality of point functions does not justify
equality of their interval analyses.

## 6. Convolution and languages preserve the chosen information

Word convolution sums over the finitely many prefix/suffix splits of a word.
The implementation and semiring laws allow arbitrary semiring coefficients,
including noncommutative multiplication. Sparse polynomials permit duplicate
word keys; normalization combines them while preserving denotation.

Coefficient homomorphisms and the natural-weight support homomorphism make
information loss explicit. The language pipeline composes sparse convolution,
normalization, forgetting multiplicity, regex construction, and finite trie
observation. `normalized_product_snapshot` relates the final lookup to the
original nonzero coefficient for every word within the observation depth.

The proof-relevant branch retains parse witnesses as types. It exposes an
important difference from Boolean recognition:

\[
\operatorname{Star}(P)([])\cong\operatorname{List}(P([])),
\]

\[
\operatorname{Star}(P)(a::w)\cong
\operatorname{List}(P([]))\times
\operatorname{Concat}(D_aP,\operatorname{Star}(P))(w).
\]

The second isomorphism retains leading empty parses. `nullableStarIso` and
`derivativeStarIso` include both inverse proofs. The familiar Boolean star
derivative can forget that multiplicity; a witness-preserving translation
cannot silently do so.

The total parser returns a witness or a refutation of every possible witness.
`recognizers_agree` connects it to the independently implemented optimized
Boolean recognizer for all regexes and words. It chooses a successful witness;
it does not enumerate every ambiguous parse. The automatic/state-machine
translation supplies total finite trie observations, not a claim that arbitrary
coinductive source code or unrestricted weighted star has been ported.

## 7. Timing gives a stronger circuit meaning than a truth table

A digital morphism has an analog signal transformation, a Boolean value
function, an interval-linear timing map, and a proof preserving stability at
every enclosed time. Values and timing are structurally independent. The
signal-to-value interpretation is relational because an arbitrary unstable
signal has no single globally valid Boolean meaning.

Timing intervals form a product tropical semiring. Addition intersects bounds;
multiplication adds endpoints. Inverted bounds are retained. They can become
useful bounds after multiplication by a sufficiently wide input interval, so
endpoint multiplication is not a well-defined operation on ordinary time sets
after all empty intervals have been identified. `empty_product_counterexample`
proves that distinction.

`Digital.timingMatrixSquare` reuses `Applications.Linear.Matrix` directly.
`Circuit.compile_matrix_stable` transports the signal theorem to matrix timing
for every source program. The typed circuit syntax remains inspectable, and
`interpret_compile` proves agreement between folding compiled circuit syntax
and compiling directly to another target.

The full adder is a source term with two lets. `compiled_fullAdder` proves
agreement with the factored circuit on analog behavior, Boolean values and
timing. Its calculated matrix is:

| Output | Input `a` | Input `b` | Input `c` |
|---|---|---|---|
| Sum | `[1/4,1/4]` | `[1/2,1/2]` | `[1/2,1/2]` |
| Carry | `[3/5,3/5]` | `[17/20,3/5]` | `[17/20,3/5]` |

With `a=c=true` and `b` falling at zero, the abstract carry stays true but the
modeled circuit carry is false at `7/10`. Both statements are theorems about
the same circuit interpretation. The inverted carry coefficient imposes a
minimum input-stability width of `1/4`, also proved.

This is an exact rational gate-delay model, not measured physical timing.
General gate templates allow signed shifts; named examples use nonnegative
delays. Stateful feedback, causality for arbitrary signed templates, physical
characterization, metastability, RTL export and timing-preserving netlist
optimization are outside the artifact.

## 8. Cross-application proofs

`Examples/ArithmeticPipeline.lean` uses one primitive signature across real
AD and rational stack/incremental/interval interpretations. It proves the
real analytic derivative, stack recomputation versus exact update, and
enclosure of the updated result. The enclosure premise refers to the updated
input, not an old box that may no longer contain it.

`Examples/MatrixStack.lean` synchronizes the independently compiled matrix and
bytecode squares for every linear source term. The joint runtime returns both
results and a proof that they decode identically. Its stronger equality also
preserves the original stack tail.

`Examples/JetScan.lean` proves a coefficient adapter from Mathlib polynomials
to shaped data and correct evaluation for any sufficiently large scan plan.
A total adapter selects a plan with `natDegree+1` slots. The package has the
dependent type:

```lean
structure Prepared (R : Type) where
  plan : ScanPlan
  data : plan.shape.Data R
```

Pasting preparation, differentiation and evaluation squares proves
`source_jet_scan` for every polynomial expression, every derivative order and
every evaluation point. Real-polynomial preparation is noncomputable; the
generic scan evaluator is executable when its scalar operations are. The
default plan is right-associated, while the sufficient-size theorem supports
alternative plans. No parallel speedup follows solely from correctness.

These indexed packages, circuit ports and derivative orders exercise genuine
dependent data. The original `Dependent.lean` split-family model is preserved.
This application extension does not implement a full dependent syntax,
universe/identity-type frontend, or general LCCC compiler theorem.

## 9. Verification and trust boundary

`check.sh` verifies that the complete public entrypoint covers every local Lean
file, rejects admissions and unsafe source constructs, then rechecks all
modules in dependency order. It ends by running `ProofAudit.lean`.

The audit enumerates project-owned declarations using Lean's module metadata,
including private declarations, generated equations, instances and theorem
auxiliaries. It checks every kernel-safe declaration with the dependency engine
underlying `Lean.collectAxioms`, sharing already-visited dependencies. The only
permitted transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Lean also generates unsafe erased runtime declarations during code generation.
They are counted separately, cannot be used by safe proofs, and are not
mathematical proof roots. The audit rejects unsafe declarations with source
ranges, and the source guard independently rejects user-written unsafe code.
The whitelist still applies to anything reached from a mathematical root.

Negative controls confirmed that the audit rejects an admitted private proof,
an arbitrary axiom under an unrelated name, native-decision trust through
`Lean.ofReduceBool`, and a source-written unsafe definition. An ordinary
private proof passes. These checks test the audit itself; they are not included
as accepted source modules.

The delivered [verification.txt](verification.txt) records compiler version,
module checks, executable results, declaration counts and the final audit.
Kernel checking validates the formal statements; the explicit independent
semantics and coverage above explain what those statements establish.

## 10. Design records and history

The [ADR index](docs/adr/README.md) lists ten decisions covering library
boundaries, relations, AD, languages, parallel algorithms, stack machines,
finite changes/enclosure, timing, matrices, and composition/auditing.

Git preserves the initial foundation and each application/integration step.
`foundation-v1` identifies the original delivery. `applications-v2` identifies
this extension. The archive's Git bundle restores the branch and tags with
ordinary `git clone`; see the commands in [README.md](README.md).

## Optimization specifications and interpretation transport

`Applications/Optimization/Basic.lean` accepts ordinary admissible sets and
objectives. `Optimization.minimizers` combines feasibility with Mathlib's
`IsMinOn`; `pareto` separately describes nondominated costs. `value` uses a
complete-lattice infimum. `Attained` and the noncomputable `select` distinguish
existence of a least-cost candidate from its selection. `pullback` and
`pullbackWorkload` are function composition, including explicit workload maps.

`Applications/Optimization/Transport.lean` exposes the extra obligations for
transport. `minimizer_image` proves optimality among interpreted source
candidates. `minimizer_transport` proves global target optimality when every
target candidate has a dominating source lift; exact coverage suffices via
`minimizer_transport_of_surjOn`. Both require monotone cost agreement and the
global theorem also requires admissibility preservation. `minimizer_reflect`
uses an order embedding. `value_transport` uses an infimum-preserving map and
exact coverage. These are sufficient hypotheses, not necessity claims.

`Applications/Optimization/Relations.lean` connects ordinary realization proofs
to `Relational.RelSquare`. `selectionSquare` relates decoded outputs to
set-valued minima by membership; `attainedSelectionSquare` restricts a classical
selector to inputs with attainment evidence. `boundSquare` instead relates a
feasible output to a stated cost bound. Both preserve the problem/workload
index in their output contract. No compiler syntax or executable optimizer is
required.

`Examples/Optimization.lean` checks exact semiring matrix reassociation for
shapes 2×5, 5×20, 20×5. The two plans use 400/550 scalar multiplications and
40/25 intermediate scalar slots, so work and storage choose opposite plans.
The counting models exclude additions, inputs, final output, kernel workspace,
and physical allocation or scheduling costs. The theorem
`matrix_work_transport` consumes ordinary matrix equality and cost proofs.
`matrix_pareto` shows both plans are nondominated but neither is jointly least.
The scope is exactly these two plans, not every matrix algorithm.

Further checked cases include a real positive-ray objective with infimum zero
and no minimizer (`positive_infimum`, `positive_not_attained`), an approximate
realization for each positive tolerance, exact indexed matrix selection,
reflection and complete-lattice value transport, a dominating lift without
surjectivity, and a cheaper target outside the source image.
`semantic_only_not_optimal` exhibits a commuting semantic square whose cost
ranking reverses. These original examples are independent of the textbook snapshot.
The motivating [research report](docs/research/compositional-optimization.md)
records the broader questions and proposed extensions.


`Applications/Optimization/Thinning.lean` reconstructs finite candidate refinement
from preserved ADWH checkpoint 233. Coverage, candidate origin and sublist order
remain distinct; map, extension and fold laws support both order-preserving and
order-changing realizations. Retained minima reach original candidates through
`minimizer_transport`. `NetworkThinning.lean` recovers layered-network generation,
adjacent pruning, failure and source tie behavior. `KnapsackThinning.lean` proves
a new 0/1-knapsack frontier globally optimal over feasible input sublists, using
`OrderDual Nat` for maximization. It permits zero weights and duplicate labels.

`Examples/Thinning.lean` checks incompatible network layers, a feasible network
requiring a non-greedy suffix, order-changing coverage, candidate origin, and
first-cost ties. Knapsack checks empty input and a capacity-5 optimum of value 9.
The composed `knapsackValues` square observes the actual frontier's values while
preserving refinement of all feasible candidate values. The
[reconstruction record](docs/research/adwh-thinning-reconstruction.md) states
provenance, statement review and limits, including the source knapsack capacity
table and global tie equivalence that remain outside this slice.

### Textbook reconstruction clients

The [coverage map](docs/research/adwh-reconstruction-map.md) routes the preserved
textbook to scoped reconstruction records. Each record names independent
semantics, executable realizations, checked public examples and declaration
provenance; it also records source contracts still outside that slice.

| Reconstructed client | Contract and examples |
| --- | --- |
| [Generalized-cost bracketing](docs/research/adwh-bracketing.md) | Recursive, cached and interval-array selection agree, including first ties. |
| [Instrumented execution](docs/research/adwh-resources.md) and [immutable knapsack workload](docs/research/adwh-knapsack-workload.md) | Event reweighting, complete old-row table refinement and exact whole-workload counts. |
| [Static search](docs/research/adwh-static-search.md) and [rational-cost adapter](docs/research/adwh-rational-search.md) | Independent path optimum, lawful queues and finite rational scaling with blocked infinity edges. |
| [Huffman construction](docs/research/adwh-huffman.md) | Duplicate-safe global weighted-path optimum and exact-occurrence queues; distinct tree ties agree on cost. |
| [Binary random-access lists](docs/research/adwh-random-access-lists.md) | Actual cached-tree access, update and borrowing refine canonical lists, with composed query and push/pop consumers. |
| [Symmetric lists and prefixes](docs/research/adwh-symmetric-lists.md) | Actual rebalancing and prefix algorithms refine standard lists, with composed endpoint and prefix-length observations. |
| [Adjacent-run compression](docs/research/adwh-run-compression.md) | Adjacent boundaries, suffix-fold equivalence and injective relabeling. |
| [Kruskal spanning trees](docs/research/adwh-kruskal.md) | Global signed-weight optimum, exact stable source execution and composed tree/cost consumers on the numbered domain. |
| [Nested Kruskal forests](docs/research/adwh-forest-kruskal.md) | Global minimum spanning forests on empty/disconnected graphs, arbitrary-label tree consumers, exact source failures and explicit vertex-order normalization. |
| [Potential accounting](docs/research/adwh-potential-accounting.md) | Shared measured workloads and potential laws, exact binary writes and symmetric-list charge/work consumers. |
| [Random-access costs](docs/research/adwh-random-access-costs.md) | Measured lookup and ordered updates, exact worst-case counts and index-only bound counterexamples. |
| [Random-access end costs](docs/research/adwh-random-access-end-costs.md) | Separate carry/borrow potentials, charged partial draining and mixed-cycle impossibility with composed consumers. |
| [Finite-sentinel Dijkstra](docs/research/adwh-dijkstra-sentinel.md) | Exact raw Int execution, strict-range state refinement, and composed distance/parent/queue observations. |
| [Growing-tree Prim](docs/research/adwh-prim.md) | Exact retained-edge execution, independent signed minimum spanning trees and composed Kruskal cost agreement. |
| [Finite Dijkstra](docs/research/adwh-dijkstra.md) | Exact link-array execution, globally shortest ordered paths, unreachable targets and agreement with the accepted closed search queue. |
| [Ordered binary search](docs/research/adwh-ordered-search.md) | Exact inversion, monotone finite cuts, actual doubling and composed least-threshold rounding. |
| [Connectivity](docs/research/adwh-connectivity.md) | List and weighted-parent histories realize the same finite connectivity, query and cycle-rejection observations. |
| [Stable sorting](docs/research/adwh-stable-sorting.md) | Sorted permutation and equal-key order remain separate contracts. |
| [Bounded segments](docs/research/adwh-bounded-segments.md) | The actual thinning scan selects a global bounded-length segment optimum. |
| [Coin choice](docs/research/adwh-coin-choice.md) | Enumeration, lexical greedy choice and minimum-count choice retain their distinct objectives and ties. |
| [Occurrence-rank selection](docs/research/adwh-rank-selection.md) | Three-way selection, standard sort/index, lower median and monotone value transport agree on rank. |
| [Ordered partitions and paragraph layout](docs/research/adwh-paragraph-layout.md) | Exact generator/pruning orders and global lexicographic layout optimum, with conditional helper agreement. |
| [Edit alignment](docs/research/adwh-edit-alignment.md) | Independent fixed-price global optimum and all-entry cached row refinement, with distinct optimal script ties. |
| [Increasing subsequences](docs/research/adwh-increasing-subsequences.md) | Merged thinning selects a longest strictly increasing sublist while preserving source witness choices. |

`Optimization.FirstMinimum` and `LastMinimum` specify positional tie choices
independently of the shared selector. `argmin_eq_some_iff_firstMinimum` and
`argminLast_eq_some_iff` connect those specifications to execution; bracketing,
segments and coin choice reuse them. `Optimization.observationSquare` retains
the problem index and maps the permitted witness set through any observation.
Segments and subsequences compose it with their selection squares to expose
optimum sums and lengths. Equal optimum values do not identify tied witnesses.

## Finite evaluation and stream progress

`Applications/Progress/` is an experimental deterministic atomic-step model.
`Evaluates` and `Delivers` define finite operational traces independently of
search. Numeric fuel/result/cost certificates have a sound Boolean checker;
exhaustion means unknown. Sequential evaluation adds transition counts and
requires the first postcondition to establish the next termination domain.

Guarded state producers deliver each finite unfolding, with map, zip and
inclusive scan laws. A realization that inserts one silent step per emission
delivers the same values and final underlying state in twice as many steps.
The bound excludes indefinite silent stuttering. Silent loops and a filter
with no matches have no finite output; filtering needs explicit next-match
progress evidence. Filtering the Boolean toggle supplies that evidence through
the checker, while emitting `none` remains a productive alternative.

`Processor` separates operations from `DeliversWithin` and `Causal` laws.
Executable Mealy and finite-drop machines connect finite input lists to stream
observations. Their compositions substitute demand functions, add transition
bounds, and preserve prefix coherence. They reuse `Optimization.membershipRep`
and `Relational.compose` for indexed admissibility and finite observation
squares. Checked examples retain outputs, machine states and transition counts.

These results count model transitions, treating each callback and list operation
as atomic. They do not establish host runtime cost, scheduler fairness, general
termination inference, conversion normalization, or a lazy heap implementation.
The [contract note](docs/progress-contracts.md) records those boundaries and the
relation to the separate recursion compiler work in #109.
