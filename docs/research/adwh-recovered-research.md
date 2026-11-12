# Research recovered from the external ADWH continuation

This note preserves design reasoning from the abandoned continuation through
checkpoint 182. It is a research handoff, not approval of the proposed Lean APIs
or a claim that the remaining source statements have been ported. The
[handoff](adwh-recovered-handoff.md) records ticket disposition, provenance and
coverage limits. GitHub #149 owns the remaining work.

The external drafts were written against older conaled revisions. The owner
comparison below uses `1e7bee1e979eeea3fe90bca4504de301426ce073`. Recheck current
interfaces before implementation. In particular, an old declaration name or a
suggested filename does not establish a missing abstraction.

## Preserve observations before choosing interfaces

The source separates value, ordered occurrences, legal witnesses, optimum
objectives, modeled work, consumer demand, productivity and native performance.
For each port, identify the observation and its domain before deciding that an
existing theorem replaces it. Membership equality loses enumeration order and
multiplicity. A value projection loses cost and intermediate state. A scalar
sum loses the ordered trace and its grouping by operation. Equality on completed
finite lists loses behavior at unknown ends and infinite inputs.

Do not add equality, canonicality, transitivity, commutativity, positivity or
nonempty-input assumptions merely to simplify a proof. Where an assumption is
necessary, retain the counterexample that distinguishes the restricted result.
Computational witnesses require a data-preserving contract; a proposition about
their existence or erased observations alone does not supply that contract.
This is a future audit criterion, not a finding that the ADWH port has the
witness-erasure defect reported in the separate Felix work.

Existing `Resources.run` supports ordered additive observations. Its append law
uses an additive monoid, not commutativity. `Resources.Potential` retains actual
intermediate states and both initial and final potentials. From
`work + Φ(final) ≤ Φ(initial) + budget`, dropping the initial term requires an
additional premise. The existing stored-potential counterexample is worth
retaining in clients, rather than recreating a second accounting framework.

## List bounds and uniform concatenation

Recovered sources: `BestWorst.lean`, `UniformConcatenation.lean`; draft
`chapter02-list-cost-spec-draft.md`.

Reuse the actual executors in `Resources.ListExecution`, `ListAppend` and
`ListFusion`, with the growth bridge in `Resources.Growth`. The research proposes
a theorem layer over these operations, not replacement list implementations.
Keep exact finite equations before asymptotic conclusions. Distinguish a bound
for every input of a length from best/worst witnesses attaining it. Preserve
empty input, failed-test charges, and parameters equal to zero.

Concatenation cost depends on association, outer block count and payload lengths.
A supplied finite input is different from the portion demanded by a consumer.
An `Option.none` result after finite exhaustion is different from semantic
bottom. A composed last-passing-element observation should use the actual
producer and consumer, charging both under their declared models.

## Demand, delayed lists and head of concatenation

Recovered sources: `CompositionDemand`, `ContextLists`, `ContextConcatenation`;
drafts `chapter02-demand-spec-draft.md`,
`chapter02-context-lists-spec-draft-r1.md`,
`chapter02-concat-head-spec-draft.md`.

Eager composition charges the actual intermediate size. Shared demand needs an
explicit cell/cache state and an observer that records requests in order. A
function returning a measured result is a delayed computation, not evidence of
memoization. Repeating its observation repeats its declared work unless a cache
transition proves otherwise.

For prefixes, suffixes and insertion positions, distinguish constructing the
outer list of delayed payloads from forcing those payloads. Preserve arbitrary
callbacks and repeated occurrences. Counting outer cells must not force labels;
complete observation must charge the callback and inner-spine traversal.
Difference-list equality must quantify over arbitrary appended tails.

Head consumption of right-associated concatenation can stop at the first
nonempty block. Left-associated concatenation can retain deferred append frames
and consume their history without first materializing all payloads. The finite
`Option` fallback law does not justify its extension to partial lists. The
semantic proof must use the existing partial-spine/ideal selector and state the
negative case where an unknown end prevents fallback. Keep an open outer
producer and infinite inner stream among the discriminating cases.

Reuse `CollapseDemand`, `CollapseMaterialization`, `PartialSpine`, and Progress
observations where their contracts fit. Those owners establish useful parts;
the recovered drafts' combined demand/cost correspondences remain obligations.
Finite value fusion alone does not discharge them.

## Prune and trim

Recovered source: `Prune.lean`; draft `chapter02-prune-spec-draft.md`.

This list-predicate trim differs from the element-predicate operation already
in `Applications.Sequences.SuffixTrim`. For arbitrary `p : List α → Bool`, accept
an empty list independently of `p []`. On nonempty input, return it if accepted;
otherwise repeatedly remove its last element. Its independent specification is
the longest acceptable prefix of that input, without a monotonicity assumption.

The right fold that trims `x :: old` at every step has a recursive specification
for every predicate. Its equality to one trim of the original input requires
tail closure: acceptance of `x :: xs` implies acceptance of `xs` or its emptiness.
Without that premise, let `p` accept exactly `[1,2]`: direct trim retains `[1,2]`,
but the right fold discards `[2]` and then `[1]`, returning `[]`.

For a decidable relation, `List.Pairwise` supplies the required tail closure.
Do not replace it with adjacent comparisons or require transitivity. With the
relation `≠`, `[1,2,1]` passes adjacent comparisons but fails pairwise comparison.

The draft proposes an explicit natural guard price `g`. Empty trim costs `g`;
a successful nonempty call of length `n` costs `n+g`; a failed one adds `2*n+g`
to the recursive cost. For final length `m`, its target identity is
`work + m² + g*m = n*(n+1) + g*(n+1)`. This is a proposed source-price theorem,
not a physical bound on evaluating arbitrary predicates. Whole prune has empty
cost zero, even when an empty direct trim costs one. Its right-fold order must
agree with a workload over reversed commands in the entire measured pair.
That semantic bridge does not charge an actual reversal that the fold never
executes. Value equality of prune and trim does not imply equal costs.

Current disposition: #470–#472 deliver the selected whole-list trim, folded
prune and arbitrary guard-price contracts, with native budget/potential reuse.
See [whole-list trim](whole-list-trim.md), [folded prune](folded-prune.md) and
[priced prune](priced-prune.md). The research distinctions above remain relevant.

## Dynamic front arrays: literal and eager resizing

Recovered sources: `DynamicArray`, `DynamicArrayEager`; latest literal/eager array drafts
and their independent design challenges.

Use a common storage/event owner and distinct insertion policies. Existing
fixed-capacity byte-buffer refinement (#253), vector updates, and measured store
operations supply related mechanisms; none alone proves dynamic resizing.
Inspect them before introducing new infrastructure.

The standalone copy theorem must preserve an arbitrary surrounding prefix and
suffix, not just prove copying into a freshly allocated array. A proposed small
implementation runs indexed copy commands through `Resources.run`. Avoid
narrowing the source universe or imposing distinct-index/in-bounds assumptions
on a raw total executor merely because a simultaneous-batch specification needs
them.

Retain ordered allocation, copy and write events. The pricing theorem must cover
every original list price satisfying empty/append laws, not only work and
allocation tariffs. Native free additive observations and `reweight_run` provide
a route to that generality. Per-insertion bills are another observation of the
same transitions; grouping cannot be recovered by a homomorphism from an
already flattened event trace.

Separate raw-state equations from layout-dependent semantics. Positive free
space is required for some spare-space and balance results. Allocation of zero
slots still records one growth event. Keep arbitrary initial states and both
boundary potentials in amortized statements.

The external source-only review unfolded these discriminating cases from an
empty array. They are future Lean fixtures, not newly checked results:

| Insertions | Policy | Work | Allocated slots | Growths | Capacity | Free |
|---|---|---:|---:|---:|---:|---:|
| `[1,2,3]` | Eager | 4 | 6 | 2 | 4 | 1 |
| `[1,2,3]` | Literal | 6 | 6 | 2 | 4 | 1 |
| `[1,2,3,4]` | Eager | 8 | 14 | 3 | 8 | 4 |
| `[1,2,3,4]` | Literal | 7 | 6 | 2 | 4 | 0 |

Neither policy is uniformly cheaper. A valid full singleton with zero free
space also distinguishes layout preservation from a positive-spare guarantee.
Keep zero-capacity, malformed raw cursor, non-power capacity, empty command
sequence and arbitrary price cases.

## Digit search and the finite average correction

Recovered source: `DigitSearch.lean`; draft `chapter02-digit-spec-draft-r1.md`.

The proposed first-hit executor returns `Option Nat` and charges one unit for
each inspected element, with zero extra charge at empty exhaustion. Its result
must agree with `findIdx?`, retaining the first position among all occurrences.
A hit at index `i` costs `i+1`; failure costs the input length. The signed `-1`
sentinel belongs only at the presentation boundary. No equality instance on
arbitrary element types is required.

For decimal words of length `n`, success means a digit at least five. Preserve
the source's ordered population, not just its cardinality. The proposed native
`List.pi` decoding needs a literal successor-enumeration theorem. Direct use of
`List.sections` changes enumeration order: its length-two prefix is `[0,0]`,
`[1,0]`, whereas the source begins `[0,0]`, `[0,1]`.

Average the actual inspected cost over `Fin n → Fin 10`. At `n=0` the sample
space has one empty word, not zero words. The source target is
`E n = 2 - 2 / 2^n`, with rational arithmetic. At length two, 50 words cost one
and 50 cost two; the latter split into 25 last-position hits and 25 failures.
The mean is `3/2`. Treating the last cost event as an uncensored geometric event
loses failures. The weighted sum `Σ (k+1)/2^(k+1)` is a different quantity:
at length one it is `1/2`, while the actual mean is one.

Reuse the integrated finite-sum and convergence results where their index ranges
match. Preserve the zero exponent in survival sums, denominator positivity at
zero, and strict finite error bounds. Population construction is not charged
as part of searching one input. These are finite-uniform claims, not claims for
an arbitrary input distribution.

Current disposition: #478 delivers the selected first-hit execution, ordered
population and corrected finite average. See [digit search](digit-search.md).
Printed-book completeness and licensing remain #149.

## Counter geometry and output

Recovered sources: `CounterGeometric`, `CounterOutput`; latest counter draft,
independent challenge, and `chapter02-reuse-author-candidate-r2.md`.

The existing `Resources.BinaryCounter`, workload and potential owners already
supply increment, finite prefixes, representation bridges, measured execution
and potential bounds. The execution and counter reuse research identifies correspondence obligations;
it does not justify copying those APIs. Keep all Boolean representations where
the source allows them. Canonicality is a separate conditional invariant.
An encountered malformed integer digit differs from an untouched malformed
suffix; zero/one observed prefixes need not increment their seed.

The independent geometric account is worth preserving even though a potential
bound exists. For zero-start transition cost `C(n)`, use the actual even/odd
increment branches to derive halving and the finite floor sum
`F(n,k) = Σ(j<k) n/2^j`. Equality `C(n)=F(n,k)` requires `n/2^k=0`.
The source-review examples distinguish the cutoff: `F(4,2)=6`, while
`F(4,3)=F(4,5)=C(4)=7`. Omitting exponent zero drops the first `n` term.
Preserve `C(2^k)+1=2^(k+1)` and the extending carry.

Observed states and transitions have different indices: five seed-inclusive
states use four transitions. A work equality for `[]` and `[false]` does not
imply equality of their zero-step states. Keep arbitrary nonzero seeds and
initial potential in bounds.

An ordered trace of per-step bills must be produced along the actual run.
Mapping a scalar total to a singleton does not recover that trace:
`[1+2]` differs from `[1,2]`. Summing an existing trace is a valid additive
transport in the other direction.

Output research adds a token renderer with decode laws, actual digit mass,
line structure and varying callback charges. This is not Haskell `Show`, byte
encoding or wall-clock performance. The earlier name-based search missed the existing
`StructuredLinear.Costs.traverse`, as #477 subsequently established. It retains
varying callback values and bills but adds no intrinsic structural list tariff.
#505 uses this owner through a local output adapter; its structured-linear
clients remain unchanged.
The historical `correspondence/timing.json` cited by the counter ledger was
absent from the supplied source archive. Its old acceptance label is not evidence.

Current disposition: #479 supplies the independent geometry and ordered bills;
#505 supplies actual prefix execution, token rendering, exact decoding, digit
mass and separate output charges. See [counter geometry](counter-geometry.md)
and [counter output](counter-output.md). Together these account for selected R6.

## Permutation execution, forcing and growth

Recovered drafts: selection-based costs, insertion-based costs and permutation
growth, with
independent design challenges and latest author candidates.

Reuse `Sequences.Occurrences` and `Sequences.Permutations`. Keep positional
picks, duplicate branches, first-occurrence removal and insertion order distinct.
A pure length theorem belongs with the pure permutation owner, avoiding a
reverse dependency from value semantics into measured execution.

The selection design calls for a fuel-free well-founded public executor and an
adequate-fuel equality for the complete measured pair. Value erasure plus an
upper cost bound does not recover an exact source execution. Charge map
callbacks, outer cells, terminal dispatch and append's copied left outer spine
through actual operations. Equality testing in removal is one declared oracle
event, not a representation-independent machine cost.

Insertion research distinguishes outer construction, delayed callback work,
outer counting and complete inner-spine observation. Forcing a thunk twice is
not free sharing. A complete observer should retain values and charge the
actual inner folds; its proposed target bill for arbitrary `xss` is
`xss.flatten.length + 3*xss.length + 1`. The flatten expression is a specification
of payload mass, not an extra runtime pass. Empty inner lists still have a
terminal observation charge.

Growth theorems must be derived from exact execution equations, then related to
native factorials and finite sums. A recurrence defined independently of an
executor is useful as a specification but does not prove execution agreement.
Keep nonuniform inner lengths, duplicate values, function-valued labels and
empty cases. Natural addition permits some charge rearrangements; those proofs
cannot silently be generalized to noncommutative traces.

Current disposition: #506 [positional permutation execution](positional-permutation-costs.md)
supplies actual construction, fuel-free execution with complete-pair adequate-fuel
correspondence, complete inner-spine observation and model-relative growth.
First-equal removal and delayed insertion retain their own remaining obligations.
#505's small insertion-output observer measures existing outputs only; it does not
charge recursive generation. R2/R4/R7 and #149 remain open.

## Already integrated numerical research

The recovered exact-arithmetic, finite-sum, discrete-estimate, growth and
recurrence drafts overlap the
maintained [exact arithmetic](adwh-exact-arithmetic.md),
[finite sums](adwh-finite-sums.md), [discrete estimates](adwh-discrete-estimates.md),
[growth](adwh-resource-growth.md), and [recurrence](adwh-recurrences.md) notes.
Use those notes and their ledgers as the destination; do not preserve draft
phase gates as active requirements.

Retain these scope tests in the capability audit: raw rational sets versus
finite real values versus strict invalid arithmetic; invalid input versus zero;
raw attainment versus closure; explicit domain restrictions in compilation;
arbitrary recurrence bases and eventual tolls; exceptional parameter cases;
and a threshold uniform in an unrestricted second parameter rather than only
pointwise growth or a product-filter limit. The floating notes similarly keep
canonical packing, overflow exclusions and rounding-step premises separate.
None of these distinctions is discharged by the axiom audit alone.

## Review failures and corrected statements

The development records contain two useful corrections beyond the planning
notes. These are resolved examples to preserve as review lessons, not newly
reported defects in the integrated code.

`development/1041/closed-author-records-r0/closure-compiler/e5-source-review-r2-erratum.md`
records a missed coercion in `eventually_value_eq_default`. An untyped zero in
`WithBot.unbotD` let Lean infer a nested `WithBot Value`, making the proposed
equality trivial instead of extracting a finite nonnegative real. The integrated
[ExactGrowth statement](../../Examples/ExactGrowth.lean) fixes the payload type
before coercing back to `Value`. Inspect elaborated types at coercion boundaries;
text that appears to express the intended mathematical equation may not do so.

`proposal-drafts/recurrences1043/clients/handoff-r2-negative-growth.md` records
that concrete finite values did not establish failure of an asymptotic Theta
claim for zero toll. The integrated
[ResourceRecurrences example](../../Examples/ResourceRecurrences.lean) includes
`zero_toll_additive_not_isTheta`, a symbolic negative result. A finite fixture
can detect some errors but cannot replace the quantified asymptotic obstruction.
