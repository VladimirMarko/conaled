# Resource contracts for replaceable data structures

Assessment for [#177](https://github.com/VladimirMarko/conaled/issues/177),
2026-10-29. Reuse `Resources` execution and accounting and `Optimization`
admissibility/objectives. The next implementation should compare ordinary and
cached ordered-summary realizations on the same append/query clients, charging
conversion and maintenance. A new generic cost framework or a textbook port
would not address the missing comparison.

This note follows the accepted [source survey](functional-data-structures.md)
and [architecture assessment](data-structure-architecture.md). Declaration
inspection used `52751e27aef9c4d4ced7eaf697e2c5d16cc9500e`; it adds no Lean theorem
or fresh build claim. Proposed laws and arithmetic examples below are
implementation specifications, not accepted formal results. #238 owns target
capabilities, #185 owns ordered-summary semantics, #178 owns finger-tree fit,
and #226/#227 own durability and persistent diagnostic-query contracts.

## What the existing interfaces establish

| Inspected declarations | Reusable guarantee | Boundary |
| --- | --- | --- |
| [`Resources.Measured`, `bind`, `bind_erases`, `erasureSquare`](../../Applications/Resources/Measured.lean) | Values and resource observations remain distinct; erasure composes independently of costs. `bind_assoc` needs associative addition. | Semantic agreement gives no cost agreement; `same_value_different_cost` is a checked counterexample. |
| [`run`, `run_append`, `run_invariant`, `run_value_fusion`](../../Applications/Resources/Workload.lean) | Execute measured transitions on their actual successive states, preserve reachable invariants and independent fold semantics. Observation composition needs an additive monoid, not commutativity. | Finite sequential words, with no branching graph, scheduler or failure semantics. |
| [`run_potential`, `run_potential_exact`, `budget_append`](../../Applications/Resources/Potential.lean) | Local natural-number inequalities telescope with both initial and final potential retained. Exact local identities give an exact global identity. | Charges follow the same state trajectory. `initial_potential_matters` forbids dropping arbitrary initial credit. |
| [`reweight_run`](../../Applications/Resources/Workload.lean), [`reweight_bound`](../../Applications/Resources/Measured.lean) | An additive map preserves accumulated observations; monotonicity separately preserves bounds. | An arbitrary change of units need not preserve composition or inequalities. |
| [`FIFOContracts.Accounting`, `client_bound`, `sequential_bound`, `reobserved_bound`](../../Applications/Resources/FIFOContracts.lean) | Public profiles over decoded states hide the concrete potential formula behind an existential certificate. Sequential composition spends initial credit once. | The initial-credit predicate and simulation are obligations; final head observation is uncharged. This is conventional Lean abstraction, not a language-level sealing theorem. |
| [`Optimization.minimizers`, `pareto`, `Attained`, `select`, `pullbackWorkload`](../../Applications/Optimization/Basic.lean) | Separate admissibility, objectives, attainment, selection, and candidate/workload maps. | `select` is noncomputable; finite candidate selection needs a separate executable procedure. Pareto candidates need not be least. |
| [`minimizer_image`, `minimizer_transport`, `minimizer_reflect`, `value_transport`](../../Applications/Optimization/Transport.lean) | Cost agreement and monotonicity transfer image optimality; dominating lifts extend it to target alternatives. Reflection needs an order embedding. Infimum transport has stronger hypotheses. | A semantic square supplies none of those cost or coverage hypotheses. |
| [`FirstMinimum`, `LastMinimum`](../../Applications/Optimization/SelectionSpec.lean) | Tie observations specify positional selection independently of the selector. | Equal objective values alone do not preserve which candidate is returned. |
| [`isBigO_of_nat_bound`](../../Applications/Resources/Growth.lean) | An eventual explicit natural bound yields a real-cast `Asymptotics.IsBigO`. | The family, size parameter, constants and primitive model must already be supplied. |

The accepted #173 accounting reconstruction covers binary writes and symmetric
list workloads, as recorded in its [provenance ledger](adwh-potential-accounting-ledger.json).
Actual [`BinaryCounter.flipCost_potential`, `counter_potential`](../../Applications/Resources/BinaryCounter.lean)
and [`SymmetricCosts.execute_work_potential`, `run_work_empty`](../../Applications/Resources/SymmetricCosts.lean)
retain their stated models. The latter bounds structural work by eight per
operation from empty, not elapsed time. Later random-access work includes
[cache and lookup accounting](adwh-random-access-costs.md); it must not be
reported as absent merely because #175's earlier audit deferred it. These
reconstructions do not establish every ADWH performance claim; the
[reconstruction map](adwh-reconstruction-map.md) remains the coverage record.

Separate six kinds of evidence when using this code: value refinement;
instrumentation and erasure; termination of the actual recursion; exact
primitive counts; asymptotic families derived from those counts; measured
performance on a named compiler/runtime/target. A terminating Lean definition
does not bound a reactive service's response time. An exact count does not
supply the duration or bit complexity of the counted primitive. No runtime
measurements were made here.

## Assumptions to select and assumptions to defer

Okasaki's 1996 thesis, §§3.2–3.3, explains why repeated operations on old
versions invalidate ordinary linear-history amortization. Its lazy analysis
relies on delayed computation and shared memoized results; appendix A specifies
suspension evaluation and memoization. Chapter 4 studies scheduling deferred
work for worst-case bounds. These are possible techniques if a target supports
their requirements, not consequences of translating list equations to Lean.
[Primary thesis](https://www.cs.cmu.edu/~rwh/students/okasaki.pdf).

Nipkow and collaborators' July 27, 2026 book separates functional correctness
from running-time functions (§1.5), and basic amortization from queue scheduling
(chapters 19–20). Its primitive-count model stops short of compiler and hardware
validation (§1.5.2). Reuse the technique of explicit recurrences and invariants;
retain their model assumptions when borrowing a bound.
[Primary book](https://fdsa-book.net/functional_data_structures_algorithms.pdf).

Calf supplies a language-level phase distinction between behavior and cost and
case studies with sequential and parallel complexity. Local `Measured` pairs
permit arbitrary Lean callers to inspect their cost component; the existing
FIFO noninterference theorem restricts its clients explicitly. Reuse the local
contract unless a client requires the stronger linguistic guarantee.
[Primary paper](https://www.cs.cmu.edu/~rwh/papers/calf/popl22.pdf),
[local comparison](modular-fifo-costs.md).

| Concern | First implementation | Deferred obligation |
| --- | --- | --- |
| History | Finite sequential append/query words with state threaded once. | Persistent branch accounting needs credit splitting or accounting for shared evaluation. |
| Evaluation | Explicit eager measured recursions; charge each summary combination. | Lazy demand, suspension identity, memo-table hits/misses and forcing schedules. |
| Primitive model | Natural counts or vectors of traversal visits, summary combinations and cache accesses, with stated weights. | Compiler lowering, machine arithmetic, allocator and physical-time adequacy. |
| Storage | Logical sequence length and one additional summary value; capacity eligibility checked on every prefix. | Physical heap size, sharing graph, fragmentation, garbage collection and reclamation time. A summary value is not necessarily one machine word. |
| Objectives | Sequential work plus explicit retained-state observations. | Span, latency, energy and communication require their own composition and primitive models. |
| Conversion | A measured traversal to build a valid cache; projection to discard it; target-specific costs remain parameters. | Online switching policy, predictive workloads, amortization of migration under concurrency. |
| Failure | No crashes in the first measured word. | Durability protocols supply failure traces and recovery work through #226/#227. |

Retained space cannot be inferred by summing allocations. A later live-space
model must record allocation and release events, reachable roots and intermediate
peaks, including temporary conversion storage. Parallel span cannot be inferred
by summing sequential work. These missing models prevent ranking candidates on
those objectives; they do not prevent proving the narrower work contract.

## Two realizations and two connected clients

Existing evidence already compares actual FIFO operations. In
[`Examples.FIFOContracts`](../../Examples/FIFOContracts.lean), enqueue 1,
enqueue 2, delete, enqueue 3 gives the same head 2, but costs six list visits
and nine symmetric visits. The list exact enqueue cost is `length + 1`; the
symmetric theorem supplies an eight-per-operation upper bound. Comparing
upper bounds alone cannot establish which actual execution is cheaper on an
arbitrary workload. These are structural observations, not runtime benchmarks.

The proposed next comparison shares #238's append/query client and #185's
ordered-summary semantics. An independent abstract state is `xs : List A`;
append extends its right end and query returns the ordered monoidal summary.
Plain state retains `xs`; cached state retains `(xs, m)` with invariant
`m = summary xs`. Both preserve full sequence observation when required.
For query-only clients the quotient that stores just `m` is a separate
realization under a weaker observation contract, not permission to erase
history from a full-sequence client.

Use two clients: a batch build followed by one summary, and queries after each
append, connected to the existing symmetric prefix-length observation. Use Boolean payloads and parity as the first cost comparison: query scans
payloads with XOR or reads maintained parity. A bounded buffer already needs
its length for append, so an extra length cache would be an artificial
comparison. Length remains a semantic composition test. Begin with singleton appends. General chunk appends require explicit chunk-summary
costs. An arbitrary monoid does not justify constant-cost multiplication or
constant-size summaries; length and an ordered noncommutative diagnostic
summary should have distinct interpretations.

Here is a **proposed cost model**, with arithmetic examples rather than Lean
claims. Start empty. Both realizations use the same measured list append;
let `B` be its total cost, including terminal visits. A plain query visits
`l + 1` nodes at current length `l` and performs `l` summary combinations.
A cached append performs one summary combination and one cache write; a cached
query performs one read. Assign weights `v`, `s`, `w`, `r` respectively, all
natural numbers. Ignore only work explicitly common to both clients. For `n`
appends and query lengths `l₁,…,lq`:

```text
plain  = B + v * Σ(lj + 1) + s * Σ lj
cached = B + n * (s + w) + q * r
```

With every weight one, four appends and one query have `B = 1+2+3+4 = 10`:
plain costs 19, cached costs 19. Eight appends and one query cost 53 each;
with cache writes weighted two, the cached version costs 61 versus 53.
Four appends with queries after each cost 34 plain versus 22 cached when all
weights are one. With no query and positive maintenance cost the plain
realization wins. Thus query placement and resource weights matter; neither
representation is universally preferable. These conclusions concern exactly
the displayed model and exclude full-list export costs, which must be added
if either client requests them.

Converting an existing plain state of length `k` to a cache adds
`v*(k+1) + s*k + w` in this model, plus any representation copy costs supplied
by the target. The benefit of switching is the future cost difference after
that charge, not the difference between already-initialized query costs.
Discarding a cache can be a value projection in the source model; reclamation
in a concrete target is a separate charged operation. Repeated conversions
must each be counted. Cache validation is also a traversal unless correctness
comes from construction evidence; do not treat a dynamic check as free.

A memory-capable target can supply growing sequences subject to its stated
resource model. A target with fixed capacity `N` can realize the same client
only on words whose every prefix stays within capacity, with sufficient summary
representation space. Alternatively expose rejection/backpressure in both
client specifications. For Boolean payloads, a bounded target can use `Fin (N+1)` length and a
Boolean parity cache. A mathematical `Nat` length counter is not a bounded
machine register without an overflow premise. A target lacking retained state
cannot implement arbitrary history-sensitive inter-request queries without
external state, replay, or a weaker contract. #238 owns the broader capability
argument; no heap or pointer identity is needed by the abstract laws here.

## Candidate laws and failure cases

These are statement templates for the implementation, with no new theorem
status. Existing lemmas should discharge the reusable parts.

1. **Reachable observation and workload transport.** For operations `stepR`,
   abstract operations `stepS`, decoder `d`, workload map `e`, and invariant
   `P`, require `P s₀`, closure of `P`, and stepwise observation agreement.
   When one source command maps to a target command word, require simulation
   of that whole word, preserving replies in order and any capacity errors.
   Derive the whole-run agreement by `run_value_fusion` or its existing fold
   ingredients. Do not replace `e w` with `w` unless the map is identity.
2. **Sequential budget.** Require at every reachable transition
   `cost + Φ(next) ≤ Φ(before) + charge`, with natural nonnegative potential.
   Then `cost(run) + Φ(final) ≤ Φ(initial) + budget`. For a reachable-only
   premise, use an invariant subtype or prove the local condition along the
   trajectory; the current `run_potential` expects the condition on all states
   of its state type. Compose segments with the final state and its potential
   intact. #173 already proves this linear theorem.
3. **Switching.** Require a measured conversion `convert : R → Measured S C`,
   valid output states, preservation of the client observation, and a bound on
   conversion cost. Compose prefix, conversion and suffix with `bind`; retain
   any initialization credit required for the new representation. A conversion
   square without a cost bound proves no improvement.
4. **Change of resource interpretation.** Require an additive observation map
   for exact sequential composition, monotonicity for inequalities, and suitable
   ordered-addition hypotheses when summing component bounds. For example
   `h(n)=n+1` is monotone but does not preserve zero or addition. On integer
   observations `h(n)=-n` is additive but reverses ordinary bounds.
5. **Restricted optimization.** Put only semantically valid, capacity-admissible
   realizations in `A`; fix the workload and objective before comparing them.
   Reuse `minimizer_image` with cost agreement and a monotone map. To claim
   target-wide least cost, provide the dominating-lift hypothesis of
   `minimizer_transport`; mere compilation coverage of some candidates is
   insufficient. Keep ties and positional selectors separate. An infimum need
   not be attained, and an empty feasible set supplies no implementation.

For multiobjective work and retained space, use a product order and `pareto`.
A hypothetical pair with costs `(2,5)` and `(5,2)` is incomparable; replacing
that order by a weighted sum is an explicit policy choice. Positive weights
alone do not recover every Pareto point or preserve a tie policy. A cheaper
upper bound alone does not prove a cheaper actual run.

Branching already has a checked counterexample in
[`Examples.FIFOContracts.chargedQueue`](../../Examples/FIFOContracts.lean).
The valid symmetric queue `([0],[1,2,3,4,5,6,7])` has initialization credit 12.
Each independently repeated delete costs 18; together 36 exceeds `12+2*8`.
The linear theorem remains true for each branch with its own initial allowance.
A future branching theorem must charge both initial allowances, allocate
nonduplicable credits across branches, or model shared evaluation and its
once-only payment. Immutability alone supplies none of these disciplines.

## Durability and storage boundary

#226's shared case is an ordered append-if-fresh history of session, identity
and payload, with a fold/count query. Compare an append log with a checkpoint
plus tail while preserving the entire logical history when required. A
summary-only checkpoint cannot answer arbitrary history queries. Ordinary
retention, branchable versions, and recovery after a crash are separate
contracts. A cache-preservation theorem does not establish an atomic durable
commit or acknowledgement guarantee.

The durable comparison needs a workload map from accepted logical appends to
physical writes, persistence barriers, root installation and recovery steps.
Charge deduplication, checkpoint copying, retained cells or encoded bytes,
recovery reads, and query folds when those operations occur. Typed retained
cells need no universal byte-encoding layer; encode/decode costs apply only to
a realization using them. Keep recovery attempts and crashes in the cost
workload: unlimited crashes prevent an unconditional finite completion-cost
bound. #227 must state retention and reclamation policy before using a storage
bound; temporarily live old and new checkpoints can both matter.

## Bounded implementation proposal

**Compare measured plain and cached ordered-summary workloads.** Depend on
accepted #177/#238 and reuse #185's semantic definitions rather than recreating
them. Keep this within the current `Resources` and `Optimization` interfaces.

Acceptance:

1. Instrument actual singleton append, summary traversal, cache maintenance,
   query and conversion; prove erasure, reachable invariants and exact counts
   for the displayed model, including empty input and failed cache validity.
   Treat runtime allocation and primitive latency as unmodeled.
2. Use Boolean parity for the cost comparison. Derive one client contract and instantiate it for both realizations. Connect
   batch-final and every-prefix queries to their independent list/summary
   specifications. Include ordered noncommutative semantics and the cheaper
   bounded length specialization as a semantic composition check without
   assuming all these summaries cost the same. Include full ordered
   materialization, charging any copying or traversal required by each target.
3. Prove workload formulas, the displayed tie and reversal cases, a nonempty
   conversion case, and a case where conversion erases any query savings.
   Preserve the workload map and initial state in all comparisons.
4. Give a fixed-capacity eligibility predicate with prefix preservation;
   demonstrate a valid word and an overflow word. Do not claim actual bounded
   compilation from a predicate alone. Reuse #238's stronger target realization
   if implemented, retaining its error/progress behavior.
5. Instantiate restricted `Optimization` candidates, show a tie and a product
   order incomparability case, and retain an unavailable-candidate example.
   No global-optimality, heap-size, or measured-speed claim follows.
6. Use example-driven development and statement review for every new formal
   claim, independent Standards/Spec review, and README's routine candidate
   build plus exhaustive proof audit. No new language or framework is required.

This slice leaves arbitrary indexed updates, lazy sharing, branching credits,
parallel cost, physical reclamation and crash cost to their explicit owners.
#178 can use its results to decide whether a measured tree has a client benefit;
#174 remains responsible for the broader toolkit. A tree or queue is never a
prerequisite for using `run`, reweighting, potential bounds or optimization.

## Cross-domain executions (#193)

[FRP and numerical adapters](measured-frp-numerical-execution.md) now exercise
`Measured` and workload/reweighting laws outside algorithm reconstruction.
FRP reuses the continuing workload executor; numerical motion needs a local
short-circuit recurrence that retains spent work. The common extension is only
an attempt/acceptance/rejection observation product with additive tariffs.
No new potential law or common execution runner was needed. These finite
attempt counts do not resolve #113 retention costs or #177 structure-dependent
traversal, allocation and ownership obligations.
