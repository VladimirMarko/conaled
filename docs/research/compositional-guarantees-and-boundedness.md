# Compositional guarantees and bounded reactive service

Research for [#231](https://github.com/VladimirMarko/conaled/issues/231) and
[#234](https://github.com/VladimirMarko/conaled/issues/234), 2026-10-29.
Inspection baseline: `27dd013f9351fc328115101b25e1800ffc10f9ed`.
This note compares existing Lean contracts with primary literature. It adds no
Lean theorem, runtime measurement, storage model or public abstraction.
Mathematical constructions and experiments below are proposals unless named
as existing declarations.

The [repository-wide inventory](preservation-contract-inventory.md) broadens
this runtime/resource comparison to other implemented contracts, including
analytic, probabilistic, dependent and geometric preservation. Those examples
constrain the family too. Relations between executions are one setting for
shared laws; typed substitution, algebraic law transport and descent need
other judgments and composition shapes.

**Boundedness belongs in the same preservation programme as optimization,
productivity and durability.** The common structure already has a useful local
core: relational interpretation, forward possible observations, backward
universal requirements, and composition of preservation evidence. Quantitative
observations and progress need additional laws. The next experiment should test
those laws on actual clients before selecting another shared interface.

[#231](https://github.com/VladimirMarko/conaled/issues/231) owns that comparison;
[#234](https://github.com/VladimirMarko/conaled/issues/234) remains its indefinite
service consumer. Resource, optimization and durability applications should
supply acceptance examples rather than duplicate the shared task. This follows
[the language direction](../language-direction.md) and
[ADR 0002](../adr/0002-relations-and-synchronization.md): preserve distinct
semantic contracts while sharing composition.

## Existing evidence

| Existing implementation | Reusable law | Obligation it does not supply |
|---|---|---|
| [RelationTransport](../../SquareKit/RelationTransport.lean) | `image_requirement` is a Galois connection; `image_comp` and `requirement_comp` compose forward possibilities and backward requirements. | Existence of a behavior, termination or fairness. |
| [InteractionContracts](../../SquareKit/InteractionContracts.lean) | `Refines.property` transfers a property through a covering relation; `safe_interference_seq` composes safety across stable boundary interference. | Interruptions inside an operation absent from its relation, or eventual recovery. |
| [Relational squares](../../SquareKit/Relations.lean) | `compose` and `pair` preserve supplied relations; `witness_compose` connects relation witnesses to exact squares. | Coverage of arbitrary operational target executions or automatic resource adequacy. |
| [Feedback](../../Applications/Progress/Feedback.lean) and [Reactive](../../Applications/Progress/Reactive.lean) | `transport` and `run_related` lift local state/output relations to streams and finite runs. | Storage size, step duration or bounded scheduling delay. |
| [Streams](../../Applications/Progress/Streams.lean) | `productive_of_next` lifts local finite delivery; `paused_delivery` preserves outputs with exactly twice the atomic steps. | A uniform delay bound from productivity alone. |
| [Measured](../../Applications/Resources/Measured.lean) | `reweight_bind` preserves sequential accounting for additive homomorphisms; `reweight_bound` transfers inequalities through monotone maps. | Cost preservation from equality of values. |
| [Potential](../../Applications/Resources/Potential.lean) | `run_potential` telescopes local charges along the actual state trajectory, retaining both boundary potentials. | Uniform retained space or worst-case latency from an amortized total bound. |
| [Optimization transport](../../Applications/Optimization/Transport.lean) and [relations](../../Applications/Optimization/Relations.lean) | Cost agreement, feasibility and candidate coverage support optimality transport; `boundSquare` records feasibility and a bound. | Global optimality merely from a bound, or attainment from an infimum. |
| [Evidence](../../Applications/Interaction/Evidence.lean) and [Obligation](../../Applications/Interaction/Obligation.lean) | Invariant and script transport preserve modeled publication, effects and identity; counterexamples expose lost acknowledgments and delayed attempts. | Physical persistence, enforced downstream fencing or exactly-once delivery. |

The [optimization and recovery comparison](optimization-transport-and-recovery.md)
already established much of the qualitative structure. The
[probability and recovery comparison](probability-and-recovery-contracts.md)
adds joint-law and cost-distribution obligations. The new question is how a
single local preservation argument can carry useful resource bounds and
progress evidence across several clients.

## The shared qualitative structure and its direction

For a relation `r : S → T → Prop`, define:

```text
E_r(P)(t) = ∃ s, P(s) ∧ r(s,t)
U_r(Q)(s) = ∀ t, r(s,t) → Q(t).

E_r(P) ⊆ Q  iff  P ⊆ U_r(Q)
E_(r;q) = E_q ∘ E_r
U_(r;q) = U_r ∘ U_q
```

These are already checked in `RelationTransport`. Forward possibilities compose
in execution order; backward requirements compose in the opposite order. For a
function graph, `U` is ordinary predicate substitution. For a many-valued
relation it universally quantifies over the related outcomes.

A compiler comparison needs coverage in the correct direction:

```text
∀ t ∈ TargetBehaviors, ∃ s ∈ SourceBehaviors, r(s,t).
```

This is existing `Interaction.Refines`. If every source behavior satisfies
`P`, and `r(s,t) ∧ P(s)` implies `Q(t)`, every target behavior satisfies `Q`.
A primitive simulation is useful because it can establish coverage for complete
executions. A relation with no witnesses cannot do that. Conversely, target
coverage does not assert that every allowed source behavior is implemented.
[Abate et al., §§2–3](https://people.mpi-sws.org/~dg/papers/esop20.pdf) develop
compiler correctness over different trace spaces with these forward-property
and backward-requirement roles. This is an established framework, not a new
claim of universal correspondence.

For environmental assumptions, use behavior sets admitted by those assumptions.
The target assumptions must ensure that its covered source behaviors meet the
source assumptions. For a deterministic environment map `e : EnvT → EnvS`,
`A_T(u) → A_S(e(u))` suffices for that part. A relational environment comparison
needs the corresponding quantified premise. It does not establish that a real
environment satisfies either assumption.

Composition also requires compatible interfaces. A first component's result
must meet the next component's precondition, and permitted interference must
preserve that condition. In a feedback loop, mutual implications alone can
be circular; initialization and a justified stepwise argument are needed.
Assume-guarantee contract theory treats refinement and composition together
with environment compatibility; its existence does not discharge these local
obligations. [Benveniste et al., *Contracts for System Design*](https://www.emerald.com/fteda/article-abstract/12/2-3/124/1320867/Contracts-for-System-Design?redirectedFrom=PDF).

The adjunction is also a connection to abstract interpretation. Sound abstract
operations can overapproximate concrete behavior and support invariant proofs.
An abstraction does not automatically preserve every property or compute a
finite invariant. [Cousot and Cousot, POPL 1977](https://cs.nyu.edu/~pcousot/COUSOTpapers/POPL77.shtml).
For this repository, the useful next question is which resource invariant and
transfer function prove a desired bound; introducing an abstract-interpretation
hierarchy is not required to use the existing adjunction.

## Boundedness needs a metric, scope and quantifiers

Let `M(ρ,n)` be retained bytes after prefix `n` of an admissible execution `ρ`.
These proposed specifications differ:

```text
∀ ρ n, ∃ B, M(ρ,n) ≤ B              finite at every finite prefix
∀ ρ, ∃ B, ∀ n, M(ρ,n) ≤ B          a uniform bound for each execution
∃ B, ∀ ρ n, M(ρ,n) ≤ B             one bound for the admitted workload
```

For natural-valued finite-state measurements the first statement can be true
simply by choosing `B=M(ρ,n)`; it does not prevent growth. The second still
allows different admitted inputs to require arbitrarily large bounds. For
#234, a useful contract chooses a workload parameter `w`, independently bounds
admitted input sizes and retained resources, and proves a finite `B(w)` valid
for all admissible executions and prefix lengths. The parameter cannot secretly
be elapsed execution length. A fixed number of `Nat` fields does not suffice.

Indefinite service does not mean bounded lifetime work. If each input requires
work, total work grows with the number of processed inputs. Separate:

- Uniform retained memory, including stacks, buffers, pending work and metadata.
- Worst-case work per accepted input, or an explicitly weaker amortized bound.
- Continued ability to process admissible inputs, with progress and environment
  assumptions stated separately.

`run_potential` proves a bound of the form
`work(prefix) + Φ(final) ≤ Φ(initial) + charges(prefix)`.
Dropping a nonnegative final potential yields a cumulative work bound. It
neither bounds the size of the final state nor bounds every individual step
by the amortized charge. A step may spend stored potential. Hoffmann and
Hofmann's resource analysis uses partial evaluation semantics to cover
nonterminating computations too; that is relevant when proving bounds over
all prefixes instead of only successful returns.
[Paper abstract](https://www.cs.cmu.edu/~janh/assets/pdf/HoffmannH102.pdf).

The resource algebra must fit the observation. Sequential work adds. Peak
scratch space can combine by a maximum only when lifetimes do not overlap and
retained outputs and boundary state are accounted for. Concurrent live storage
usually needs simultaneous holdings and buffer bounds. Latency can use sums
along dependencies and maxima across genuinely parallel branches. Queues need
an arrival/service or capacity/backpressure invariant. These are proposed
modeling choices; `Measured` currently supplies additive sequential accounting,
not a theorem identifying all these quantities with addition.

## A quantitative preservation contract to test

A useful proposed extension of the local state relation carries an invariant,
an observation comparison and a bound transformation. For related states
`r(s,t)`, require the target observation to obey

```text
c_T(t) ≤ h(c_S(s)),                 h monotone.
```

Together with coverage of reachable target states and a source bound `B`, this
gives target bound `h(B)`. Finite bounds must map to finite bounds. A second
realization with map `k` gives `k(h(B))`. This composition is ordinary monotone
inequality transport, already represented locally by `reweight_bound`.
Costs of compiler/runtime administrative state must occur in `c_T` or in the
comparison; value correctness cannot hide them.

For composing measured computations, more is needed than monotonicity. Exact
preservation through sequencing requires compatibility with the observation
operation, as in existing `reweight_bind`. For upper bounds a sufficient
proposed condition is
`h(a) ⊗_T h(b) ≤ h(a ⊗_S b)`, with monotone target composition and suitable
unit treatment. Alternatively carry an explicit overhead transformer instead
of pretending it is a homomorphism. The direction of that inequality matters:
it bounds the sum of translated component bounds by the translated combined
bound. It is not available for every monotone map.

A source transition realized by several target steps needs an additional
progress argument. In a deterministic experiment, exhibit a finite target
segment for each source step, preserve the relation at its endpoint, and
bound all intermediate storage and segment work. Induct on source prefixes to
compose the segments. For nondeterministic machines, existence of a good
segment is insufficient: every admitted execution must make the corresponding
progress under explicit fairness or a well-founded stuttering argument.
Matching only finished segments misses an infinite silent target execution.
The existing `paused_delivery` supplies a concrete deterministic factor-two
case; it does not prove a general asynchronous simulation theorem.

This suggests a small family of compatible laws, rather than one record
containing every resource, progress and durability property. Atkey's
parameterised computations show how pre/post indices and monoidal structure
can organize composable effects. They are a possible language-level account
if repeated clients justify indices; they do not supply physical cost or
crash semantics by themselves.
[Atkey, *Parameterised Notions of Computation*](https://bentnib.org/param-notions.pdf).

## Cross-domain experiment and failure cases

A proposed first comparison uses two clients with different observations.

**Finite-value reactive delay.** Start with initialized delay over `Bool`.
Instantiate the existing initialized-machine and reactive-compiler interfaces
with a finite-value delay; the current compiled count/sum examples do not
already provide a compiled `Bool` delay. Specify an abstract backend retaining
one value, and a second backend with a
finite phase bit that inserts a silent step. Relate their emitted sequences
and boundary states; bound the second backend's intermediate states and steps.
Sequentially compose two delays without retaining the lifetime output list.
In a chosen fixed-cell model the composition retains two delayed values plus
explicit administrative cells, with a constant work bound per input. Physical
Lean allocation is a further realization obligation. The current feedback and
paused-producer results supply parts of this construction, not its complete
bounded-resource proof.

**Recovery of already-published evidence.** Reuse `Evidence.Recover` without
re-executing the external effect. In a bounded experiment, take Boolean probe
outcomes, a fixed attempt cap, and an explicit unresolved result. If among the
first `f+1` completed probes at most `f` fail and the cap is sufficient, a
successful acknowledgment follows within `f+1` probes. Count probes and effects
separately; preserve the effect count and publication invariant under every
transition. Compose the observation phase with a bounded cleanup phase only
when its precondition follows from the actual intermediate result. This is
the existing [recovery-resource proposal](probability-and-recovery-contracts.md#revised-smallest-recovery-resource-experiment),
not a claim that `Evidence` already has physical durability or probe bounds.
#196 owns implementation of the capped probes and fault-budget theorem. #231
should reuse or coordinate a scoped specialization of that consumer, rather
than create another owner for the recovery implementation. If it is unavailable,
#231 can compare existing finite `Evidence` recovery transitions with explicit
per-transition accounting, leaving capped retry and its progress theorem to
#196. Closure of the broader recovery programme is not a prerequisite.

Both clients can use local simulation, invariant transport, finite-run
composition and quantitative bounds. Their progress premises differ: total
bounded transitions for delay, fault and scheduling assumptions for recovery.
Their observations also differ: output sequence versus effect/publication/
acknowledgment. The shared interface earns its place only if it removes repeated
proof work while retaining those distinctions.

Retain these negative cases alongside the positive comparison:

| Dropped obligation | Counterexample or existing evidence |
|---|---|
| Uniform bounds | A counter holding the processed-input count has finitely many fields and a finite value at every prefix, yet requires an unbounded representation. |
| Buffer compatibility | Bounded producer and consumer states connected by an unbounded queue can accumulate arbitrary pending data when service lags arrivals. |
| Nonblocking progress | A bounded machine can silently loop forever. `silent_no_evaluation` and `filter_no_match` are checked examples. |
| Observation adequacy | `Evidence.coarse_loses_publication` preserves effect count while losing publication. A value-only compiler relation likewise permits extra retained garbage. |
| Crash semantics | Normal-return agreement allows a crash between two independently durable writes to expose a mixed state unless the contract prevents it. This is a constructed scenario, not a theorem about an implemented storage layer. |
| Candidate coverage | A translated optimizer may minimize over its image while a cheaper feasible target candidate lies outside that image. `minimizer_transport` exposes the missing dominating-lift premise. |
| Identity lifetime | Reusing a bounded ID without excluding stale messages can mistake an old request for a new one. Adding an ever-growing epoch merely moves the growth. |
| Probability strength | Almost-sure productivity does not imply a hard deadline or finite expected cost. The checked heavy-tail and retry examples are documented in the probability/recovery comparison. |

Durability must retain permitted crash points and recovered observations,
including repeated crashes during recovery. Perennial's recovery refinement
uses those observations and proves safety; it does not infer eventual recovery
from them. GoJournal adds modular crash specifications and framing for its
verified journal. These support studying composition at the right boundary,
not a conclusion that arbitrary durable components compose atomically.
[Perennial, §§3, 5](https://pdos.csail.mit.edu/papers/perennial:sosp19.pdf);
[GoJournal, §§2–5](https://www.usenix.org/system/files/osdi21-chajed.pdf).
The local [durability research](compositional-durability.md) owns the broader
comparison. Acknowledgment truth, publication persistence and the absence of
duplicate effects remain separate properties.

Optimization has a further quantifier distinction. A resource bound compares
one execution with a budget. Optimality compares a candidate against all
feasible alternatives. Existing `minimizer_image` needs cost agreement;
`minimizer_transport` additionally needs feasible translation and a dominating
source lift for every target alternative. Translating each component's local
optimum need not optimize their composition when they share resources or when
one component changes another's feasible choices. Product feasibility and an
appropriate separable monotone objective would be sufficient assumptions in a
separate proposed theorem. They are not consequences of ordinary simulation.

## Bounded follow-up under #231

Extend #231's comparison with the two clients above, using the existing
relation, progress and resource APIs first. Record the guarantee, environment
assumptions, observation relation, coverage direction, resource operation and
progress premise for each client. Develop one reusable local-to-run law only
where those clients repeat a proof. Compare the direct and shared caller
obligations, including intermediate states and boundary potentials.

Acceptance should include a composed example, a representation change with
explicit quantitative overhead, a reachable nonempty witness, and failed
variants that lose progress or exceed a uniform resource bound. Keep the
mathematical specification independent of the concrete backend. If existing
APIs already express the comparison without repeated arguments, retain them
and report that result instead of adding a wrapper.

#234 then uses the result for its first indefinite-service class and closure
laws. [#232](https://github.com/VladimirMarko/conaled/issues/232) supplies identity
and retention constraints; [#193](https://github.com/VladimirMarko/conaled/issues/193)
and [#177](https://github.com/VladimirMarko/conaled/issues/177) supply resource
and cost comparisons. [#225](https://github.com/VladimirMarko/conaled/issues/225)
and [#196](https://github.com/VladimirMarko/conaled/issues/196) own crash,
observation and recovery obligations. [#200](https://github.com/VladimirMarko/conaled/issues/200)
uses these examples to classify transport routes by the judgments and
observations they preserve, including one-way bounds and lost information.
This investigation leaves the remainder of the correspondence programme open.
