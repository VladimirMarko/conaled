# Covered bounds, finite delay and recovery evidence

Implementation assessment for [#231](https://github.com/VladimirMarko/conaled/issues/231).
The experiment starts from `5392a69` and preserves existing public interfaces.
The [contract inventory](preservation-contract-inventory.md) supplies the wider
source audit; this assessment records the implemented instances, their limits,
and the handoff to [#235](https://github.com/VladimirMarko/conaled/issues/235).

## Result and shared law

The reusable argument is **covered relational preservation**. Existing
`Interaction.Refines.property` transfers a property to every permitted target
behavior through a related permitted source behavior. It already composes via
`Refines.trans`, backed by `RelationTransport.image_comp`. No universal
preservation record, syntax, operational semantics or modal interface was needed.

[PreservationBounds](../../SquareKit/PreservationBounds.lean) adds a small derived
lemma, `Refines.bound`, for ordered observations:

```text
targetCost(t) ≤ h(sourceCost(s))       for related s,t
sourceCost(s) ≤ B                     for every admitted source s
h monotone
⇒ targetCost(t) ≤ h(B)                for every admitted target t
```

The source and target costs can inhabit different preorders. The relation can
be many-valued, and either carrier can contain traces, failures, pairs of runs
or functions. Coverage goes from every target behavior to a source witness;
it supplies neither a target execution nor an implementation of each source
behavior. `comparison_comp` uses an actual intermediate witness and composes
bound maps in translation order. `combine` leaves the resource operations
explicit and requires
`targetOp (h a) (h b) ≤ h (sourceOp a b)` plus monotonicity of `targetOp`.
This is a sufficient upper-bound law, not a claim that every useful translation
has that law. Additional overhead can occur in the target operation, but the
caller must establish its relation to the composite implementation.

These are theorem conveniences over existing relations and orders. They do
not replace `Measured.reweight_bind`, whose additive homomorphism gives exact
accounting, or the native contracts listed below.

## Two checked clients

[FiniteDelay](../../Applications/FRP/FiniteDelay.lean) compiles a Boolean seed
and transition body with `ReactiveCompiler`. Its independent specification
returns the previous Boolean and retains the new one. The source and function
target agree by compiler soundness. A redundant realization stores the value
and its complement; `Related` retains that invariant. The existing
`Feedback.run_related` and `Pipeline.run_consumer_related` establish equality
of outputs and the related final state for every input/command list.

The pipeline observes each completed batch through `List.any id`. This
observation deliberately forgets order and occurrence multiplicity. Original
timestamped batches remain in the paired pipeline events. Silence stutters;
an emitted empty batch still advances the consumer. The experiment uses the
existing one-shot frontier engine, not a new repeated-request protocol.

`pipeline_cells` applies `Refines.bound` to all command-prefix final consumer
states, with source observation one Boolean cell, target observation two
Boolean cells, and `h n = 2*n`. Its quantifier order is one bound for every
command list, with initial sources fixed. The theorem covers only consumer
state. Source histories, payloads, timestamps, command/output lists and runtime
allocation are outside that observation. No claim of bounded whole-pipeline
memory follows.

`next_output` constructs an output and successor for every synchronous input
and state. It is independent of the cell bound. A concrete frontier script
supplies an actual nonempty emission witness. Source closure and processing
are still needed for arbitrary frontier requests; no fairness follows from
compiler soundness.

[EvidenceBounds](../../Applications/Interaction/EvidenceBounds.lean) reuses
`Evidence.Recover`, beginning at `unknownEffect`: one effect has occurred,
publication exists, and acknowledgment is absent. Reachable states are the
finite reflexive-transitive recovery closure. A tuple representation retains
effect count, publication and acknowledgment separately. `encoding_coverage`
and `Refines.bound` give `encoded_effects_bound`; `uniform_prefix_effects`
lifts it to every prefix of every permitted infinite recovery run from that
state. Both clients therefore consume the same covered-bound theorem, though
one measures retained cells and the other measures external effect executions.

`recovery_then_ack_exists` constructs a permitted finite recovery/acknowledgment
composition. It proves possibility, not that an arbitrary scheduler selects
it. `safe_without_progress` combines the uniform effect bound with the existing
infinite interrupted run that never acknowledges. Capped probes, fault budgets
and their scheduling theorem remain owned by #196. This model proves no physical
persistence or crash recovery contract.

## Composition and resource boundaries

[PreservationBounds examples](../../Examples/PreservationBounds.lean) retain
checked cases for the following distinctions:

- Two compiled delays compose using `Feedback.run_seq`, with the worked output
  `[false,false,true]` on `[true,false,true]`. The two stores remain live together.
- Two redundant stores occupy four modeled Boolean cells. The shared `combine`
  law proves the additive bound under the doubling translation. A separate
  maximum instance shows that the theorem does not force every observation to
  use addition; an implementation using maximum still owes a lifetime argument.
- `middle` represents the phase after the first transition while the second
  store and intermediate Boolean remain live. `liveCells` bounds every such
  modeled frame by five cells. This explicitly includes the connecting value;
  it is not a theorem about the evaluator's heap, stack or tuple allocations.
- Evidence encoding followed by an optional representation composes coverage
  with `Refines.trans`. A second quantitative observation adds one administrative
  unit, and `comparison_comp` preserves the bound through the intermediate tuple.
- The monotone map `n ↦ n+1` fails the additive compatibility condition: translating
  two components pays the administrative unit twice. Monotonicity is insufficient.

Cumulative work, worst-case work per output, retained storage and peak storage
are different observations. These clients establish retained Boolean-cell and
effect-count bounds, not total work or wall-clock bounds. One total synchronous
body call per input describes the machine interface; it does not price compiled
instructions. Recovery may do arbitrarily much silent work while its effect
count stays one. Boundary potentials do not occur in either chosen observation;
clients using amortization must retain both endpoint potentials through existing
`Resources.run_potential`, and cannot replace them by this cell count. #234 owns
the concrete bounded execution target and per-step accounting; #193 owns broader
resource integration.

## Failed variants and information loss

The checked examples include an empty observation fiber satisfying a universal
requirement but unable to cover a nonempty target set. A queue growing by one
unserviced input per tick is finite at each prefix but has no uniform prefix
bound. Removing a silent position changes the next observation despite preserving
completed values. Boolean batch aggregation identifies different orders and
multiplicities. Existing `Evidence.coarse_loses_publication` shows that count-only
observation cannot establish publication, still less durability.

Two further design checks exercise native contracts outside those clients:

1. `fairTable` and `biasedTable` are valid rational stochastic tables with the
   same support. `different_law` uses `Table.kernel_singleton` to prove their
   interpreted kernels differ. Support transport cannot replace mass preservation.
   Existing `ProbabilityCorrelation.joint_distributions_differ` additionally
   rejects replacing joint laws by equal marginals.
2. `erasure_no_inverse` uses two `Cursor [true,true]` witnesses. Both select the
   same payload, so no payload-only inverse recovers both occurrences. The
   adjacent application of `Occurrence.selected_value` retains the dependent
   witness through arbitrary history prefixes. Existing `DependentSquares`
   `TermCert.reindex` transports fibers along a substitution equality, and
   `Example.appliedCert` retains a result type depending on its argument value.
   An unindexed value comparison is not a replacement for either contract.

## Compatibility assessment

The table classifies the existing inventory against the selected design. A
**native layer** remains directly usable and is not implemented anew by the
ordered-bound lemma. An **adapter obligation** names work that a future client
must discharge; it does not assert that the adapter exists. All unmet shared
architecture obligations below pass to #235, coordinated with their domain
owners. None is a prerequisite for using the unchanged native API.

| Family and source evidence | Carriers, judgment and direction | Existing composition and assumptions | Assessment and missing integration obligation |
|---|---|---|---|
| Exact/relational squares; `RelationTransport`; `InteractionContracts` | Representations to meanings; forward relations, backward requirements, covered target sets | `Relational.compose`, `image_comp`, `requirement_comp`, `Refines.trans`; local preservation and target coverage distinct | Instantiated here. Equivalence/reflection require additional evidence; empty fibers do not supply progress. |
| Reactive compiler and feedback | Typed source transition terms to initialized target machines; state/output relations forward | `realize_compile`, `transport`, `run_related`, pipeline factorization; initial and local step relation, command alignment when comparing reference traces | Instantiated for finite delay. General asynchronous or stuttering compilation needs intermediate-state bounds and all-admitted-run progress, not only matching completed endpoints. |
| Interaction and durability | World states, admitted transitions, observed publication/effects/acknowledgment | `safe_interference_seq`, `Stable.closure`, `Events.interpret_safe`; actual boundary predicate and interference stability | Instantiated for finite recovery safety. #196/#225 must add their fault, persistence and crash observations; count equality does not carry them. |
| Measured resources and potentials | Values with ordered costs; state-indexed potentials | `reweight_bind` needs additive homomorphism; `reweight_bound` monotonicity; `run_potential` both boundary potentials | Compatible native layer. #193/#234 owe cost-model adequacy, intermediate live storage and resource-specific aggregation before using bound transport. |
| Optimization | Feasible candidates, objectives in an ordered carrier, minimizers | `minimizer_transport` needs feasible translation, cost comparison and dominating lift of every target alternative | Native layer. Covered executions alone do not supply candidate coverage or attainment. A shared adapter must retain feasible-set quantifiers and the lift premise. |
| Dependent representations and substitution | `TyRep` fibers over contexts, typed term sections; forward substitution with equality transport | `SubCert.compose`, `TermCert.reindex`, `term_sub_related`; related environments and indexed witnesses | Native layer, checked erasure boundary. Future adapter must map fibers and preserve substitution/casts, not erase indices into a unary value predicate. |
| Dependent source soundness | Source derivations to model sections with dependent types | `type_substitution`, `term_substitution_heq`, `term_sound`, beta/eta soundness in the supported fragments | Native layer. Shared judgment routes must retain typing/conversion and heterogeneous comparisons; no interpretation of arbitrary Lean is supplied. |
| Coherent substitution and base change | Display maps, pullback objects/arrows, natural comparison isomorphisms | `FamilyCoherence.associativity`, `composition_natural`; `DependentBaseChange.evaluation` and `curry_baseChange` with actual pullback and specified adjunctions | Native layer. Strict bound-map composition is not a coherence theorem. Adapter must preserve chosen comparisons, naturality and unit/associativity diagrams. |
| Logical validity and geometric principles | Regular derivations to sheaf validity; product-rule derivation to model equations | `SheafSoundness.sound` composes cut; `GeometricProductRule.parameters` precomposes; sheaf/model hypotheses retained | Native layer. A setting-change adapter must preserve interpretation/substitution and local image semantics; local existence is not global selection. |
| Paths, symmetry and identity | Groupoid routes, fiber maps and labeled arrows; numerical C4 action | `Route.comp`, `transport_concat`, `reindex_comp`; `checkedStep_equivariant`, `run_equivariant`, `success_arrow` | Native layer. Adapter must retain arrow action and naturality. Forgetting routes cannot reconstruct path labels; this is not arbitrary higher-identity preservation. |
| Descent | Compatible local torsors and equivariant morphisms to global objects/arrows | `mapEquiv`, `arrowEquiv`, `Map.arrow_comp`; cocycles and locally surjective cover | Native layer. A shared gluing route needs object and arrow comparisons plus cover hypotheses; sequential trace composition cannot replace gluing. |
| Probability mass, correlation and invariance | Stochastic tables/kernels and measures; exact law interpretation and invariant measure | `Table.kernel_comp`, `tableMeaning_laws`, `invariant_comp`; normalized nonnegative tables, measurable kernels, same invariant measure | Native layer, checked same-support/different-law boundary. Adapter must preserve joint mass and composition; support or marginal bounds are insufficient. Invariance does not imply reversibility or convergence. |
| Probabilistic progress and divergence | Environment-indexed executions and result/cost measures | `sequential_ae`, `sequential_tail_le`, `results_mass`; joint environment/intermediate result. Tail inequality does not require independence or measurability; measurable-step theorem separately needs countability/measurable fibers | Native layer. Adapter must retain almost-everywhere quantifiers, divergence mass and tail events. No hard deadline follows from almost-sure progress. |
| Higher-order compiler naturality and structure transport | Typed terms and categorical morphisms compared by `HomEquiv` | `naturality_comp`, `Preserves`; `ClosedMap.transportLaws` requires congruence and reflection for law transport | Native layer. Ordered one-way refinement would need an explicit compatible relation at higher types; it is not established by the current equivalence-based naturality result. |
| Analytic derivatives and higher-order AD | Primal maps with actual continuous-linear derivatives; curve/function relations | `DMap.comp`, `tangent_comp`, `compile_hasFDerivAt`, `eval_related`; analytic and curve hypotheses, fixed sum tags | Native layer. Value-only transport misses derivative correctness; adapter must preserve the analytic/curve relation and its application rule. |
| Enclosure and numerical approximation | Intervals related to points/functions; optional numerical runs related to exact runs and error budgets | `compile_contains`, `run_append`, `run_correct`, `run_error`; containment, valid domain and successful-run premises | Native layer; ordered observations can be consequences after an adequate relation is supplied. Failure/domain coverage and approximation recurrence are missing adapter obligations; exact rational bounds do not prove roundoff bounds. |
| Timing and causality | Signals/intervals/values; pairs of input/output runs with prefix agreement | `Digital.compose`, `matrix_stable`; `mealy_synchronous` and delivery demand bounds | Native layers. Timing intervals and two-run causality must remain explicit. Adapter needs interval admissibility or run-pair correspondence; neither establishes message lifetime, replay exclusion or bounded lookback. |
| Incremental state repair | Valid caches, observations and emitted changes at actual intermediate states | `Laws.comp`, `CompValid`, `project_repair`; each component's validity/change law | Native layer. Adapter must preserve both boundary validity and changes; semantic repair alone gives no resource improvement. |
| Stable sorting and FIFO representation | Ordered lists with multiplicities/equal-key order; queue states and client observations | `StableSort.map` needs key preservation, not injection; `Simulation.comp`, `runSquare_append` need state simulation | Native layers. Set erasure loses order/multiplicity. A cost adapter needs each implementation's cost relation in addition to observational agreement. |
| Parsing, linear protocols and temporal witnesses | Type-valued parses, context-indexed process proofs, indexed wait/terminal witnesses and cursors | `Parser.transport`, `derive`; `Steps.append`, finite `CutStep.simulates`; `Until.Rel.comp`, `encode_advance` | Native layers, checked occurrence-erasure boundary. Adapter must preserve witness constructors, residual contexts and horizons. Recognition, endpoint payloads or this finite cut fragment do not imply witness recovery or general deadlock freedom. |

Exact declarations, links and further negative cases for each row are in the
[inventory](preservation-contract-inventory.md). This is a representative
compatibility audit, not an assertion that every theorem fits one interface.

## Author comparison and decision

The retained direct proofs are `direct_delay_bound` and `direct_evidence_bound`
in the examples. They state the same concrete bounds and use the same assumptions
as the shared routes. They expose no new syntax, custom record or cast.

| Task | Direct/native route | Shared/specialized route | Observed author cost |
|---|---|---|---|
| Constant retained delay cells | `le_rfl` after the cell definition | `pipeline_cells`, whose implementation constructs reachable sets/coverage and supplies costs, doubling, monotonicity and comparison | Direct proof is shorter. The shared route checks connection to the compiled representation relation; it does not simplify constant arithmetic. |
| Encoded recovery effect bound | Unpack the image witness and use `reachable_effects` | `encoding_coverage.bound` with projection costs and identity bound map | Same invariant needed; shared route factors target coverage and ordered inequality chaining. Savings are small for this instance. |
| Changed delay state representation | Supply one local state/output preservation proof to `run_related` and pipeline lifting | Same native theorem calls, reused by the quantitative coverage proof | Existing local-to-run laws remove induction over each client trace. No replacement evaluator or preservation record is warranted. |
| Composed resource observations | Prove monotonicity and the operation inequality manually | `combine` takes those same obligations explicitly | A named sufficient law makes the missing overhead condition visible; it does not infer a resource model. |

Development diagnostics exposed a missing namespace, additive notation needing
normalization, and redundant tactic sequencing; they did not require stronger
mathematical hypotheses. The author was the implementing agent with repository
context. These are checked same-author comparisons, not independent usability
trials. #235 owns those trials and records assistance and failures separately.

The experiment does **not** justify a new overarching public interface. The
small derived bound lemmas retain existing arguments and can be bypassed by
ordinary direct proofs. The demonstrated reuse is native relation composition,
local-to-run lifting and the same ordered consequence in two domains. Existing
contracts and concrete results remain unchanged under their original assumptions.

## Handoff to continuing architecture

#235 owns the following unresolved deliverables, with domain owners retained:

- **Typed and coherent routes** (#36/#200): choose a native indexed/coherent
  client, specify judgment and comparison data, and show composition without
  discarding witnesses or replacing comparison isomorphisms by strict equality.
  Acceptance includes an old concrete specialization and an erasure negative case.
- **Probability-aware transport** (probability workstream/#200): instantiate a
  route retaining exact or explicitly approximate joint laws, with normalized
  mass and divergence scope. Acceptance must distinguish the same-support
  tables and preserve native kernel composition; a support adapter alone fails.
- **Operational/resource adequacy** (#193/#234): connect state observations to a
  chosen execution target, include intermediate storage and per-step work, and
  keep the uniform all-prefix quantifier. No physical bound is inherited merely
  from `pipeline_cells`. #232/#233 retain protocol and external driver obligations.
- **Recovery/durability integration** (#196/#225): supply admitted crash/recovery
  traces, publication observations and progress hypotheses before transporting
  durability or latency. The finite recovery client establishes safety only.
- **Independent author trials and retrofit policy** (#235): use public examples
  on an old client and a new/mismatching family; compare obligations, casts,
  diagnostics and assistance. Fix regressions or explicitly own a scoped
  interface revision and checked migration. Extend the inventory whenever a
  newly encountered family fails the current composition shape.

The other native-layer obligations in the table remain compatibility requirements
under #235, to be selected when a concrete consumer needs an adapter. This handoff
keeps them visible without claiming their implementation or expanding #231 into
all of probability, dependent semantics, descent and durability.
