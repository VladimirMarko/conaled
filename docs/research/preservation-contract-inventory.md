# Preservation contracts already present in the repository

Repository evidence for [#231](https://github.com/VladimirMarko/conaled/issues/231)
and [#200](https://github.com/VladimirMarko/conaled/issues/200), 2026-10-29.
Inspection baseline: `c4260c72fb6bd5c1dbbd63e1973f988930aafed9`.
This inventory extends [the boundedness comparison](compositional-guarantees-and-boundedness.md).
The [implemented two-client assessment](preservation-experiment.md) classifies
these families against the selected laws and records the outstanding adapters.
It records existing declarations and design constraints. It adds no Lean
abstraction or preservation theorem.

**Boundedness, productivity, durability and optimality are acceptance examples,
not the boundary of the preservation programme.** Existing clients also retain
dependent typing, logical validity, path labels, coherence, local gluing data,
probability mass and correlation. A common interface must allow their different
judgments and evidence rather than require every client to become a predicate
on a total function's final result.

The survey uses current Lean definitions and checked examples as primary
sources. It samples contract families across the integrated library, not every
theorem. A named composition theorem below establishes its stated composition,
not a generic transport theorem for every backend. The proposed interface tests
are requirements for future work.

## Dependent judgments, identity and changes of setting

| Contract already present | Existing preservation and composition | Conditions and interface constraint |
|---|---|---|
| Indexed representations and dependent terms | In [Dependent.lean](../../Dependent.lean), `TyRep` retains a family over a represented context; `SubCert.compose` composes represented substitutions and `TermCert.reindex` transports a term certificate along one. `tmSub_comp`, `pi_subst`, `app_subst` and `sigma_subst` express substitution compatibility. | Result types depend on context values. `reindexRep` uses the equality carried by the substitution certificate to transport the fibre. A comparison must retain that indexed typing data; relating only underlying unindexed values would omit the obligation. |
| Dependent source substitution and computation | [DependentSheafSoundness](../../SquareKit/Internal/DependentSheafSoundness.lean) proves `type_substitution`, `term_substitution_heq`, `term_sound` and `conversion`; [DependentFunctionSheafSoundness](../../SquareKit/Internal/DependentFunctionSheafSoundness.lean) proves `beta_sound` and `eta_sound`. | These are interpretations of the supported source fragments. Substitution can change the type of the interpretation, requiring comparison before equality. They do not interpret arbitrary Lean dependent programs. |
| Coherent substitution through chosen pullbacks | [FamilyCoherence](../../SquareKit/FamilyCoherence.lean) proves `map_comp`, `composition_natural`, `right_unit`, `left_unit`, `associativity` and corresponding term equations. [TypeFamilyCoherence](../../SquareKit/TypeFamilyCoherence.lean) compares those maps with strict split-family substitution via `composition_comparison`. | Categorical substitution uses chosen comparison isomorphisms; split Type substitution has strict equations. Requiring all clients to compose by literal equality would exclude the former or conceal the comparison proof. |
| Dependent products under base change | [DependentBaseChange](../../SquareKit/DependentBaseChange.lean) constructs `leftComparison`, `pullbackIso` and `WithAdjunction.iso`; `evaluation` and `curry_baseChange` relate the comparison to evaluation and currying. | The square is an actual `IsPullback`, and the dependent products come with specified right adjunctions. Preservation under arbitrary base maps is not asserted without these hypotheses. |
| Logical validity under interpretation | [SheafSoundness](../../SquareKit/Internal/SheafSoundness.lean), `sound`, interprets every derivation of the current regular calculus; its cut case composes validity. `formula_instantiate` retains substitution and `frobenius_valid` interprets both directions of the source Frobenius proof. | Carrier and relation sheaf hypotheses matter. Existential interpretation uses local image and elimination into a sheaf predicate. Local existence is not a global witness-selection procedure. Soundness is not completeness or reflection. |
| Arrow-sensitive identity and family transport | [GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean), `Route.comp`, `transport`, `transport_concat`, `reindex_comp`, `comp_assoc`, and the identity laws compose a base functor with a natural fibre map. [TransferSoundness](../../SquareKit/Internal/PathTransport/TransferSoundness.lean), `basePathEquiv_concat`, retains source identity as composition of base arrows. | A route preserves the specified action on paths and fibres; its existence does not imply faithfulness. These route examples test first identity in groupoids, not a universal higher-identity transport construction. |

The last case has a checked negative example. In
[GroupoidRoutes](../../Examples/GroupoidRoutes.lean), `not_constant` distinguishes
a family with monodromy from a constant family with the same fibre cardinality.
`composed_source_route` transports the same interpreted source term through two
routes. The forgetting route still has a naturality law, but
`no_fiber_observation` and `no_label_observation` prove that it cannot reconstruct
the forgotten fibre values or path labels. Preservation must therefore name its
observations; it must not silently promise reflection or reconstruction.

The [language direction](../language-direction.md) also requires higher identity
to remain expressible. The groupoid evidence here is a lower-dimensional test
of that requirement, not a claim that every higher identity is implemented by
`Route`.

## Local-to-global and geometric contracts

Effective descent preserves compatible local objects **and their morphisms**.
In [SheafTorsorDescent](../../SquareKit/SheafTorsorDescent.lean), `Datum` retains
transport and cocycle data; `torsor` constructs a descended torsor,
`comparison` relates its restriction to the local object, and `mapEquiv`
compares compatible local maps with global equivariant maps. `Map.arrow_ident`
and `Map.arrow_comp` establish compatibility with identity and composition.
Local surjectivity of the covering map is an explicit hypothesis for descent.

[SheafActionQuotientDescent](../../SquareKit/SheafActionQuotientDescent.lean)
adds compatibility of the equivariant map into the acted-on object.
`Datum.object`, `Datum.comparison`, `arrowEquiv`, `Map.arrow_ident` and
`Map.arrow_comp` retain that additional structure. This is evidence against an
interface that keeps only truth of local properties, isomorphism classes, or
orbit sets. The gluing and arrow data are part of what is preserved. It is also
a different composition shape from sequential execution: compatibility on a
cover is needed before the global object can be constructed.

The geometric source-to-model bridge supplies another judgment shape.
[GeometricProductRule](../../SquareKit/GeometricProductRule.lean), `product`,
derives a product differentiation equation for ordinary sheaf maps from the
source derivation through soundness. `parameters` preserves that equation under
precomposition by an arbitrary natural parameter map. The scalar sheaf
hypothesis and the chosen smooth setting remain explicit. This is preservation
of a differential principle in a specified model, not a theorem that every
map between mathematical settings preserves differentiation.

## Probability contracts retain more than possible outcomes

| Contract already present | Existing declarations | Conditions and distinction |
|---|---|---|
| Exact probability interpretation | [FiniteKernel](../../Applications/Probability/FiniteKernel.lean), `Table.kernel_comp`, `tableMeaning_laws`, `tableCategoryLaws`, `table_steps_meaning` | Finite rational stochastic tables interpret as measurable kernels. Composition preserves probability mass, not merely support. The finite iteration result follows through the same interpretation. |
| Invariant distribution | `invariant_comp` and `invariant_steps` in the same module | Both transitions preserve the same measure. This proves stationarity of their composite, without asserting that the composite is reversible or converges to that measure. |
| Detailed balance | [FiniteMH](../../Applications/Probability/FiniteMH.lean), `detailed_balance`, `target_balance`, `stationary` | The finite Metropolis–Hastings construction supplies weight/proposal hypotheses. The invariant-composition theorem does not claim that detailed balance itself is closed under arbitrary composition. |
| Correlation | [ProbabilityCorrelation](../../Examples/ProbabilityCorrelation.lean), `copy_after_draw`, `draw_twice`, `joint_distributions_differ` | Shared and independent draws have the same marginals (`shared_first`, `shared_second`, `independent_first`, `independent_second`) but different joint laws. A componentwise marginal contract cannot replace the joint contract. |
| Almost-sure progress and tail bounds | [Execution](../../Applications/Probability/Execution.lean), `sequential_ae`, `sequential_tail_le`, `measurableSteps_sequential` | Composition retains the joint environment and actual intermediate result. Almost-everywhere progress is weaker than progress on every path. `sequential_tail_le` needs neither independence nor measurable-event hypotheses; `measurableSteps_sequential` separately requires countable state/result types and measurable step fibres. |
| Termination and divergence mass | [Results](../../Applications/Probability/Results.lean), `results_mass`, `divergence_mass`, `results_none`, `results_some` | Result semantics includes missing mass from divergent paths and observations of returned values/costs. Probability of a result cannot be replaced by a Boolean possibility predicate. |

Two checked boundaries prevent overclaiming. `identity_does_not_converge_to_fair`
and `orbit_does_not_converge_to_fair` in the correlation examples show that an
invariant fair measure does not imply convergence from a point start.
[CoinPaths](../../Applications/Probability/CoinPaths.lean) proves
`ae_productive` while `all_false_not_terminates` exhibits an exceptional
divergent path. Neither deterministic totality nor a uniform finite deadline
follows from the almost-sure theorem.

## Compiler, numerical and operational contracts

| Contract already present | Existing declarations | Conditions and distinction |
|---|---|---|
| Compiler interpretation and naturality | [STLCNaturality](../../SquareKit/STLCNaturality.lean), `Preserves`, `naturality`, `preserves_comp`, `naturality_comp` | Operation compatibility lifts to all supported terms and composed interpretations, relative to the chosen `HomEquiv`. This includes higher-order application/currying and sums. It does not already provide arbitrary one-way ordered refinement. |
| Algebraic law transport | [ClosedMap](../../SquareKit/ClosedMap.lean), `ClosedMap.comp`, `ClosedMap.transportLaws` | Closed-category laws transport with the specified operation-preservation, congruence and reflection hypotheses. This is generic structure transport without a transition-system or execution-prefix presentation. Reflection is an explicit premise here, not an automatic property of every interpretation. |
| Actual analytic derivatives | [AD/Core](../../Applications/AD/Core.lean), `DMap.correct`, `DMap.comp`, `DMap.pair`, `tangent_comp`; [AD/Compiler](../../Applications/AD/Compiler.lean), `compile_hasFDerivAt` | `HasFDerivAt` states the analytic relation. Equality of primal outputs alone would not specify the returned derivative. [AD/HigherOrder](../../Applications/AD/HigherOrder.lean), `Related` and `eval_related`, use curves and function relations; their sum curves have fixed tags, not arbitrary changing branches. |
| Sound enclosure | [Intervals/Arithmetic](../../Applications/Intervals/Arithmetic.lean), `compile_contains`; [Intervals/HigherOrder](../../Applications/Intervals/HigherOrder.lean), `compile_contains`, `iterateTwice_contains` | Inclusion permits overapproximation. `interval_cancellation_is_wider` is a checked negative case against exact result equality. The higher-order case retains relations on functions and their arguments. |
| Signal timing and stability intervals | [Timing/Digital](../../Applications/Timing/Digital.lean), `Stable`, `Digital.correct`, `Digital.compose`, `matrix_compose`, `matrix_stable` | The relation joins a signal, time intervals and Boolean values. Composition uses relational preservation. Signal stability here is distinct from numerical stability or a scalar execution-time upper bound. |
| Incremental repair invariants | [Incremental/Stateful](../../Applications/Incremental/Stateful.lean), `Ops`, `Laws`, `CompValid`, `Laws.comp`, `project_repair` | Composition retains cache validity, observed values and the emitted change at the actual intermediate boundary. It supplies no resource improvement merely from repair correctness. [Incremental/Arithmetic](../../Applications/Incremental/Arithmetic.lean), `tangent_is_not_a_finite_change`, distinguishes finite updates from derivatives. |
| Stable order and multiplicity | [Sorting/Stable](../../Applications/Sorting/Stable.lean), `StableSort`, `StableSort.map`, `StableSort.unique` | The contract combines sortedness, permutation and preservation of equal-key record order. Transport needs a key-preserving map, not injectivity; uniqueness additionally needs the stated partial-order hypothesis. Set membership would discard required information. |
| Abstract data-structure observations | [Sequences/AbstractFIFO](../../Applications/Sequences/AbstractFIFO.lean), `Simulation.comp`, `Simulation.runSquare_append`, `representation_independent` | Simulations compose while preserving client observations across queue representations. This is semantic representation independence, distinct from the separate cost of either implementation. |
| Parse witnesses | [Languages/Witnesses](../../Applications/Languages/Witnesses.lean), `nullableStarIso`, `derivativeStarIso`; [Languages/Parser](../../Applications/Languages/Parser.lean), `transport`, `derive`, `parse` | Inverse maps retain parse structure, including lists of nullable parses. [ParserBridge](../../Applications/Languages/ParserBridge.lean), `recognizers_agree`, establishes recognition agreement after erasure; Boolean recognition is a weaker contract than preserving parses. |
| Numerical error and domain validity | [Orbifold/NumericalExecution](../../Applications/Orbifold/NumericalExecution.lean), `run_correct`, `run_append`, `run_error` | Successful runs preserve an approximation relation to an independent exact execution, related endpoint lists and domain conditions. The runner can fail. `errorAfter` iterates changing error budgets; [NumericalBounds](../../Applications/Orbifold/NumericalBounds.lean), `local_error`, bounds truncation under control/domain assumptions. Exact rational arithmetic here does not establish a floating-point roundoff bound. |
| Symmetry and representative changes | [Orbifold/NumericalSymmetry](../../Applications/Orbifold/NumericalSymmetry.lean), `checkedStep_equivariant`, `approx_equivariant`, `run_equivariant`, `success_arrow` | The C4 action preserves execution and approximation through representative changes; the success arrow retains the action label. This is an equivariance contract, not solely equality of unlabelled results. |
| Causality | [FRP/TemporalCausality](../../Applications/FRP/TemporalCausality.lean), `Synchronous`, `synchronous_of_delivery`, `mealy_synchronous`, `shift_not_synchronous` | Causality compares runs on inputs agreeing through a prefix. Delivery needs the explicit `demand n ≤ n` condition. The shift counterexample rules out inferring synchrony from an arbitrary stream map. A unary predicate on one final result would miss this comparison. |
| Linear protocol usage and finite cut simulation | [Session/Process](../../SquareKit/Session/Process.lean), `Proof.typed`, `Typed.valid`, `CutStep.simulates`, `Steps.append` | `Proof` is Type-valued; `CutStep` retains the residual context index. The implementation covers its finite additive/unit principal-cut fragment, not arbitrary process subject reduction or global deadlock freedom. |
| Temporal horizons and occurrence identity | [Temporal/Relations](../../SquareKit/Temporal/Relations.lean), `Until.Rel.comp`, `horizon_eq`; [Progress/OccurrenceCursor](../../Applications/Progress/OccurrenceCursor.lean), `CursorRel`, `encode_advance`, `cursors_related`, `cursor_lookup`, `selected_value` | Composition retains wait/terminal evidence and dependent occurrence indices, even for duplicate payloads. Terminal observation deliberately forgets the temporal horizon. It cannot replace the indexed certificate when waiting length or selected occurrence matters. |

This table is a survey of active library modules. It does not use the historical
standalone orbifold formalization as a proof reference. Some contracts are
different views of related structure, so the rows are not a count of independent
mathematical abstractions.

## Constraints on the shared programme

The existing [RelationTransport](../../SquareKit/RelationTransport.lean)
`image_comp` and `requirement_comp` remain useful for predicates on related
behaviors. `requirement` is universal partial correctness and can hold without
any related output. It is one reusable layer. It does not by itself replace
the indexed certificates, natural transformations, comparison isomorphisms,
descent data or probability laws above.

The experiment in #231 should leave the following choices explicit:

- **Judgment and retained evidence:** propositions, indexed terms, path labels,
  morphisms, traces, costs or probability laws, including the context in which
  each is interpreted.
- **Strength and direction:** preservation, target coverage, reflection,
  reconstruction and equivalence are separate obligations. A checked
  forgetting map is an admissible client.
- **Composition shape:** sequential composition, products, substitution,
  feedback, iteration and local gluing have different prerequisites. A law
  for one is not evidence for all of them.
- **Comparison strength:** some clients have strict equations, others an
  isomorphism or a relation with further coherence laws. Preserve the actual
  comparison rather than demand one universal equality convention.
- **Assumptions and quantifiers:** admissible inputs, sheaf and covering
  hypotheses, measurability, almost-everywhere claims, and intermediate domain
  conditions must survive transport. Do not silently strengthen local existence
  into global selection or almost-sure progress into pathwise termination.
- **Operational observations:** missing outputs, failures and divergence must
  remain expressible when present in the client. A total value function is not
  a universal operational semantics.
- **Quantitative structure:** interval bounds, rational approximation budgets,
  timing maps and probability mass already require more than one natural-number
  cost. Composition may accumulate an error, preserve an invariant, or transform
  a bound; those are different laws.
- **Multiple executions and related functions:** causality and higher-order
  relations compare inputs, outputs or executions. Restricting the interface
  to a predicate about one run would force these clients to hide the relation
  that makes their composition theorem useful.

These are interface tests, not a proposal to package every field into one
record. Existing specialized modules should stay usable directly. A candidate
abstraction should demonstrate a reused proof with clients from distinct rows,
and explain which other rows remain specialized. This follows
[ADR 0002](../adr/0002-relations-and-synchronization.md): share composition while
retaining the semantic distinctions.

The finite-value delay and recovery-evidence clients proposed in #231 can remain
the bounded first formal experiment. This inventory broadens its applicability
review: before choosing the interface, compare it with the native contracts
above and record any exclusion. It does not expand that experiment into a
requirement to refactor or formalize every listed family at once.

## Continued discovery and author usability

[#235](https://github.com/VladimirMarko/conaled/issues/235) owns evolution beyond
the first experiment. Apply the [language-direction criteria](../language-direction.md#evolving-preservation-laws-and-usable-specializations)
when a new native contract exposes a gap, a shared law changes, or a concrete
specialization becomes difficult to author. Expand this inventory with evidence,
record needed infrastructure changes and retain scoped owners for unresolved
work. Existing clients and their usable specializations are regression cases
for a retrofit. The first two-client experiment cannot close that programme.
