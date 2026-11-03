# Extensions from the compiling with squares discussion

This is the reconciled extension list from the
[possibilities discussion](history/compiling-with-squares-possibilities.md).
Prompt 2 governs where it conflicts with Response 1; Response 2 supplies the
reformulation. Ideas from Response 1 that remain compatible are retained below.
The list records scope for future GitHub issues, not a commitment to a particular
machine, representation, or implementation schedule.

Elegant specifications should define families of correct implementations.
Felix architectural parity comes first. Exact mathematical meanings remain
separate from executable representations, observation guarantees, and costs.
Machine choices belong in particular realizations or explicit parameters.

The [shared language direction](language-direction.md) connects categorical
compilation to internal reasoning: make the mathematical setting a first-class
parameter, so authors can factor out a construction's requirements and reuse
it across suitable targets and models. Use progress in both workstreams to
constrain the language's design; this ambition concerns semantics and admissible
reasoning as well as the author interface.

## Existing work to reuse

1. **Establish Felix architectural parity.** Reuse the inventory and plan in
   [#1](https://github.com/VladimirMarko/conaled/issues/1) and implementation
   milestone [#15](https://github.com/VladimirMarko/conaled/issues/15), including
   their child issues. This covers general categorical infrastructure, separate
   operations/equivalence/laws, structure-preserving maps, law transport, general
   squares, and recovery of existing applications through those abstractions.
   There should be no separate Type Class Morphisms port: investigate its useful
   mathematical principles within this work and the broader Felix effort.

2. **Port and complete the full body of Felix work.** Reuse
   [#8](https://github.com/VladimirMarko/conaled/issues/8). Distinguish proved
   upstream constructions from unfinished claims requiring mathematical work.
   Preserve stronger local results. Extensions below that complete Felix
   constructions should link to this issue rather than duplicate its scope.

## Representation and certified construction

3. **Compose certified approximations of exact specifications.** Develop
   observation and error contracts with explicit composition hypotheses,
   including sensitivity or continuity bounds where needed. Keep enclosure,
   error bounds, and exact representation distinct. Demonstrate how a guarantee
   survives successive representation changes and where a missing hypothesis
   prevents composition. Approximation belongs in the realization contract;
   unqualified numerical approximation must not replace the mathematical meaning.
   This extends the relational infrastructure covered by the parity milestone.

4. **Preserve dependencies in enclosure analysis.** Investigate symbolic and
   relational representations that retain correlations lost by ordinary interval
   operations. Compare them through a shared concrete meaning and explicit
   precision judgments. Cancellation and correlated outputs should distinguish
   soundness, precision improvement, and equality of analysis results. Do not
   promise optimal bounds for unrestricted programs.

5. **Construct and transform proof-indexed implementations.** Develop algorithms
   that select, normalize, specialize, or transform implementations while
   carrying the relevant correctness evidence. Dependent pairs describe valid
   implementations; algorithms must still construct them. Revisit partial
   evaluation, code motion, sharing, and representation search on this basis.
   State which observations each transformation preserves, and prove cost
   improvements separately. Include executable examples that expose whether
   semantic witness data remains at runtime. Neither smart constructors nor a
   shared graph are prescribed as the universal interface.

6. **Represent finite functions with memo tries and tables.** Supply executable
   function representations with tabulation/lookup correctness and compositional
   operations. Connect at least one representation to an existing application,
   such as carry functions or language computations. Lazy, partial, and infinite
   domains require additional contracts and are later generalizations.

7. **Represent linear maps with structured matrices.** Add useful block, sparse,
   permutation, or factored representations related to the same linear-map
   semantics. Demonstrate composition without obligatory dense materialization
   and reuse in AD, ordinary linear algebra, or timing. Require only the scalar
   structure appropriate to each representation.

## Differentiation and integration

8. **Complete general higher derivatives and higher-order AD.** Extend beyond
   polynomial towers to coherent all-order smooth differentiation, multivariate
   derivatives, and programs that accept, return, or capture functions. Include
   higher-order reverse mode and alternative derivative representations. Compare
   suitable semantics before choosing a model for function types. Completion
   requires composition and correctness results with explicit hypotheses;
   executable evaluation and space behavior need their own results. Smooth
   derivative towers must not be treated as convergent Taylor representations
   without an additional analyticity contract.

9. **Develop exact integration semantics and compositional laws.** Make domains,
   measures, codomains, and admissibility hypotheses explicit, including in
   higher dimensions. Investigate categorical integration alongside the pinned
   Mathlib infrastructure. Treat the fundamental theorem of calculus,
   product-domain integration, change of variables, and differentiation under
   integration as distinct results with their own hypotheses. Exact multivariate
   polynomial integration is an initial checked application, not the final scope.

10. **Realize integrals by certified numerical algorithms.** Connect quadrature,
    cubature, or other selected algorithms to item 9 through a requested-error
    contract. Specify the effective input information needed to meet the bound
    and terminate; classical smoothness alone is insufficient. Use this to test
    composition of AD, enclosures, polynomial representations, and error
    contracts from item 3. Selecting a numerical algorithm must not redefine
    the integral.

## Time, feedback, and evolving computations

11. **Generalize timing to real-time semantics and certified representations.**
    Determine the assumptions needed by each timing construction and recover
    rational timing as an instance where applicable. Develop real-time signal
    semantics and executable representations with guarantees over all relevant
    real times. Rational samples alone do not determine an arbitrary real-time
    signal. Preserve the distinction between setup/hold bounds and sets of times,
    including the role of inverted intervals.

12. **Model causal events, local clocks, and relativistic timing.** Investigate
    temporal models and maps between their observations without assuming one
    global clock. Specify how clock relationships, locality, and relativistic
    effects enter the chosen model. Deliver contrasting examples and explicit
    assumptions; replacing rational time by real time does not resolve these
    questions. This research should inform subsequent hardware models.

13. **Support state and feedback with model-specific admissibility.** Develop
    feedback operations whose witnesses express the conditions needed by the
    chosen semantics, such as guardedness, causality, or existence and uniqueness.
    Establish the laws that actually follow. Recover stateful examples without
    requiring every realization to use registers, cycle counts, or handshakes.
    Coordinate the general construction with #8; this item also needs concrete
    temporal applications beyond an abstract interface.

14. **Develop functional reactive semantics and evaluation strategies.** Relate
    behaviors, events, switching, and finite observations to suitable temporal
    meanings. Explore push-pull and incremental evaluation as realizations.
    State productivity, simultaneous-event, and approximation obligations where
    applicable. Discrete causal streams can be an initial case without becoming
    the definition of all reactive computation.

15. **Model partial information and unambiguous concurrent choice.** Describe
    compatible partial results and their combination, then relate concurrent
    evaluation to that meaning. Separate agreement of completed outputs from
    progress, termination, and scheduling guarantees. Racing implementations
    that agree on final answers is an example to analyze, not already a proof
    of unambiguous choice.

## Hardware research and external realizations

16. **Recover and analyze the Tabula architectural sources.** Continue from the
    [preserved WP003 and provenance](references/tabula/README.md), pursuing the
    original 2010 papers, WP004, and DesignInsight material identified in the
    discussion. Record what is recovered and what remains unavailable. Extract
    stated design principles, assumptions, and mechanisms; distinguish those
    from marketing claims and from principles we would need to derive ourselves.

17. **Study functional-language hardware architectures.** Examine the Heron,
    Cloaca, KappaMutor, and Ouros research identified in Response 2 against primary
    sources. Compare function representations, parallel evaluation, memory,
    laziness, and garbage collection, including their proof and benchmark
    boundaries. Produce architectural lessons and candidate experiments rather
    than selecting a mandatory graph-reduction runtime.

18. **Derive hardware realizations parameterized by architecture.** Explore
    locality, communication, storage, spatial duplication, and temporal reuse
    as explicit choices under a shared specification. Relate observations and
    admissibility across contrasting realizations. Introduce schedules and
    resource validators where a selected model needs them. Distinguish proved
    costs in an abstract model from measured area, energy, or frequency.
    Neither operation graphs nor discrete microsteps define correctness for
    every architecture.

19. **Connect signal guarantees to physical observation contracts.** Relate
    stability guarantees to sampling or handshake events under explicit
    propagation, setup/hold, skew, routing, load, and characterization assumptions.
    Address causality and clock-domain boundaries in the selected realizations.
    A sound empty observation interval does not demonstrate successful sampling.
    Claims about metastability or voltage-level behavior require an appropriate
    physical model beyond Boolean signal semantics.

20. **Build checked interoperability with external hardware tools.** Introduce
    finite-word encodings, arithmetic conventions, protocols, RTL, or netlists
    when a chosen external interface requires them. Give each representation a
    meaning and each conversion a preservation or error contract. Identify the
    trust boundary for synthesis and place-and-route, using checked certificates
    where available. Graphs, ready/valid, FIFOs, fixed-point formats, and machine
    words remain local interface choices. The concrete first target awaits the
    architectural investigations.

21. **Design FPGA experiments that distinguish architectural hypotheses.**
    Compare static circuits, spatial overlays, temporal overlays, or fabric
    emulation only for a stated experimental purpose. Specify the hypothesis,
    observations, baseline, and measurements before choosing the implementation.
    Separate latency, initiation interval, frequency, and resource use. An FPGA
    experiment cannot by itself establish the physical efficiency of a proposed
    custom chip; there is no assumed universal overlay slowdown.

## Applications that test composition

22. **Derive families of parallel speculative adders.** Use finite carry-function
    representations and scans to connect arithmetic specifications to alternative
    implementations. Compare functional correctness, timing, and cost under
    separately stated contracts. This is a candidate integration application for
    items 6, 18, and 19; implementing it does not require committing the whole
    library to a netlist or FPGA production pipeline.

23. **Develop functional images and graphics realizations.** Start from images
    as functions over space and connect transformations, AD, and regional bounds
    to that meaning. Sampling, filtering, finite precision, and any shader target
    need explicit observation contracts. Retain this as an exploratory application
    of the shared abstractions; a deployable graphics system is separate work.

## Changes to the original recommendations

| Original recommendation | Reconciled disposition |
| --- | --- |
| Prioritize a new frontend and syntax | Deferred. Agents can use typed constructions directly. |
| Build a typed visual editor or Eros-style environment | Deferred with human-facing frontend work. It is not a prerequisite for the library. |
| Port Type Class Morphisms as its own workstream | Fold applicable principles into items 1 and 2. |
| Port Compiling Embedded Languages and smart constructors | Reconsider the algorithms through proof-indexed implementations in item 5. |
| Require a shared graph middle end | Withdrawn as a universal requirement. Graphs remain optional representations in items 5, 18, and 20. |
| Start with machine words, global cycles, registers, and protocols | Move these choices to selected realizations and external interfaces. |
| Treat rational time as an implementation expedient | Retain its existing mathematical role; generalize assumptions and add real-time semantics in item 11. |
| Treat approximations as the semantic meaning | Use exact meanings with explicit, compositional observation/error contracts in items 3 and 10. |
| Proceed directly from adders to RTL to a temporal FPGA overlay | Replace the prescribed product sequence with research and experiments in items 16 through 21. |
| Limit general differentiation to a practical polynomial extension | Retain completion of general differentiation as a major objective, and add integration. |

## Issue boundaries and ordering

Items 1 and 2 already have tracking issues. Each of items 3 through 23 is a
candidate substantive issue; broad topics should first establish a research or
planning deliverable and then acquire implementation children. Their numbering
identifies scope, not execution order. The deferred frontend and editor do not
need implementation issues in this round.

Architectural parity is the first implementation milestone. Calculus and temporal
research can proceed independently, with implementation using the resulting
shared foundations. Hardware experiments follow a stated hypothesis and an
adequate semantic model. Interoperability work follows selection of an actual
external target. Small contrasting examples should inform those choices before
a product pipeline is adopted.

When filed, each issue should identify its specification, unresolved choices,
deliverables, dependencies, and checked applications. Research tasks need a
concrete comparison or decision as their outcome. Implementation tasks need
statement review, checked specializations, and the applicable build and axiom
audit. This list does not assert that the proposed general constructions already
exist or that every research question has a positive answer.

The timing extension must reconcile [ADR 0008](adr/0008-timing.md), which selects
rational time for the existing development. Calculus extensions must preserve
the distinctions and explicit hypotheses in [ADR 0003](adr/0003-ad.md).
Enclosure work must preserve the soundness/equality distinction in
[ADR 0007](adr/0007-incremental-and-enclosure.md). Any incompatible implementation
decision needs an explicit ADR revision rather than an implicit scope change.
