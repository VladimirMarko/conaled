# Construction and observation after the integration experiments

Ownership update: #193 is closed and supplies completed measured-execution
evidence. Historical assignments to #193 below are not an active work queue;
use the [current residual-owner map](workstream-status-reconciliation.md) for
new resource, runtime and error-comparison work.

The workstream has established a reusable method: specify a meaning and its
observations, prove local interaction laws, and derive preservation for compound
constructions. The latest work connects equation views, indexed composition,
exact rewriting and observation extension. It also constructs guarded solutions
and a higher-order logical comparison, and gives explicit retention and
normalization implementations with limited cost results. These are reasons to
retain and reuse the work. They do not yet supply the all-model extension,
dependent coherence or requirement-discovery capabilities assigned to
[#288](https://github.com/VladimirMarko/conaled/issues/288),
[#289](https://github.com/VladimirMarko/conaled/issues/289) and
[#290](https://github.com/VladimirMarko/conaled/issues/290).

The recommended next step is to use these results as reference clients and
failure cases for those programmes. Keep their initial tasks independently
executable, and keep alternative foundations eligible for comparison. A new
umbrella or a repeat of completed experiments would add little. The unfilled
connections have owners in the existing issue graph.

## Evidence and scope

This assessment inspected source at
`ff942508e8d1c0052f5cdc638f93a2b84a843a52` on 2026-11-04, the linked research
records, and the issue bodies and completion comments. It covers #256,
#266–#271, #273–#279 and #281–#285. The independent external discovery in
[#280](external-discovery-assessment.md) and paper comparisons in
[#286](proof-requirement-comparison.md) and
[#287](representation-extension-comparison.md) supply context. This is a
synthesis of that evidence, not a new breadth survey or a formal implementation.

Here, a **checked result** means a declaration inspected in integrated Lean
source with recorded earlier acceptance. No Lean build or proof audit was rerun
for this assessment. The
[#274 acceptance](https://github.com/VladimirMarko/conaled/issues/274#issuecomment-6630415739)
records the 968-module build/audit at `4792d16`; the
[#281–#285 integration](https://github.com/VladimirMarko/conaled/issues/285#issuecomment-6638778821)
records the 986-module build/audit at `2556ead`, with independent Standards and
Spec review. The
[#284 record](https://github.com/VladimirMarko/conaled/issues/284#issuecomment-6638777837)
also reports a separate fresh check. These are historical validation records,
not a new verification receipt for this documentation change. Paper calculations,
external theorems and recommendations below have separate labels.

## Completed issue inventory

All issues in this table were closed in the inspected tracker snapshot. Their
completion does not close the broader questions listed in the last column.

| Issue | Delivered evidence | Retained boundary |
| --- | --- | --- |
| [#256](https://github.com/VladimirMarko/conaled/issues/256) | Checked indexed equation expressions, two presentations, exact syntax round trips and interpretation preservation in [EquationTranspose](../../SquareKit/EquationTranspose.lean), especially `untranspose_transpose`, `transpose_untranspose` and `transpose_preserves`. | Binding-free cells with supplied total primitives; no equivalence between arbitrary data values and all codata behaviors. |
| [#266](https://github.com/VladimirMarko/conaled/issues/266) | Completed parser rows in [Transposition](../../Applications/Languages/Transposition.lean), and `addConstructors_old` / `addObservers_old` in the shared equation API. [Implementation record](constructor-destructor-transposition.md). | Preserves old cells under unchanged primitive meanings; calling parser primitives does not compile their recursion. |
| [#267](https://github.com/VladimirMarko/conaled/issues/267) | [ObservationExtension](../../SquareKit/ObservationExtension.lean): restriction, compatibility, extension and quotient descent, with [parser/FIFO examples](../../Examples/ObservationExtension.lean). | Exact equality in each fixed result fiber; neither arbitrary dependent descent nor all-model theory extension. |
| [#268](https://github.com/VladimirMarko/conaled/issues/268) | [CompositionalCoalgebra](../../SquareKit/CompositionalCoalgebra.lean): local compatibility, fold and substitution morphisms; [weighted recovery](../../Applications/Languages/Compositional.lean) preserves noncommutative order and adds pointwise multiplication. | Ordinary finite terms and a restricted rule format; not the full categorical distributive-law framework. |
| [#269](https://github.com/VladimirMarko/conaled/issues/269) | [Pairing assessment](pairing-observation-transport.md), with paper parser/vector pairings and a proposed exact-square adapter. | Research recommendation, not a checked Chu adapter or universal pairing library; changing result fibers needs explicit comparison. |
| [#270](https://github.com/VladimirMarko/conaled/issues/270) | [Producer/consumer assessment](symmetric-producer-consumer-assessment.md), including logic, evaluation-order and indexed-observer obligations. | Paper comparison; no replacement proof calculus, elaborator or measured author benefit. |
| [#271](https://github.com/VladimirMarko/conaled/issues/271) | [IndexedCompositional](../../SquareKit/IndexedCompositional.lean): index-changing constructors, typed paths and compatible substitution; [ordinary recovery](../../SquareKit/IndexedCompositionalOrdinary.lean). | Fixed index base and finite syntax; neither dependent binders nor arbitrary change of base. |
| [#273](https://github.com/VladimirMarko/conaled/issues/273) | [Demand/retention/cleanup assessment](demand-retention-cleanup-assessment.md) separates the contracts and identifies useful comparisons. | Research findings do not establish a universal duality, resource result or thermodynamic conclusion. |
| [#274](https://github.com/VladimirMarko/conaled/issues/274) | [Full finite parser composition](../../Applications/Languages/IndexedCompositional.lean): `cut`, concat/star compatibility, `recovered`, `recovered_tree`, and restriction coherence. | Exact finite observations, including nullable-star witnesses; no retained storage or infinite productivity follows from this theorem. |
| [#275](https://github.com/VladimirMarko/conaled/issues/275) | [Bialgebraic adoption assessment](bialgebraic-semantics-adoption.md), with source hypotheses and proposed discriminating experiments. | Paper investigation; later #276/#284/#285 implement selected alternatives, not every categorical theorem proposed there. |
| [#276](https://github.com/VladimirMarko/conaled/issues/276) | [ExactRewrites](../../Applications/Languages/ExactRewrites.lean): transport identity/fusion and `contextual_exact` under all supported finite contexts. | Semantic equality of exact decisions; no quotient monad, canonical form or optimizer termination proof. |
| [#277](https://github.com/VladimirMarko/conaled/issues/277) | [EquationComposition](../../SquareKit/EquationComposition.lean): `compile_transpose` and `observations`; generated vector rules and a [parser union/scale specialization](../../Applications/Languages/EquationComposition.lean). | Only output-local cells and finite successor templates; general equation tables are not automatically compilable. |
| [#278](https://github.com/VladimirMarko/conaled/issues/278) | [ObservationComposition](../../SquareKit/ObservationComposition.lean) and [vector extension](../../Examples/ConstructorObserverExtension.lean): common-meaning comparison, old-client recovery and explicit cross-cell failures. | Compares completed rules on a common signature; no unconditional theorem that extension orders commute. |
| [#279](https://github.com/VladimirMarko/conaled/issues/279) | [Independent author trials](construction-observation-author-trials.md), with checked [Author A](../../Examples/ConstructionObservationAuthorA.lean) and [Author B](../../Examples/ConstructionObservationAuthorB.lean) clients and archived attempts. | Two supplied-interface tasks; no requirement-discovery result, general human-usability claim or causal speed comparison. |
| [#281](https://github.com/VladimirMarko/conaled/issues/281) | [ClientSchedules](../../Applications/Uncomputation/ClientSchedules.lean): arbitrary finite repetition, independent output, clean release, coherent lifting and specified work/space comparisons. | Peak-workspace comparisons are finite instances; no globally optimal scheduler or physical resource measurement. |
| [#282](https://github.com/VladimirMarko/conaled/issues/282) | [RetainedSnapshot](../../Applications/Languages/RetainedSnapshot.lean): explicit binary tree, exact lookup/restriction and construction-inclusive derivative-call accounting. | Fixed binary alphabet and retained depth; no generic memoizer, finite-state bound or total runtime/memory bound. |
| [#283](https://github.com/VladimirMarko/conaled/issues/283) | [DerivativeNormalization](../../Applications/Languages/DerivativeNormalization.lean): exact outer-transport packing and instrumented derivative/packing counts. | Keeps witness-function compositions; neither state interning nor unconditional performance improvement. |
| [#284](https://github.com/VladimirMarko/conaled/issues/284) | [GuardedStreams](../../SquareKit/GuardedStreams.lean): constructed solutions, uniqueness, reuse and noninjective interpretation transport. | Coordinate-guarded functions on `Nat → A`; no general GSOS/CIA framework or recursive-source compiler. |
| [#285](https://github.com/VladimirMarko/conaled/issues/285) | [HigherOrderComparison](../../SquareKit/HigherOrderComparison.lean): independent function denotation, logical relation, application/binding/substitution and a step-observation obstruction. | Total simply typed fragment; no locally final higher-order domain or general weak/full-abstraction theorem. |

## What the recent integration establishes

**Finite composition now supports demanding native contracts.** In
`IndexedCompositional`, `Rule.Compatible` has separate output and successor
equations. `fold_morphism` proves them for arbitrary finite terms from those
local laws and a leaf morphism. `bind_morphism` and `observe_morphism` then
cover compatible substitution and typed finite observation paths. The parser
specialization retains `Decision (P word)`, rather than a success bit. Its
`cut` operation changes available depth without consuming a symbol, which is
the extra operation needed by retained concat/star operands. The
[source](../../Applications/Languages/IndexedCompositional.lean) supplies native
`sourceCompatible` and `targetCompatible`, then derives `recovered_tree` and
the direct concat/star results. This is demonstrated reuse without a new
whole-term induction or a shared-core redesign.

**The rewrite result is broader than its transport examples.**
`contextual_exact` accepts arbitrary typed holes, repeated or unused, and local
exact agreement at each hole's depth. It uses parser/trie recovery,
`WitnessTrie.ext_lookup` and `Term.fold_bind` to obtain replacement throughout
the supported context. Transport fusion supplies one useful instance. The
[negative example](../../Examples/ExactParserRewrites.lean) keeps recognition
equal while selected sum tags differ, so the result cannot be weakened to
Boolean agreement. This gives a reusable criterion for future transformations
without requiring a quotient representation from every parser caller.

**Equation views and semantic composition now share authored material.**
`compile_transpose` proves equality of the whole generated rule, including
successor templates and their indices. The
[vector specialization](../../Examples/IndexedCompositional.lean) actually
defines its public rule from the equation table; the bridge therefore removes
one independently maintained rule body. `observations` still requires semantic
compatibility with an independently supplied algebra. The
[second-coordinate counterexample](../../Examples/EquationComposition.lean),
`second_coordinate_not_local`, shows why: a child's head cannot determine every
later coordinate. The compiler accepts the restricted `EquationComposition`
signature, not arbitrary existing parser/vector cells. Full equation-row
coverage in #266 and full finite composition in #274 do not imply full coverage
by this bridge. Parser union and scale are its checked common fragment.
The second-coordinate obstruction constrains this immediate-output interface.
A longer observation path or a richer output interface changes the problem;
the counterexample establishes no general limit on language expressiveness.

**Extension composition has a substantive acceptance test.** In
[#278's vector client](../../Examples/ConstructorObserverExtension.lean), the
new shift constructor and sum observer interact through `ShiftSumLaw`.
`correct` covers arbitrary mixed terms; `old_client` reuses the original
coordinate theorem; `embedded_client` retains every old coordinate under the
enriched observation. `order_comparison` follows from both rules satisfying
the same independent vector meaning, via `Rule.compare_observations`.
`failed_sum_law` shows that keeping old cells unchanged cannot validate a wrong
new interaction. Separately, `constructors_no_factor` rules out recovering
syntax-node count from the old coordinate quotient. The successful sum
observer factors through vector meaning, so `enriched_iff` proves it leaves
the old equivalence unchanged. These are different obligations, both checked.
This addresses part of the original concern about brittle extensions: an old
theorem retains its stated contract, and a proposed extension exposes the new
law it must satisfy. It does not eliminate extension work. A new observer that
distinguishes old-equivalent representations can require a richer carrier or a
revised equality, with corresponding client recovery proofs. Making that
boundary explicit helps diagnose a redesign; it is not a reason to forbid one.

**Retention and normalization have moved beyond semantic possibility.**
`RetainedSnapshot.Tree` stores two children as data, and `lookup_build` connects
its exact result to native parsing. `query_restricted` justifies a shallower
view of the same stored tree. `build_work` and `repeated_saves` count initial
construction before claiming a saving. The
[checked workloads](../../Examples/RetainedParserSnapshot.lean) include an
adverse single request. `DerivativeNormalization.normalize_exact` and
`contextual` use the rewrite contract to justify outer-spine packing; its
`deriveCounted_result` connects instrumentation to native derivatives. The
[normalization examples](../../Examples/DerivativeNormalization.lean) show
that a long transported continuation can save modeled work, while a short
continuation or an already simple state can lose. The construction still
composes witness functions, so fewer parser nodes do not establish less total
memory or faster final witness computation.

**Whole-client resource reasoning now includes useful work between uses.**
In [ClientSchedules](../../Applications/Uncomputation/ClientSchedules.lean),
`advance_repeat` lifts a segment contract to every finite repetition and
`correct` proves the independently specified caller output and clean release.
`coherent_reference` retains arbitrary amplitudes with an untouched finite
reference. `low_costs` and `high_costs` distinguish when retention saves gates
at equal peak scratch and when recomputation fits a smaller workspace budget.
`retained_wire_not_available` rejects allocating a retained wire even if its
current value is zero. This strengthens #273's resource comparison without
identifying observation, storage ownership and cleanup as one theory.

**Guarded recursion adds a new construction, not an assumed solution field.**
`GuardedStreams.solve` uses well-founded recursion on the coordinate;
`solve_fixed`, `unique` and `seed_independent` discharge the solution laws.
The later `sumsBody` uses the already constructed `ones`. `map_solution` lifts
a local interpretation square to whole-solution equality without injectivity;
`sums_map` discharges that square using the earlier `ones_map` law. The
[parity example](../../Examples/GuardedStreams.lean) makes the information loss
explicit. `Causal` permits dependence through the current coordinate, whereas
`Guarded` permits only earlier coordinates. `identity_not_guarded` and
`identity_two_solutions` show why causality alone cannot justify uniqueness.
This is a useful reusable semantic component even though #109 still needs a
source grammar, admissibility and compilation interface.

**Higher-order comparison supplies an interface beyond forward carrier maps.**
In [HigherOrderComparison](../../SquareKit/HigherOrderComparison.lean), `D`
and `denote` give ordinary function meaning independently of `V` and the costed
`run`. At function types, `Rel` quantifies over related inputs and relates
their outputs. `comparison`, `application`, `extend_related` and
`substitution_comparison` make that obligation explicit, including under
binders. The module does not supply a total erasure map on arbitrary behavioral
functions. At closed ground type, `weak_iff` identifies result equality with
denotational equality. `no_strong_adapter` proves that step count cannot be
recovered from that denotation: zero and its identity redex have equal meaning
and different costs. This is a useful positive relational comparison and a
precise negative fit result for the stronger observer.

## What the source papers add

The following primary-source checks delimit the inference from the new code to
the earlier adoption recommendations. They inspect the cited definitions,
hypotheses and theorem passages; they do not revalidate every bibliography in
the workstream.

*Presenting Distributive Laws*, Assumption 2.2 and Theorem 4.3, requires
coequalizers in `Alg(T)` and specified functors to send regular epimorphisms
there to epimorphisms in the base. Under its setup, preservation of equations
is equivalent to a unique induced distributive law on the quotient monad;
Proposition 4.10 extends this to copointed functors. #276 proves contextual
semantic replacement directly. It constructs neither that quotient monad nor
its categorical law, so the paper remains a possible generalization when a
quotient client needs it. [Bonsangue et al., v2, §§2 and 4](https://arxiv.org/pdf/1503.02447v2)

*Abstract GSOS Rules and a Modular Treatment of Recursive Definitions* assumes
binary products/coproducts, a terminal behavior coalgebra and free operation
algebras in its standing setup. Theorem 4.8 extends a completely iterative
algebra by an interpreted guarded recursive program scheme; Definition 4.5
includes iteratability and the guard factorization. This supports the broader
modularity ambition. #284 constructs the coordinate instance directly, with
its own guardedness proofs, and does not implement the entire recursive-scheme
apparatus. [Milius, Moss and Schwencke, v2, Assumption 2.1 and §4](https://arxiv.org/pdf/1307.2538v2)

*Towards a Higher-Order Bialgebraic Denotational Semantics* constructs an
adequate algebra from a locally final domain under relative flatness
(Theorem 3.9); adequacy means denotational equality implies behavioral equality
(Theorem 3.11). Theorem 4.13's domain construction requires a stable
M-category, chain limits, variance-sensitive metric conditions, an inhabited
specified hom-set and convergent final sequences. Section 6 leaves the
converse and weak denotational semantics as further work. #285 independently
proves a logical comparison for its total language; it does not instantiate
those domain-existence or higher-order GSOS theorems. Its rejection of exact
step observations for extensional meaning therefore limits this proposed
identification, not every bialgebraic model.
[Goncharov et al., v2, §§3–4 and 6](https://arxiv.org/pdf/2602.18295v2)

The [#269](pairing-observation-transport.md) and
[#270](symmetric-producer-consumer-assessment.md) conclusions remain paper
assessments. Query contravariance and producer/consumer organization are useful
design ideas; the recent implementation supplies no new Chu framework or
symmetric proof calculus. A common mathematical pattern is evidence to
investigate, not a checked translation among all these theories.

Variance recurs without selecting a global subtype relation. #269 transports
queries backward while representations move forward; #285 compares functions
on related inputs. The former's exact pairing equation and the latter's logical
relation have different contracts. Together they support keeping explicit
variance and comparison evidence reusable, as in
[#257](https://github.com/VladimirMarko/conaled/issues/257), while leaving
[#260](https://github.com/VladimirMarko/conaled/issues/260) conditional on its
own matched author tasks and semantic choices. Neither result establishes a
need for global implicit value subsumption.

## Consequences for the three programmes

For **#288 and [#291](https://github.com/VladimirMarko/conaled/issues/291)**,
reuse #267/#278 as concrete local contracts and counterexamples. The gap is
quantification and retained data: a compatible interpretation of chosen vector
operations does not expand every admitted old model, reflect old semantic
consequences or transport arbitrary dependent sections. `ObservationExtension`
allows an indexed family of observations, but each comparison is equality in
one fixed result type; its `descend` has a fixed codomain. That is useful input
to #291, not its coherent-fiber-bijection descent construction.

The exact parser quotient is a good candidate consumer because it can reject
Boolean erasure with an existing selected-witness counterexample. #291 must
still show how it instantiates the frozen many-sorted model fixture, or state
and justify the adapter before designing a certificate. Preserve the distinction
between a selected parser witness, a proposition that some witness exists and a
natural representative selector. #278's common vector carrier adds no new
semantic sorts. The programme's separate coordination with #262 remains
necessary. These conclusions follow from the inspected declarations and
[#291's acceptance contract](https://github.com/VladimirMarko/conaled/issues/291),
not from a new claim that Morita extensions have been formalized here.

For **#289 and [#292](https://github.com/VladimirMarko/conaled/issues/292)**,
keep the dependent study's priority. #271 handles fixed families with requests
whose successor sort is determined by the index and request. Its substitution
maps each leaf to a term of the same index. #285 has simply typed binders with
types generated by ground and arrow, and no type family depending on a term.
Neither addresses the genuinely dependent tail, source annotation or two-step
dependent substitution obligations frozen by #292. These smaller results are
successful cases a redesign should recover, not evidence that the harder
coherence work is complete. Local-universes applicability still needs the
actual model hypotheses and a correspondence back to the generated source
judgments. This assessment changes neither #107's repair nor #108's independent
theorem selection.

For **#290**, the new code provides concrete requirement interfaces to compare
with proposed theory publication and transport. `Compatible`, `ShiftSumLaw`,
`Guarded`, and `Rel` expose different sorts of evidence. In particular,
`sums` requires `Add` and `One` for construction, while `sums_eq` needs
`AddMonoidWithOne` for its independent formula. That is an existing example
where the required assumptions belong to the particular claim. It should not
become a published solution handed to a supposedly unexposed trial author.
[GuardedStreams source](../../SquareKit/GuardedStreams.lean)

[#293](https://github.com/VladimirMarko/conaled/issues/293) still needs its
frozen requirement-discovery tasks and support. #279 supplies a protocol and
evidence about using an already given interface, not about finding that
interface from a concrete proof. [#294](https://github.com/VladimirMarko/conaled/issues/294)
can use the local compatibility law and noninjective stream interpretation as
public comparison evidence when choosing its task. It must retain totality,
logical-rule and equality obligations for any theory view, rather than treating
the presence of a Lean structure as proof of an adequate theory-network
encoding. Each parent still owes its synthesis beyond its children's success.

## Lower-priority studies and promotion decisions

| Study | Evidence contributed here | Recommendation |
| --- | --- | --- |
| [#295 relational transfer](https://github.com/VladimirMarko/conaled/issues/295) | #284 transports through a noninjective coefficient map; #285 uses related function inputs and outputs. | Strengthen the candidate-task inventory, but retain lower priority. Neither result shows that a new relational transfer tool is needed: the present proofs already discharge these clients. Promote when another argument must be reused and repeating its logical-relation proof becomes the concrete cost. Do not claim a Trocq instantiation. |
| [#296 effectful realizers](https://github.com/VladimirMarko/conaled/issues/296) | #278's failed cross-cell law and #285's changed observation contract are useful failure patterns. | Retain the effectful-client trigger. #285 has no effects, so it proves no state/exception ordering, handler or effect-interaction law. |
| [#297 modal contexts/higher identity](https://github.com/VladimirMarko/conaled/issues/297) | Explicit indices and binding environment comparisons preserve distinctions within their fragments. | Retain separate modal and higher-identity comparisons. Simply typed environment extension does not supply context modalities or nontrivial identity transport. |
| [#298 higher-order probability](https://github.com/VladimirMarko/conaled/issues/298) | #285 makes function-input comparison explicit without a universal erasure map. | Keep the random-function and joint-law trigger. Its natural-number/function model supplies no ambient probability model or shared-versus-fresh sampling theorem. |
| [#299 ordered/metric observations](https://github.com/VladimirMarko/conaled/issues/299) | #281–#283 separate exact outputs from modeled resource observations and adverse workloads. | Preserve the distinct numerical error/precision task. Counts of gates or derivatives are not an ordered approximation or metric interpretation theorem. |
| [#300 open-system wiring](https://github.com/VladimirMarko/conaled/issues/300) | #281 has segment composition; #284 supplies a concrete condition for unique stream feedback. | Use these as comparisons when selecting an open-system client. Sequential schedule composition and one guarded recurrence do not establish arbitrary wiring or feedback. |
| [#301 omitted traditions](https://github.com/VladimirMarko/conaled/issues/301) | The tested fragments identify assumptions alternatives could challenge: fixed index bases, supplied interpretations, total functions and explicit syntax. | Retain breadth work and its limit of at most two deeper follow-ups. More local examples do not make this architecture representative of the omitted traditions. |

These are assessment recommendations within the
[approved agenda](language-research-agenda.md). Scheduling remains independent
of mathematical dependency. Existing code makes some comparisons cheaper to
specify; it does not establish that their external alternatives rank below the
current design.

## Author evidence and remaining interface questions

The [#279 protocol](../../experiments/construction-observation-authoring/protocol.md)
and [reports](construction-observation-author-trials.md) establish successful
completion by two independent AI authors under recorded conditions. The vector
task composes supplied constructors and uses the public all-term theorem. The
parser task adds a pair of exact observations and proves its quotient descent.
Both retained the native contracts and rejected Boolean witness erasure. The
shared vector route avoids reproducing the whole-term argument; the direct
parser pair/quotient route is already short. Both facts matter to interface
choice.

The observed failures involved name qualification and unavailable notation or
tactics, rather than a demonstrated mathematical impossibility. The trials did
not ask authors to design a new primitive signature, author #277's equation
cells, discover `Compatible`, or invent #278's cross law. No general claim about
those activities follows from completion. Model/configuration metadata was
partly unavailable, route exposure was not eliminated, and host contention was
uncontrolled. Keep the attempts and assistance record as a baseline; no causal
speed ranking follows from elapsed times.

The unmeasured authoring of equation tables and new interaction laws is a real
question under #235, but it does not yet require a new trial issue. Select an
actual new author task before deciding whether to test that interface, refine a
specialization or compare a competing representation. A future trial should
freeze the interface and use fresh held-out work where needed. It should not
reuse #279 as evidence of #293 requirement discovery or expand #117's separate
surface-comparison boundary. The
[language direction](../language-direction.md#elegance-author-capability-and-language-constraints)
continues to distinguish mathematical quality, Lean encoding and author/tool
capability.

## Priorities, gaps and architectural choice

1. **Adopt the demonstrated contracts and keep their native specializations.**
   Reuse indexed local compatibility, exact contextual replacement, the guarded
   solver and the higher-order relation where their hypotheses fit. Preserve
   ordinary clients and the concrete parser/vector contracts when a broader
   framework is proposed. #271's ordinary bridge shows that recovery can be a
   checked theorem rather than a promise.
2. **Proceed with #291–#294 as discriminating next tasks.** They ask questions
   the completed work does not answer. Record this inventory as evidence in
   #288–#290 and #235; do not reopen #278/#279/#285 or turn the scheduling order
   into new dependencies. A paper alternative may warrant a redesign before
   it has an easy local adapter.
3. **Keep concrete operational follow-ups with their existing owners.** #263
   owns the generic retained-representation integration beyond #282; #109 owns
   recursive-source compilation beyond #284. #174/#193 retain scheduling and
   resource questions. #283's closure costs, workload selection and possible
   larger optimizer remain explicit questions under #235 and any later scoped
   client. These are neither solved by the model counts nor reasons to repeat
   the accepted bounded experiments.
4. **Require a client before adding another shared framework.** General
   quotient laws, arbitrary equation-cell compilation, extension diagrams with
   different signatures and a reusable binding/mixed-variance interface remain
   possible gaps. #235 already owns integration and recovery. The new evidence
   supports recording their exact missing laws there, not creating a parallel
   foundation programme or adopting a universal AST, Chu object or GSOS layer.
5. **Retain independent denotation as a test and keep its scope open to challenge.**
   For #285's total function fragment, exact beta count cannot be recovered from
   function meaning; the source proves that obstruction. A client whose meaning
   includes costs, interaction, divergence, probability or intensional evidence
   needs a different stated contract and its own comparison. The result does
   not require every future observer to forget steps. The new programmes and
   #301 may challenge current semantic choices as well as their Lean encoding.

The remaining universal-foundation question has not been decided by these
experiments. They prove claims in different fragments with different additional
hypotheses: local finite composition, quotient-compatible observers,
coordinate-guarded solutions and a typed logical relation. There is no checked
common theorem subsuming all of them, and the paper assessments have not ranked
all competing traditions. The positive result is more concrete: useful
specializations now share proofs, fail visibly when an intended observation is
lost, and supply stronger tests for whatever architecture the next research
programmes recommend.

## Dependent interpretation follow-up

The [#329 reassessment](bialgebraic-dependent-reassessment.md), inspected at
`701023ce73ff297604fb21f2b6caada9e727c10c`, compares the published bialgebraic
contracts with the newer dependent judgments and constructor admission. The
fixed memo and exact parser/weighted clients supply distinct preservation
requirements. Generic compatibility remains useful; a family/section comparison
that removes repeated proof work is a proposed next test with #325, not a
constructed consequence of higher-order congruence. The report retains the
witness-loss and step-observation failures and specifies recovery conditions
before any replacement of the ordinary/indexed interfaces.
