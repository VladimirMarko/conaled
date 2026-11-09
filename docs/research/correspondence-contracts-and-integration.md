# Correspondence contracts and integration with existing transport

Ownership update: #193 is closed and supplies completed measured-execution
evidence. Historical assignments to #193 below are not an active work queue;
use the [current residual-owner map](workstream-status-reconciliation.md) for
new resource, runtime and error-comparison work.

The first follow-up priority is [#231](https://github.com/VladimirMarko/conaled/issues/231):
generalize preservation laws demonstrated by the compiled FRP lifecycle and
an existing interaction consumer. The [FRP follow-up record](frp-runtime-follow-up.md#preservation-laws-to-reuse)
links the checked results, clock and information-loss counterexamples, and
coordination with resource and durability work. Reuse existing relational
squares and requirement transport before introducing another interface. This
priority leaves the broader correspondence programme open.

The [boundedness and compositional-guarantee assessment](compositional-guarantees-and-boundedness.md)
compares the same preservation structure across resources, optimization,
productivity and durability. It distinguishes relational predicate transport
from quantitative composition, uniform resource bounds, progress witnesses and
crash observations. These are consumers for #231's experiment; the assessment
adds no public abstraction or new Lean theorem.

The [implemented-contract inventory](preservation-contract-inventory.md) is the
broader compatibility checklist for that experiment. It includes probability
laws, derivatives, enclosures, causality, ordering and witness identity,
dependent substitution, symmetry and descent. The first runtime clients must
not define the boundary of the family. Existing STLC naturality and structure-law
transport are reusable foundations alongside predicate transport.


Research for [#202](https://github.com/VladimirMarko/conaled/issues/202),
2026-10-28. Source inspection baseline:
`441f618a044c040adaeb85acace27e76cdc68f57`, Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The original text is a research-phase integration
proposal; it records the declarations and planned tests at that baseline.
The implementation update below identifies the subsequent formal results.

**Implementation status:** the research baseline and proposed tests below are
retained as a dated design record. The
[compiled temporal-payload experiment](compiled-temporal-payload.md)
now supplies X1's same-horizon relation, compiler-to-batch lifting, honest FRP
terminal map, positive/negative cases and authored-content accounting.
The [proof/program bridge](curry-howard-implementation.md),
[temporal adapter](../temporal-frp.md), [shared FIFO client](abstract-fifo-client.md),
[public cost contract](modular-fifo-costs.md) and
[path coverage report](path-correspondence-coverage.md) provide the other bounded
consumer evidence. The [result index](curry-howard-correspondences.md#results-of-the-bounded-experiments)
collects their exact scopes. None establishes a universal correspondence calculus
or a measured reduction in development time.

**Keep cooperating fragments, connected through their existing semantic
interfaces.** The common requirement is a translation with a specified
comparison and composition law. It is not a common datatype for every proof,
program, model, clock and path. Exact squares, relations, categorical model
maps and indexed transport already implement different parts of that contract.
The next additions should connect concrete consumers without replacing them.

The [atlas](logic-correspondence-atlas.md) supplies the range of connections.
The [temporal assessment](temporal-logic-frp-contracts.md) selects a next/until
certificate fragment and an FRP observation contract; the
[Harper assessment](harper-methods-and-adaptation.md) selects shared-client and
private-potential experiments. Their implementation reports distinguish subsequent results from the
declarations inspected at this research baseline. The
[language direction](../language-direction.md) requires familiar author-facing
constructions, explicit requirements, and an unchanged ordinary Lean path.

## Existing contracts and their limits

| Interface inspected | What can already be reused | What it does not establish |
|---|---|---|
| [Compiler](../../Compiler.lean): `Term`, `Target`, `Sound` | Intrinsically typed syntax, primitive-parametric interpretations and Set-valued semantic preservation. The base type has one atom, whose interpretation varies. | A universal syntax, arbitrary categorical faithfulness, operational simulation, or a smallest set of assumptions. Its semantic beta/eta equations are not syntactic normalization. |
| [STLCNaturality](../../SquareKit/STLCNaturality.lean): `Model`, `ModelCongr`, `Preserves`, `naturality`, `preserves_comp`, `naturality_comp` | For all current terms/contexts, local operation and primitive obligations yield interpretation preservation. Composing preservation packages needs no new syntax induction. `compile_ofTarget` retains compatibility with the original API. | This full-language `Model` contains operations even if a particular term does not use them. It does not make an arbitrary matrix backend closed or supply a translation between different source grammars. |
| [CategoryMap](../../SquareKit/CategoryMap.lean), [CartesianMap](../../SquareKit/CartesianMap.lean), [OptionalMap](../../SquareKit/OptionalMap.lean) | Operations, `HomEquiv`, `MapLaws`, reflection, comparison arrows and inverse/operation laws are separate. Product/closed comparisons allow chosen objects to differ. | `Comparison` alone is only a pair of arrows. Invertibility requires `ComparisonLaws`; transport of source laws can additionally require reflection. `HomEquiv` is not a directed cost order. |
| [Squares](../../Squares.lean): `compose`, `vertical`; [Relations](../../SquareKit/Relations.lean): `RelSquare`, `compose`, `ofSquare`, `witnessSquare`, `witness_compose` | Horizontal composition; vertical pasting with an explicit middle equality; exact-to-relational embedding; compositional presentation on total relation witnesses. | A `RelSquare` preserves a relation without totality, reflection or bijectivity. Its witness space retains the semantic value as data; the construction is not an erasure theorem or extraction from `Prop`. |
| [STLCRelations](../../SquareKit/STLCRelations.lean): `Encoding.arrow`, `Primitives`, `compile_preserves` | Higher-order relations quantify over all related inputs. Primitive obligations lift through the entire current source. | Proof-relevant parametricity, arbitrary effects, or cost noninterference for unrestricted Lean functions. |
| [Internal Logic](../../SquareKit/Internal/Logic.lean): `formula_subst`, `Derives`, `sound`; [PathTransport model](../../SquareKit/Internal/PathTransport/Model.lean), [contextual model](../../SquareKit/Internal/PathTransport/ContextualModel.lean) | Regular formula substitution/validity, plus separate dependent context, family, section and substitution operations. `Telescope.reindex` and contextual identity machinery retain dependency. | `Derives` lives in `Prop`; it is not a freely inspectable computational derivation. The dependent model is a specified fragment, not every dependent type theory or a model of all Lean. |
| [SourceReindex](../../SquareKit/Internal/PathTransport/SourceReindex.lean): `transport_code_reindex`; [SourceSemantics](../../SquareKit/Internal/PathTransport/SourceSemantics.lean): `transport_obj`; [GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean): `Route.transport`, `reindex_comp`, `comp_assoc` | Source transport interpretation and substitution evidence already exist. A base functor and natural fibre map preserve transport, including arrow action. | The route interface itself does not translate arbitrary source syntax. Set-valued fibres over a category are not a univalent universe or arbitrary higher-identity semantics. |
| [ClassifierSourceChange](../../SquareKit/Internal/ClassifierSourceChange.lean), [ClassifierSourceCoherence](../../SquareKit/Internal/ClassifierSourceCoherence.lean) | `sourceModelFunctor`, `classifierSourceIso`, `sourceModelCompIso`, associativity and unit comparisons for the complementary-predicate classifier. | This is concrete evidence for coherent comparisons, not a generic coherence theorem for every indexed model. |
| [RelationTransport](../../SquareKit/RelationTransport.lean): `image_requirement`, `image_comp`, `requirement_comp` | Forward existential images and backward universal requirements form a Galois connection and compose in the appropriate order. | No existence, fairness, knowledge of reachability, or executable weakest-precondition solver. |
| [Progress Evaluation](../../Applications/Progress/Evaluation.lean), [Processors](../../Applications/Progress/Processors.lean), [Elaborator](../../Applications/Elaboration/Elaborator.lean) | `Evaluates` and fuel search separate admissibility from finding evidence; processors retain input demand; `Elaborates` separates fidelity, obligations and typing. | Bounded elaboration completeness is relative to its annotated fragment and overload policy. Demand-relative causality is not automatically synchronous no-lookahead. |

These are source-inspection findings, not a fresh build. Accepted
[#130](https://github.com/VladimirMarko/conaled/issues/130) includes witness,
dependent-data, first/second-identity, finite-universe and finite-prefix stress
tests. [GroupoidRoutes](../../Examples/GroupoidRoutes.lean) already compares a
source transport with composed routes and retained labels; `not_constant`
shows that equal fibre cardinalities do not imply a constant family.
[ConstantSheafStreams](../../Examples/ConstantSheafStreams.lean) already
separates finite-prefix preservation from a full-stream comparison.
[#131](https://github.com/VladimirMarko/conaled/issues/131) includes the accepted
bounded evaluation/productivity and elaboration contracts. Repeating these
examples under a new generic name would not establish integration.

## What organizational tools contribute

These source results justify vocabulary and candidate interfaces. They do not
supply Lean implementations of the proposed adapters. Versioned links pin the
surveyed text; other primary copies were checked on the research date.

| Tool and primary source | Exact useful structure or result | Fit and additional obligations |
|---|---|---|
| Logical frameworks: [Harper–Honsell–Plotkin, LF, encoding/adequacy sections](https://homepages.inf.ed.ac.uk/gdp/publications/Framework_Def_Log.pdf) | Dependent types encode judgments and binding; adequacy relates canonical inhabitants to intended object derivations. | Adopt adequacy and substitution as obligations for each encoding. A shared judgment representation does not prove that two encoded logics interpret each other, preserve reduction, or retain computational witnesses. Reuse Lean's existing host rather than require LF as another kernel. |
| Doctrines: [Lawvere, *Adjointness in Foundations*, 1969, author-commented 2006 reprint](https://tac.mta.ca/tac/reprints/articles/16/tr16.pdf); [Seely, *Hyperdoctrines, Natural Deduction and the Beck Condition*, 1983](https://www.math.mcgill.ca/rags/ZML/ZML.PDF) | Context-indexed predicates/proof objects, substitution by reindexing, and quantifiers by adjoints. Beck conditions express compatibility of these adjoints with suitable base change. | Useful for logical validity and substitution-sensitive quantification. Specify the fibres and which adjoints exist; a posetal fibre forgets distinguishable proofs. Indexed categories can retain more data, but computation and causal observations need extra structure. Existing internal models should be adapters/instances, not discarded. |
| Categories with families: [Dybjer, *Internal Type Theory*, TYPES '95 proceedings 1996, §§2–4](https://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf) | Contexts/substitutions, indexed types/terms and comprehension provide a syntax-oriented categorical account, also expressible as a generalized algebraic theory. | Compare the local `StructuralModel` to the needed fragment before adding a competing CwF structure. Identity, universes and reduction are added operations/laws; the bare interface does not supply them. |
| Coherence: [Lumsdaine–Warren, *The Local Universes Model*, v2, 2015, Theorem 3.4.1](https://arxiv.org/pdf/1411.1736v2) | Under the paper's condition (LF) on a full comprehension category and weakly stable specified constructors, the local-universes construction gives a split model with strictly stable constructors. | A possible route from weak semantic stability to strict syntactic substitution. It is not a blanket strictification theorem for arbitrary effects or higher structure. First exhibit the hypotheses and the required constructors; no reconstruction of this theorem is proposed for the initial adapters. |
| Institutions/comorphisms: [Goguen–Roşu, *Institution Morphisms*, 2001 report, Definitions 11 and 23](https://ntrs.nasa.gov/api/citations/20010097127/downloads/20010097127.pdf) | Signatures, sentences, models and satisfaction invariant under signature change. A comorphism translates source signatures/sentences forward and target models backward, with a satisfaction equivalence. | Useful for heterogeneous specification and model checking. The sentence/model contract has no derivation datatype, reduction, execution cost or online strategy. Do not confuse its satisfaction equivalence with a compiler's one-way simulation or source-model coverage. |
| Multimodal presentations: [Gratzer–Kavvos–Nuyts–Birkedal, MTT, v3, 2021, §§2,5–7](https://arxiv.org/pdf/2011.15021v3) | A small strict 2-category specifies modes, modalities and transformations. The paper proves canonicity; suitably functorial dependent right adjoints induce models. | Promising when several actual modal interfaces must interact. Modality symbols alone do not supply FRP fairness, a physical clock, cost sealing, or a safe equation between next and guarded later. Keep mode equations and their interpretations explicit; the first next/until experiment needs less machinery. |
| Phase-sensitive parametricity: [Sterling–Harper, LRAT, v3, 2021](https://arxiv.org/abs/2010.08599v3) | Proof-relevant, phase-sensitive parametricity for a specified module calculus, with gluing and a lax modality for effects/generativity. | Supplies a target modularity property for #210/#211. Existing `compile_preserves` remains the starting point. A theorem for an operation-only client is a bounded reconstruction, not adoption of the complete module metatheory. |

A comorphism's equation can be written, for a source sentence `φ` and target
model `N`, as `β(N) ⊨ φ ↔ N ⊨ α(φ)`. To infer source validity from target
validity one still needs enough target models to cover the relevant source
models, or another conservativity argument. This is a consequence of the
quantification, not an extra theorem provided by naming a map a comorphism.
Similarly, preserving a typing judgment does not establish faithfulness of
its denotation. This proposal keeps these checks separate.

## Three route contracts to compare

The notation below describes obligations. It does not declare a new universal
Lean `Route` type or identify objects from different fragments.

| Field | Cartesian proof/program | Temporal certificate/FRP | Dependent/path-sensitive |
|---|---|---|---|
| Source and target judgments | Product/arrow natural deduction `Γ ⊢ A` with retained terms; existing typed `Term Prim Γ A`, then a chosen model arrow | Time-labelled `Γ ⊢[n] A` in the selected atom/unit/product/next/until fragment; a finite `Until` witness, then delivery/value observations | A bounded contextual source transport term; interpretation as a section, then transport in a family `B : C ⥤ Type` |
| Translation and substitution | Proof-to-term and simultaneous substitution must agree; semantic model change uses `naturality` | Substitution keeps absolute time labels. Interpret next at `n+1`; until retains a finite horizon. Map atomic witnesses pointwise, without silently reindexing time | Existing source reindexing and interpretation lemmas connect to family precomposition; `Route.reindex` changes the base along a functor |
| Comparison | Exact term round trips for the selected presentation, then semantic `HomEquiv.Rel` or a logical relation on values | Evaluation produces a certificate; search provides actual horizon/payload data. `responseSquare` compares an emitted list with source truth under honesty | Naturality equation `r_y(B(p)b) = A(F(p))(r_x b)`; preserve base arrows as well as fibres |
| Computation/equality | Beta/cut simulation is an additional operational theorem. Denotational equality does not prove normalization | Constructor/fold equations and substitution soundness; no general recursion or full LTL completeness. Equal final lists do not imply equal horizons | Chosen source equality, propositional transport comparisons, and explicit arrow/2-cell data are different levels; no host equality reflection |
| Erasure and assumptions | Erasing a proof wrapper may retain its term; mapping all terms to one denotation loses distinctions. Primitive preservation is required | Forgetting horizon or payload destroys constructive arrival evidence. Fairness/available closing prefixes justify conditional existence; causality is separate | Orbit sets erase labels/stabilizers. Native `Eq` cannot replace distinguishable higher witnesses; constant fibre size does not remove monodromy |

At this baseline #203 and #206 are **in progress**. The #203 implementer reports
an admissibility-restricted wrapper over the existing intrinsic term tree,
identity round trips, binder-aware substitution, and beta/projection reduction
as the intended bounded interface. This is not an accepted declaration inventory.
The #206 implementer reports `Until` constructors, horizon/fold/map laws,
a time-labelled interpreter and an executable arrival search as intended APIs;
conditional existence remains `Nonempty` in `Prop`. These names and proofs are
not frozen. This proposal relies on the accepted #205 specification. Update it
to reviewed public names after integration.
The dependent/path column already has checked bounded evidence under #130;
#213 owns further higher-identity work, not reconstruction of existing routes.

A substructural extension would change the first column's context discipline.
An unrestricted diagonal `x ↦ (x,x)` cannot simply be forwarded to a linear
context lacking contraction. The atlas's S1–S3 give representative source
systems; no linear adapter is inferred from the word “linear” in matrix algebra.

## Composition: equality, relations, and coherent comparisons

For functions and a specified observational equality, exact squares can paste
when their middle arrows match. `Squares.vertical` already accepts an explicit
extensional equality there. For relational squares, each stage preserves the
same chosen intermediate relation; `Relational.compose` then composes the two
proofs. Changing that relation needs a separate inclusion/adapter theorem.
Totality cannot be recovered from a relation that happens to be preserved.

For model maps, `preserves_comp` uses the second map's congruence to carry the
first comparison through it before composing comparisons. This is why a plain
function on representations is insufficient. With changed products or closed
objects, use the existing comparison arrows and their laws; do not demand
that independently chosen model objects be definitionally identical.

For indexed models, substitution may commute only through specified
isomorphisms. Retain their naturality, associativity and unit diagrams.
`sourceModelCompIso` and `sourceModel_associativity` are an existing bounded
example. By contrast, the chosen `GroupoidTransport.Route` composition is
strict in its present representation. Neither fact settles all future models.
A noninvertible refinement comparison cannot be passed to an adapter requiring
an isomorphism, and an equality proof cannot stand in for retained path data.

A schematic preservation contract is

```text
J(source)  --translate-->  K(target)
   | interpret                 | interpret
   v                           v
semantic source --map--> semantic target
                 comparison
```

Record the actual types, comparison direction, and equations for each instance.
A proof of this diagram alone supplies none of reflection, definability,
extraction, full abstraction, termination, cost bounds or causal execution.
Each stronger result needs a named theorem and its own hypotheses. Effects may
also change the valid equations: unrestricted beta substitution is not a
license to duplicate stateful or resource-consuming computations.

## Forward guarantees and backward requirements

For a relation `r : X → Y → Prop`, the existing contracts are

```text
image r P       = { y | ∃ x, P x ∧ r x y }
requirement r Q = { x | ∀ y, r x y → Q y }
image r P ⊆ Q  ↔  P ⊆ requirement r Q.
```

Under this partial-correctness interpretation, `requirement r Q` is the largest
admissible input set ensuring all related outputs satisfy `Q`. This is an exact
mathematical weakest liberal precondition. It does not compute a formula in an
arbitrary source logic. An empty relation satisfies every universal postcondition;
progress additionally needs output existence or the appropriate delivery contract.
`requirement_comp` propagates requirements backward through the composed relation.

For FRP, retain separate assumptions for legal source consumption, fairness,
available closing prefixes, enabled consumer processing and honest source
windows. A value comparison can need honesty without a progress proof needing
it. No automatic rule turns one condition into all the others. In an interactive
system, the environment strategy and observation order are also part of the
relation; a relation on final values alone can omit them entirely.

Requirements can be handled at several levels:

- **Declared:** primitive meanings, context use, clock discipline, invariants,
  relation/observation, and semantic assumptions. Model packages can carry
  reusable proofs that these are satisfied.
- **Collected from selected syntax:** which constructors/primitives a term uses,
  and the obligations generated by a bounded elaborator. This is a conservative
  description of that presentation, not semantic minimization.
- **Discharged by existing evidence:** composition laws, preservation packages,
  instances and explicit lemmas. The elaboration work already separates admissible
  solutions from the algorithm that finds them.
- **Not promised:** discovering the weakest categorical structure, synthesizing
  all fairness assumptions, deciding realizability, or proving two arbitrary
  programs extensionally equal.

Do not add a second requirements language until two consumers need to exchange
its results. The initial adapter signatures can expose ordinary Lean arguments.

## A composed route across program and temporal meanings

The following is the proposed integration test **X1**, not a checked theorem.
It composes a cartesian program interpretation with a temporal witness and
an external value observation. It uses #203/#206 results once accepted.

1. Choose the product/arrow term `λf. λx. f (f x)` over the single base
   atom, and supply related input endofunctions in two interpretations. Existing
   relational compilation yields resulting functions `gR`, `gS` and a relation
   `E` with `∀ x y, E x y → E (gR x) (gS y)`. A scalar example uses `Nat`
   and successor as the supplied function, not as a new logical rule. No new
   multi-atom type syntax is needed.
2. Lift that relation to lists by `List.Forall₂ E`. This establishes the
   relation between mapping `gR` and `gS` over related payload batches.
3. Reuse #206's finite delivery witness. Define a relation between two until
   certificates that requires equal horizons, pointwise-related wait evidence,
   and related terminal lists. Lift the list map to terminal witnesses and
   prove that it preserves this relation. Do not reduce this to `Nonempty`.
4. Under `traceRep`, connect the terminal emission to the ordered source-truth
   batch through `Demand.responseSquare`. In the equality specialization `gR = gS = f`,
   the output is exactly `List.map f (truth left t ++ truth right t)`.
   The certificate retains its original horizon; mapping a batch does not
   establish a physical deadline or a host-runtime cost bound.
5. Compose two source functions and show that mapping after composition agrees
   with the two witness transformations, using the compiler and witness map
   composition laws. Compare the direct ordinary Lean consumer with the
   optional syntax-based consumer in the same example file.

Test zero waiting, a nonempty delayed batch, and known-empty delivery. If the
first relation identifies two different payloads, the result is relational
preservation; do not assert exact equality or a reverse map. A negative test
must forget the horizon and show that equal terminal batches cannot determine
whether arrival was immediate or delayed. A separate future-reading stream
map may preserve total stream values while failing the no-lookahead condition;
it must not pass as an online realization of this route.

This test shares a relation-lifting proof and composition, not a common syntax.
A theorem specialized only to identity maps or a closed concrete trace would
not demonstrate the proposed reusable interface.

## Minimal additions, migration, and validation ownership

| Proposed addition | Existing interface and placement to prefer | Cost and acceptance boundary |
|---|---|---|
| Product/arrow proof-program bridge | #203, existing `Term` and model interpretations | Add substitution/reduction correspondence beside the source; retain ordinary compiler APIs. No migration of other fragments. |
| Time-indexed witness adapter | #206, existing Demand/Progress APIs | Retain horizon and payload in `Type`, prove map/substitution laws; existing FRP clients keep their interfaces. The certificate interpreter and online consumer stay separate. |
| Cross-kind witness relation/composition X1 | Small integration module after #203/#206, using `RelSquare`, list relations and temporal maps | Add only the relation lifting demonstrated by two interpretations and composed functions. No global route registry, automatic translator or new kernel axiom. |
| Abstract client plus public cost contract | #210/#211, existing squares, workloads and potential lemmas | Hide representation and potential from the client theorem; retain ordered costs and initialization credit. Cost erasure is not an unrestricted parametricity theorem. |
| Indexed comparison adapter when required | #213 and existing source/groupoid coherence | Preserve arrow/fibre observations and substitution. Do not replace source-specific equality/coherence by a single cast or erase 2-cells. |
| Requirement/observation comparison | Existing `RelationTransport`; #196/#193 consumers | Propagate a selected partial-correctness predicate; keep progress, faults and resource assumptions separately. New syntax or inference is deferred. |

A common IR remains useful for a selected backend or source family with proven
translations. #128 owns source-to-core artifact and checker contracts. It does
not follow that temporal certificates, path labels and measured executions must
all become its core terms. Cooperating fragments require explicit adapters but
preserve their useful distinctions; a common IR shifts that burden to encoding,
adequacy and observation theorems. The proposal selects cooperating fragments
for these tests and leaves backend-specific IR choices open.

### Caller obligations to measure

These were the prospective acceptance measurements. The linked implementation
reports now record authored constructions and residual obligations; they do not
claim a measured improvement in developer time.
Count independently authored constructions/proofs and residual bookkeeping,
not just lines of code. Count a reused theorem once even if instantiated twice.

| Test | Mathematical content the caller should author | Reusable implementation work | Residual obligations to report |
|---|---|---|---|
| #203 two models | One product/arrow proof/program | Proof/term conversions, substitution, model naturality | Primitive preservation per model; any manual variable indices, casts or admissibility annotations |
| X1 temporal payload transformation | One scalar function and one intended delivery observation | List/witness lifting and composition | Relation on payloads, clock alignment, source honesty/progress premises, any extra interpreter wrappers |
| #210/#211 shared ADT | One operation-only client theorem and public budget statement | Representation simulation, resource fusion and private potential accounting | Per-implementation operation proofs, initial credit, any representation facts leaking into the client |
| Path route | One transport construction and an arrow-sensitive observation | Existing source interpretation/reindexing and naturality | Model-specific fibre action and coherent comparisons; unsupported higher identity |

The baseline is the existing direct client, not a deliberately cumbersome new
encoding. The X1 report now counts its shared source proof, scalar obligations,
relational adapter and index transports; the FIFO reports identify the single
client theorem and per-implementation obligations. Ordinary Lean applications
remain available. These structural counts do not measure development effort.

### X1 implementation and original follow-up contract

The original child scopes did not own their joint relational integration test.
The [implementation report](compiled-temporal-payload.md) now records the
checked route and its author obligations. The original follow-up contract was:
[#215: Compose compiled payload relations with finite temporal delivery witnesses](https://github.com/VladimirMarko/conaled/issues/215)
tracks this follow-up under #202, blocked on the accepted #203/#206 interfaces.
Its deliverables are the five X1 steps, a reusable same-horizon witness relation,
identity/composition laws, equality and nonfunctional-relation specializations,
and the delayed/known-empty/forgotten-horizon negative cases. Require one direct
and one optional syntax client, an authored-content/bookkeeping comparison,
statement review, checked examples, fresh build/audit and independent review.
Place reusable lemmas with their owning libraries and the cross-kind application
in `Examples`; do not require a universal route datatype. No integrated-validation
claim is made before that issue passes. Its compiled payload carriers are
restricted to `Type` (universe zero), matching the current compiler; the
standalone until-certificate relation may remain universe-polymorphic.

## Coordination and decisions left open

The following scope boundaries use issue bodies read on 2026-10-28:

| Owner | Integration constraint |
|---|---|
| [#8](https://github.com/VladimirMarko/conaled/issues/8) | Reuse categorical maps and law transport; this note neither re-audits all Felix parity nor replaces its pinned inventory. |
| [#36](https://github.com/VladimirMarko/conaled/issues/36) | Optional internal reasoning, multiple settings and unchanged ordinary clients. Do not take ownership of the #107/#108 independent repair/retest. |
| [#109](https://github.com/VladimirMarko/conaled/issues/109) | Recursion/iteration needs its own fixed-point, productivity or operational assumptions; it is not inherited from composition. |
| [#128](https://github.com/VladimirMarko/conaled/issues/128) | Preserve intended-source fidelity, actual emitted artifact, target typing and execution trust as separate claims. |
| [#177](https://github.com/VladimirMarko/conaled/issues/177) | Resource contracts and persistent-use assessment own cost-model choices; a single linear trajectory does not justify duplicated credit. |
| [#193](https://github.com/VladimirMarko/conaled/issues/193) | Actual FRP/numerical transition instrumentation must preserve failed/rejected attempts. Equal values do not imply equal work. |
| [#196](https://github.com/VladimirMarko/conaled/issues/196) | Interaction/fault/recovery contracts need admissible environments and observation spaces. No universal fault monad follows from the relation interface. |

Remaining design questions concern evidence from these consumers: whether a
shared indexed client interface earns its cost, which comparison data must be
proof-relevant, and whether repeated modal interactions justify an MTT-style
presentation. The initial tests can answer these without forcing a global
choice of logic framework or IR. Existing semantic composition and the bounded X1 cross-fragment integration
are delivered. Its implementation report records actual construction and
obligation counts. General author-effort savings, a shared indexed client
interface and a global modal presentation remain unestablished.
