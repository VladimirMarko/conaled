# Implementation, use and scaling assessment for #362

Recommendation: keep the checked native and shared routes available, but do not
release #358–#361 on a claim of demonstrated architectural scalability. Compare
model-level coherence and relational composition on new problems before
expanding the current client-specific machinery. The strongest reason to retain
the present approach is its explicit connection between native judgments,
compiled syntax and independently specified selected meanings. The strongest
reason to challenge it is that the demonstrated reusable argument still sits
inside a prepared fragment whose typing, quotation and substitution bridges
were built in advance. Their cost across new operations and settings is unknown.

This is an independent initial assessment under the supplied brief. I had no
earlier task conversation or participation in the reported experiments, did not
read the other initial assessments, and did not coordinate conclusions. Fresh
context does not establish model diversity. The repository evidence baseline is
`5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`; source inspection used `git show`
at that commit. External sources were accessed on 2026-11-08. I read the
architectural standard, language direction, glossary, domain guidance and ADRs
0001, 0002 and 0010. No Lean execution, full build, new formalization or benchmark
was performed. Existing success records below are supplied receipts, not checks
rerun for this assessment.

Before assigning roles to modules, the author contract should require an
argument to expose its mathematical assumptions, work in settings with distinct
interpretations of those assumptions, and retain the evidence its conclusion
selects. Changes of context must preserve both the selected witness and its
dependent action. Joint use of extensions must expose interaction obligations.
A declared relational observation must survive representation hiding without
selecting an arbitrary representative. A compiler may inspect representations,
but must carry a separate contract. These requirements do not prescribe an AST,
a set-valued model or a single equality. A successful design must also distinguish
what the framework developer, model builder, extension author and mathematical
client each have to prove.

The inspected sources give the following narrower evidence.

| Evidence at the pinned commit | What is reused | What remains local |
| --- | --- | --- |
| [`DependentBranchSemantics`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/DependentBranchSemantics.lean), `LocalMeaning`, `interpret_transport` | Induction lifts a certificate law for every rule and independently supplied premise value to preservation of every derivation. | The rule model, comparison `m`, local certificate law and hypothesis compatibility. This particular theorem uses judgment-indexed Lean types and functions; it is not by itself the semantics of every mathematical setting. |
| [`DependentPairSharedModel`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Examples/DependentPairSharedModel.lean), `pass_local`, `translate_meaning`, `interpret_expected` | The transport theorem handles arbitrary fragment derivations. An independent `expected` function specifies their selected value. | Each phase uses `Nat` or the same dependent packet as value. The phase distinction changes projection versus splitting; it does not demonstrate reuse in distinct geometric or logical settings. `interpret_expected` also supplies a fragment-specific induction connecting the model to the independent specification. |
| [`DependentPairSharedClient`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Examples/DependentPairSharedClient.lean), `compiled_image` | One theorem connects actual native fullG compilation, target quotation and execution for every source fragment proof. | It covers the generated proof image with provenance. Arbitrary target proofs, a new constructor, and a new semantic provider are separate tasks. |
| [`IncrementalDependentNativeTrial`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Examples/IncrementalDependentNativeTrial.lean) | `generate_append`, `eval_generate`, `selected` and `Ix.typed` already cover arbitrary schedules. Existing native typed substitution and theory transport are reused. | The author constructs arithmetic syntax, source/target executable carriers, native pair typing and conversion, quotation, and replacement lemmas. “Native” does not mean starting without library infrastructure. |
| [`IncrementalDependentCompositionalTrial`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Examples/IncrementalDependentCompositionalTrial.lean) | Existing syntax, code, native typing and `compiled_image` supply the implementation connections. | Schedule/specification connection, syntax substitution under declarations, dependent result-type alignment, and actual code-substitution connection remain author work. `expression_replace` exposes `Expr.lift`, zero weakening and finite argument indices. |
| [`FiniteObservation`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/FiniteObservation.lean), `read_morphism` | A coalgebra morphism preserves a typed path followed by its public decoder. | The morphism hypothesis and the declared observation. It does not automatically establish equality of all hidden-state possibilities. |
| [`RelationalSemanticBoundary`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/RelationalSemanticBoundary.lean) | `client_invariant` hides representations under equality of full possibility sets; selected-witness maps compose separately. | `PossibilityMap` requires exact possibility-set preservation, stronger than forward relational preservation. This is an existing foothold for the proposed hiding test, not evidence that the test is already solved. |

These are real universal results. Once the hypotheses are established, a longer
derivation needs no new preservation argument. The native schedule route also
has this property. Repeating successor/doubling more often would primarily test
generation, elaboration, kernel checking and execution, not marginal mathematical
author effort. Nor do `.source`, `.extended` and `.target` constitute three
independent model constructions merely because there are three phase labels.

The [#357 report](../incremental-dependent-author-trial.md), the two author
outcomes and final wrapper receipts support successful completion in both arms.
The native receipt records exit zero for Attempt05, with source hash
`a70ad60ebd81ea6ca54861aa9a22d1be2d26adcca2f74002415f6e86326c2786`;
the candidate receipt records exit zero for Attempt06, with source hash
`117be324594e0ed4c2b1d2b39b43405283b134dd3804666c8bba47e932eb46d1`.
The receipts are under
[`evidence/baseline/checks/Attempt05`](../../../experiments/incremental-dependent-authoring/evidence/baseline/checks/Attempt05/result.json)
and
[`evidence/candidate/checks/Attempt06`](../../../experiments/incremental-dependent-authoring/evidence/candidate/checks/Attempt06/result.json).
Their recorded acceptance is pending coordinator statement/axiom checks; the
later report records replay and acceptance evidence separately. I inspected
the final clients, outcomes, receipts and failure-log entries, not every archived
attempt in full or every manifest hash.

Reported elapsed author time is approximately 4 minutes 40 seconds native and
4 minutes 2 seconds shared; archived checks are five and six. The shared final
source is longer. The shared arm also receives more prepared support, including
client-specific helpers. Setup development, review and framework construction
were not fully timed. No model/token telemetry or replicated trial is available.
This observation establishes neither an asymptotic author-cost advantage nor a
causal productivity ranking. The rewrite and dependent-normalization failures
are useful evidence of exposed encoding work. They do not prove a mathematical
limitation of either approach.

For future accounting, let `P` be primitive/rule families, `S` genuinely distinct
settings, `E` interpretation edges, `I` explicitly required extension interactions,
and `N` construction size. A useful ledger is framework setup plus model setup
plus operation/setting obligations plus edge preservation plus interaction
obligations plus client work and checking cost. This is a proposed accounting
scheme, not a measured complexity formula. If every operation needs a new proof
in every setting, the ledger has up to `P × S` occupied cells. Shared theorems can
derive many cells from one parametric model construction; they cannot erase
genuinely different semantics. Likewise an interface graph need not contain every
possible pair of settings. Count the actual edges and higher compatibility
conditions; do not assume either quadratic growth or free composition.

Universal composition controls one part of this ledger. It does not bound
certificate size, term normalization, elaborator search, proof-checking memory,
documentation search or maintenance after a primitive changes. Maintenance should
record which declarations are edited, which mathematical obligations change,
which clients break and which modules rebuild. A local repair that forces all
clients to unfold a representation is different from a model-only proof repair,
even if both have the same line count.

Three alternative workflows deserve a matched comparison in their own terms.

* **Model construction through comprehension and local universes.** A model
  builder supplies a full comprehension category satisfying (LF): finite
  products and the specified exponentials along display maps into display maps
  and product projections. Weakly stable supported logical structure then lifts
  to strictly stable structure in the split replacement, by Lumsdaine–Warren,
  Theorem 3.4.1. An author uses the resulting dependent language; routine
  substitution stability is derived at the model boundary. The paper's extension
  discussion is heuristic beyond its proved constructors, and explicitly excludes
  general type-equality rules from that lifting. It does not provide compiled
  code quotation or arbitrary model-map preservation. [Primary source,
  v2, 2015-04-06, §§3.1–3.4 and 4.1](https://arxiv.org/html/1411.1736v2).

  The design hypothesis to test is whether this moves recurring provider
  coherence into one construction without strengthening the client's assumptions.
  It could replace the current dependent model boundary while leaving compiler
  contracts available. Its implementation and checking costs in Lean are
  unmeasured here; absence of a current adapter is not a mathematical objection.

* **Operations and observations through presented distributive laws.** Specify
  operations, equations and a behavior functor; construct the free operational
  law and prove that it preserves the equations. The quotient-law theorem in
  Bonsangue–Hansen–Kurz–Rot §4.1 makes that condition equivalent to existence of
  the compatible quotient law. Its standing §2 assumptions require algebra
  coequalizers and preservation of regular epis to epis by `U`, `TU` and `EU`.
  The resulting law can support bialgebraic reasoning; final semantics additionally
  needs the final coalgebra. [Primary source, v2, 2015-08-05,
  §§2–4](https://arxiv.org/html/1503.02447v2).

  This workflow offers a precise place to test interaction equations and derive
  reusable observation laws. The comparison should count equation-preservation
  work against today's local certificates and repeated client proofs. Extending
  it to the required dependent/higher judgments is an open construction here;
  a first-order success cannot discharge that requirement.

* **Open systems with relational hiding.** Build open algebraic dynamical systems
  by composing boundary interfaces, then hide internal states through the
  steady-state relation. Baez–Pollard's Theorem 23 gives a symmetric monoidal
  black-boxing functor from `Dynam` to `SemiAlgRel`; finite-dimensional real data
  and algebraic vector fields support the semialgebraic claim. It does not
  require unique hidden steady states and does not assert transient behavioral
  equivalence. [Primary source, v5, 2020-09-08, Definition 22 and Theorem
  23](https://arxiv.org/html/1704.02051v5).

  This is a model capability and an alternative composition workflow, not a
  complete dependent-language replacement. Charge construction of this model
  equally whether exposed through current relational boundaries or through its
  native categorical API. The useful question is which route derives exact
  hiding/composition with fewer recurring obligations.

Felix supplies a further check against treating concrete decoders as the only
incumbent. Its pinned comma object contains an arrow between two interpreted
objects, and its morphism stores two component arrows and a commuting equation
under the specified equivalence. This supports comparison of interpretations
without identifying every carrier with one set of values. I inspected
[`Comma/Type.agda` at `6f36d28097db7ea5f5df3263db3e8be08f74e490`](https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda)
alongside the local parity record; this is not a new full parity audit. Keeping
the shared categorical foundation is compatible with replacing a dependent
encoding or adding a different model-construction route.

The smallest useful next comparison is a paper-level obligation ledger for one
dependent transport argument in a family setting and a groupoid-valued setting,
with local-universes and current certificate presentations developed separately.
Only then freeze a bounded implementation/author trial. This prevents a short
client exercise from concealing that one arm received the solution as a helper.
The following proposed tests give independent expected outcomes and ways the
incumbent could lose.

1. **Distinct settings and selected action.** Reuse one argument that transport
   along a composite equals successive transport. In a groupoid-valued case,
   choose two different automorphisms of one object and a dependent family whose
   action distinguishes them; retain the chosen arrow through two reindexings.
   A discrete family case exercises the same argument under its own admissible
   interpretation. Expected outcome: preservation of the selected arrow and
   action, not merely equal endpoints. Negative control: replace the chosen
   arrow by the other automorphism. This must fail where their actions differ.
   Separately test an ineffective action where different arrows have the same
   action: retaining action alone must then fail the witness contract. A method
   requiring each client to rebuild native substitution proofs loses against
   one deriving those obligations once, provided both preserve these contracts.

2. **Independent extensions with a failed joint model.** Use a base theory with
   a selected point `x` and boolean-valued `f`. One separately satisfiable
   extension requires `f(x) = false`; another requires `f(x) = true`. Their
   combined interpretation into ordinary booleans must be rejected. Include
   a compatible pair and a mixed term whose interaction law is not contained in
   either separate extension. Expected outcome: an explicit joint-model or
   equation-preservation obligation. Merely pairing separate certificates fails.
   Add a dependent version only after agreeing on its unchanged witness contract.

3. **Exact relational hiding.** Specify polynomial open-system equations with
   multiple compatible hidden steady states. Independently define the boundary
   relation by existential elimination. Compose through a shared port and require
   equality between the composite's boundary relation and relational composition.
   Compare distinct internal presentations with that same boundary relation.
   Expected outcome: boundary clients cannot distinguish them, while no unique
   internal state is selected. Negative control: a forward simulation that omits
   one permitted boundary behavior must fail exact preservation. The current
   possibility-set boundary may succeed; a forced path/selected-state adapter
   that loses possibilities fails. This test cannot be replaced by arithmetic
   packet equality.

4. **Growth and maintenance.** Vary construction size with fixed operations and
   models; then add genuinely different operation families with fixed models;
   then add settings with fixed theory; finally introduce specified mixed
   extension equations. Report each axis separately. In a later maintenance
   round, change a primitive presentation while keeping its semantics, change
   a model representation, and change the observation contract. Expected outcome:
   representation changes stay behind the declared boundary; stronger observations
   produce new obligations rather than silently reusing an inadequate theorem.
   Measure elaboration and kernel-checking cost separately from author work.

For every arm, retain initial setup and model-development costs, public sources,
allowed helpers, dependency revisions, assistance, failed attempts, elapsed
author time and available model/token metadata. Separate authors implementing
the foundation from authors using it. Use multiple matched tasks and held-out
extensions; preserve native formulations rather than forcing all arms through
the incumbent's certificate API. Record conditional mathematical coverage first,
then agent effectiveness. Human-productivity superiority is not a requirement.

Migration, if later justified, should begin with a bounded dependent provider
and checked recovery of the prior selected results, quotations and observations.
Count the bridge, dual maintenance, changed imports and checking/audit costs.
An apparently small facade may retain a large duplicated proof boundary. A new
host or proof importer would add trusted-semantics and artifact-compatibility
work; neither is authorized here. No conflict with ADRs 0001, 0002 or 0010 is
required by these comparisons. Replacing their semantic contracts would require
an explicit reconsideration.

The orbifold question remains a separate source of requirements. Synthetic
internal reasoning may appropriately assume cohesive and infinitesimal
principles. A concrete model must validate the principles used; comparison with
classical orbifold presentations needs its own correspondence, including
isotropy; executable realizations need separate observation and numerical
contracts. The owner's completion statement about the latest Agda work is
reported evidence. Its artifact and comparison report are unavailable, so this
assessment assigns no library ranking or coverage to it and does not substitute
older archives. On arrival, pin the report, library revisions and selected
statements, then classify mismatches as semantic, foundational, API, maturity,
documentation or artifact compatibility.

The consequential uncertainty is whether recurring work lies mostly in the
mathematics of genuinely new models or in the present encoding's repeated
bridges. #357 cannot distinguish these explanations. The proposed tests could
favor retaining the current core, replacing the dependent provider boundary,
or pursuing another core representation. Final architectural selection and
release of #358–#361 remain pending the incoming evidence or an explicit owner
change of scope.
