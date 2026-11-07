# Six semantic traditions and the language research agenda

Assessment for [#301](https://github.com/VladimirMarko/conaled/issues/301),
2026-11-05. **Investigate synthetic domain theory and rewriting-based conversion
extensions through two bounded paper comparisons. Defer implementation.** The
other four traditions remain eligible when the promotion conditions below hold.
This extends [#280's discovery](external-discovery-assessment.md); it does not
reopen its completed comparisons or exhaust the alternatives.

## Current coverage and successors

This is the frozen #301 assessment. Its proposed #337/#338 paper studies are
complete; #346/#347 and #345 own their implementation/provider successors.
The [#350 coverage map](semantic-traditions-coverage.md) replaces the residual
ownership table below for current scheduling. In particular #296 and #300 are
closed bounded comparisons, not active owners of classical-pole or relational
hiding work. Their remaining questions now have open programme owners and
explicit promotion tests. #351/#352 own the two promoted adjoint experiments.


## Capability brief and exposure

The starting requirements were those of the [language direction](../language-direction.md):
authors should reuse arguments across mathematical settings, expose the
principles each argument needs, extend a theory without losing old meaning,
and retain equality, dependent indices and selected witnesses. Meaning must be
specified independently of an evaluator. Constructing a setting from data that
varies in a context is also a capability to test, not an externally chosen model
instance in disguise.

The inspected local revision was
`701023ce73ff297604fb21f2b6caada9e727c10c`. The issue, repository guidance and
language direction were read before external discovery. Those documents already
exposed summaries of local results, including #314–#320. No Lean implementation
was inspected for this study. The six external technical readings preceded
reading the comparison reports and dependent reassessment for reconciliation.
Thus this was author-needs-first discovery with disclosed exposure, not a blind
search or an independent author trial. Prior training exposure is unknown.

The six traditions were mandated by the issue. Searches used these literal
queries, followed by title/author searches to recover primary copies:

| Area | Initial query | Technical reading beyond the abstract |
| --- | --- | --- |
| Synthetic domain theory | `synthetic domain theory predomains complete well complete lifting fixed point theorem Simpson` | van Oosten–Simpson, §1.1, Definition 1.11, Theorem 1.13 and its proof; distinction from well-completeness. |
| Nominal binding | `Gabbay Pitts new approach abstract syntax binding theorem freshness nominal sets pdf` | Gabbay–Pitts, §5, Theorem 5.1, Corollary 5.3, Lemma 5.4, Theorem 5.5 and substitution Example 5.7. |
| Proof-theoretic semantics | `Prawitz proof theoretic semantics validity introduction elimination normalization pdf` | Gheorghiu–Pym, §2 atomic bases and support, §3.1–3.3 soundness/completeness statements and selected proof steps. |
| Classical realizability | `site.irif.fr krivine realizability algebras adequacy lemma pdf` | Krivine, §1 algebra and pole definitions, truth clauses, Theorem 1.3 and application case of its proof. |
| Rewriting frameworks | `Dedukti lambda Pi modulo rewriting confluence subject reduction theorem paper pdf` | Saillard, introduction's critical peak, §6.3–6.4, Theorems 6.1–6.4 and the product-compatibility argument. |
| Categorical systems | `Baez Pollard compositional framework reaction networks theorem black boxing pdf` | Baez–Pollard, Definition 22, Theorem 23, polynomial/projection argument and composition proof. |

Primary copies are linked at the claims below. Edinburgh's original download
returned 403; its Pure mirror supplied the technical text. IRIF's Krivine PDFs
were inaccessible through the browser; the author's arXiv paper supplied it.
Gabbay's and Baez's copies opened initially but later timed out; Cambridge and
arXiv copies supplied the detailed passages. These are access failures, not
negative mathematical evidence. Search results included secondary summaries;
none serves as evidence for the conditional results below. The reading was
selective, not a complete audit of all proofs and references.

**Evidence classes:** “Source result” identifies a paper's claim and hypotheses.
“Assessment” and proposed tasks are this report's deductions or design judgments.
There are no new checked Lean claims or observed author outcomes in this report.
Existing local results are attributed to their retained reports rather than
claimed to have been rechecked here.

## Synthetic domain theory: change the ambient notion of function

**Source result.** In the internal logic of an elementary topos with a natural
numbers object and a dominance Σ, let L be its partial-map lifting monad, I its
initial lift algebra, and F its final lift coalgebra. Completeness of X means
that restriction `X^F → X^I` is an isomorphism. Theorem 1.13 says that if X is
complete and carries a strict L-algebra structure, every endomap of X has a
fixed point. Its proof extends the initial-algebra map to F and evaluates at
infinity. This is not a theorem about arbitrary classical sets or a uniqueness
claim. [van Oosten–Simpson, Definition 1.11 and Theorem 1.13, p. 244](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf).

**Assessment.** This could overturn the assumption that continuity and recursion
must always be separate author-supplied structure on ordinary functions. A
suitable internal setting may discharge those obligations in its construction.
It challenges separation of argument requirements from model construction:
which functions an author can form already depends on that setting's logic.
The benefit would be reusing a recursive argument without repeating continuity
proofs for each composition.

**Discriminating task.** Specify a partial recursive computation by an independent
partial-map denotation, then compare an internal complete-algebra argument with
an external domain argument. Vary the presentation over Γ and demand that the
chosen solution and its dependent correctness certificate commute with two
substitutions. A fixed-point existence proof without this selected-data contract
fails the task. As a paper rejection control, classical Bool with negation has
no fixed point, so a proposed interpretation admitting it as such a complete
strict algebra must fail. This rejects overbroad adoption, not SDT itself.

Model construction must establish the topos/dominance/algebra hypotheses.
Compositional meaning needs maps preserving the chosen solution, not just the
existence of some solution. Evaluation and adequacy remain separate. Equality
of fixed-point proofs does not identify their chosen values or dependent data.
The model infrastructure cost is substantial; no immediate Lean adapter is
required to keep this alternative eligible.

## Nominal binding: make freshness a semantic obligation

**Source result.** Gabbay–Pitts work with finitely supported objects in the
Fraenkel–Mostowski universe over atoms. For untyped lambda terms, Theorem 5.1
identifies alpha classes with the inductively defined FM-set using variables,
application and name abstraction; Corollary 5.3 gives its initial-algebra
property. Lemma 5.4 says an FM-function `h : A × X → Y` induces the specified
map from `[A]X` exactly when, for fresh a, every `h(a,x)` is fresh for a.
Theorem 5.5 applies the corresponding condition to recursion.
[Gabbay–Pitts, §5, pp. 5–6](https://www.cl.cam.ac.uk/~amp12/papers/newaas/newaas.pdf).

**Assessment.** Binding need not be organized around explicit positions in a
context or arbitrary host functions. The author could reason by fresh names
and structural induction modulo alpha equivalence. This changes the possible
judgment representation, but does not establish dependent substitution,
context-indexed model construction or higher identity for this project.

**Discriminating task.** Compare a named, freshness-aware representation with the
retained source boundary on substitution beneath two binders, preserving the
free-variable support and a selected dependent payload. Both routes must show
that renaming the binders leaves the independent interpretation unchanged.
A proposed operation returning the bound atom of an abstraction is the negative
control: `[a]a = [b]b` cannot support a well-defined extractor returning a and b
respectively when they differ. This paper argument rejects an unrestricted
binder observer, including one disguised by choosing representatives.

The FM construction supplies a model of binding; its initiality supplies
compositional syntax interpretation under the stated conditions. It is not an
evaluator or a proof of observational equivalence. Alpha equality of syntax
must remain distinct from beta/eta equality and from equality of dependent proof
objects. Adopting it would require binding infrastructure and a migration of
judgments, rather than a cosmetic renaming helper.

## Proof-theoretic semantics: challenge model-first requirements

**Source result.** Gheorghiu–Pym define support relative to extensions of atomic
bases over fixed denumerable symbol supplies. Their basis C permits zero- and
first-level rules; I also permits second-level rules with discharge. With the
matching classical or intuitionistic Hilbert calculus, Theorem 3.7 gives
soundness and Theorem 3.11 gives completeness for a finite set Γ of sentences
and sentence φ. The support clauses and the basis restriction are part of the
hypotheses. This is not completeness for full set-theoretic second-order
semantics. [Gheorghiu–Pym, §§2–3](https://www.cantab.net/users/david.pym/Proof_theoretic_Semantics_for_Second_order_Logic.pdf).

**Assessment.** The source is a technical manuscript; the inspected typesetting
contains apparent slips in displayed clauses. The recommendation uses its named
conditional results, not those displays as a ready formal specification. A
formalization would require resolving them against the authors' definitions.

The architectural challenge is whether admissible reasoning and extension of
inferential commitments should determine the setting before an external model
is chosen. Authors might reuse an inference under every allowed extension of
an atomic base. This could reshape #290's notion of a proof's requirements.
Our independent-denotation criterion still needs a bridge from that inferential
account to the client's separately fixed observations; operational presentation
is neither an automatic rejection nor such a bridge.

**Discriminating task.** Freeze an implication argument, an independently specified
selected witness family, and two successive atomic-base extensions. Compare
base-relative support with a model-relative proof. A route fails if it transfers
validity but cannot return the same witness under the allowed interpretation.
A deliberately overstrong claim that changing the permitted base class cannot
change the logic must also be rejected.

The support relation supplies compositional logical meaning in this fragment;
existence of a particular geometric or dependent model remains unproved.
Soundness/completeness compares consequence relations, not computational traces
or an equality on proof objects. Adding proof relevance is a concrete unresolved
obligation, not a consequence of the word “proof” in the tradition's name.

## Classical realizability: separate valid realizers from selected witnesses

**Source result.** Krivine's realizability algebra supplies terms, stacks,
processes, application, push, continuations and designated combinators. Its pole
is closed backwards under the specified process reductions. Given an
interpretation I, a derivation `x₁:A₁,…,xₖ:Aₖ ⊢ t:A`, and realizers ξᵢ of the
interpreted assumptions, Theorem 1.3 says that substituting them into t realizes
the interpreted conclusion. Implication is interpreted through pushing an
argument realizer onto a counterexample stack. [Krivine, §1, pp. 3 and 7](https://arxiv.org/pdf/1005.2395).

**Assessment.** This challenges an architecture that treats classical principles
only as inert propositions while constructive witnesses live in a separate
unrelated language. An author could expose a classical principle as a realizer
requirement and reuse a proof after it is supplied. It also couples the choice
of model and interaction behavior through the pole. A machine-independent client
denotation must therefore be an additional contract, not inferred from adequacy.

**Discriminating task.** Hold an arithmetic result and its returned witness
observation fixed while changing a continuation interpretation. Compare the
realizer with a direct witness-producing specification. Require the observed
witness and dependent certificate, not just realizability of an existential.
As a rejection control, a pole containing every process satisfies backward
closure and trivializes realization. Thus adequacy alone cannot certify a
nontrivial client observation; admissibility must rule out this collapse.
This is a paper counterexample, not a checked local construction.

An algebra and pole establish an interpretation, with additional conditions
needed for its desired consistency or observations. Truth clauses are
compositional relative to them. Realizer execution is a separate computation
claim; two realizers of one formula need not be equal programs, equal selected
witnesses, or equal proofs. #296 owns the corresponding effect/witness problem.

## Rewriting frameworks: extensions can alter conversion

**Source result.** Saillard's Theorem 6.3 derives product compatibility for a
global context Γ if its higher-order rewrite system `HRS(βΓ)` is confluent.
Theorem 6.4 assumes Γ well formed, left side u a λΠ-pattern, a well-formed local
context Δ with `FV(u) = dom(Δ)`, and both sides u,v typed at the same T. It then
gives permanent well-typedness of the rule in well-formed extensions. Theorem
6.1 preserves typing under rewriting modulo β in well-formed global/local
contexts. These conditions do not assert termination or consistency of every
rule extension. [Saillard, §6.3–6.4, pp. 98–99](https://arxiv.org/pdf/1507.08055).

**Assessment.** Constructor admission may change judgmental conversion, not only
add operations and law proofs to a fixed judgment system. Authors could reuse
arguments whose intermediate types compute by admitted equations without
repeated explicit transports. This is a possible replacement of the judgment
boundary, not an instruction to alter Lean's kernel.

**Discriminating task.** Freeze a dependent family indexed by an expression and a
selected section. Admit two separately justified equation packages and compare
conversion-based reuse with explicit equality transport. Require an independent
model in which each equation holds and the chosen section is retained. As a
paper rejection control, two individually terminating, confluent ground systems
`f(a) → b` and `f(a) → c`, with distinct irreducible b,c, have a nonconfluent
union. If b,c have different denotations, no common sound interpretation admits
both. This forces a joint admission check even when separate checks succeeded.

A well-formed rewriting signature is not a proof of all-model expansion.
Compositional meaning requires interpretation of conversion; computation needs
its own normalization/decision hypotheses. Convertibility, propositional
identity and equality of proof witnesses must stay separate. Implementation
would require a checked object-language encoding or translation back into Lean,
plus soundness and old-client recovery, not additional kernel axioms.

## Broader categorical systems: an observation can forget internal solutions

**Source result.** Baez–Pollard's Theorem 23 constructs a symmetric monoidal
black-boxing functor from Dynam to semialgebraic relations. Dynam's open systems
use finite-set cospans and algebraic vector fields. The relation consists of
boundary concentrations and flows admitting a steady state; polynomial
constraints and projection give semialgebraicity. The theorem does not require
unique internal steady states. [Baez–Pollard, Definition 22 and Theorem 23,
pp. 31–35, arXiv v5](https://arxiv.org/pdf/1704.02051).

**Assessment.** This is a coverage test beyond wiring syntax. It challenges the
assumption that the meaning worth preserving must be a returned function value
or retain all internal state. An author could compose an externally observable
steady-state contract while changing internal presentations. A relation may be
the appropriate independently specified denotation, but only if the client's
observations permit the loss of internal information.

**Discriminating task.** Fix two polynomial open systems and a boundary relation
before choosing their presentation. Compare relational hiding with a native
selected-solution interface. Require equality of the composite boundary
relations. Then strengthen the task to retain a chosen internal steady state
and its dependent certificate. A closed system with `v(x)=x(x−1)` has distinct
steady states 0 and 1 but only one empty boundary tuple. Black-boxing cannot
recover which was selected. This explicit paper example rejects using boundary
relation equality as a universal selected-witness preservation contract.

A category of systems and a functor supply compositional static meaning;
individual solution existence is encoded relationally, not guaranteed for each
boundary input. Numerical solution, transient trajectories and stability are
separate computation/analysis questions. Relation equality is neither equality
of internal systems nor proof equality. This gap belongs with #300 and the
observation owners; it does not justify another wiring implementation study.

## Selection, costs and promotion conditions

The criteria are semantic fit to an unmet author capability, uncertainty that
could reverse an architectural decision, and cost of obtaining discriminating
evidence. Cost means new mathematics, migration and author obligations as well
as implementation effort. No rating uses popularity or ease of a Lean encoding.
The table makes a qualitative choice, not a measured ranking.

| Tradition | Decision and semantic fit | Uncertainty, cost, and promotion condition |
| --- | --- | --- |
| Synthetic domain theory | **Investigate**: internal partiality could change which author obligations belong to the setting. | High uncertainty about context-varying complete algebras and selected solutions; high model cost. A paper comparison can reveal the required reindexing law before a port. |
| Nominal binding | **Defer**: direct fit for binder reasoning, narrower evidence for the requested dependent settings. | Medium binding-infrastructure cost; dependent payload and comparison laws unestablished. Promote when a named client shows repeated binder/freshness work after ordinary facade repair. |
| Proof-theoretic semantics | **Defer**: strongest challenge to model-first reasoning requirements. | High uncertainty about independent observations and proof-relevant data; source-definition clarification required. Promote when a base-extension client needs a witness-preserving semantic bridge unavailable in #290's existing routes. |
| Classical realizability | **Defer here; reconcile with #296**: classical principles as reusable computational requirements. | Pole/observation and extraction costs remain; #296 already owns changed effects with selected witnesses. Promote a separate study only for a classical principle and pole contract that #296 does not cover. |
| Rewriting frameworks | **Investigate**: conversion-changing extensions challenge fixed judgment admission. | Joint confluence and independent model admission are uncertain; an object-language checker/translation would be costly. Compare two equation packages on paper before choosing that implementation. |
| Broader categorical systems | **Defer**: relational hiding fits external observations and exposes lost internal data. | Moderate paper cost, substantial nonlinear analysis cost. Promote when #300's chosen observations need existential hiding or selected solution recovery beyond wiring composition. |

No tradition is rejected wholesale. Reject the overbroad contracts identified
by the six tasks. No immediate library adoption follows from the existence of
an external theorem.

### Two follow-up investigations

The original assessment proposed these two investigations. The owner approved
their creation on 2026-11-07: [#337](https://github.com/VladimirMarko/conaled/issues/337)
is a child of #289, and [#338](https://github.com/VladimirMarko/conaled/issues/338)
is a child of #288. Their tracker bodies now own acceptance and scheduling;
the descriptions below retain the mathematical motivation of this assessment.

1. **Context-varying partial settings and selected fixed points (#337).** Owner:
   #289, coordinated with #36/#235 and #288. Freeze a small independently defined
   partial computation and an indexed selected correctness certificate. Compare
   an SDT construction in slices with an external domain route. State the exact
   slice/dominance/completeness hypotheses; derive or refute preservation of the
   selected fixed point under two reindexings. Include Bool negation as the
   invalid-model control and a map that preserves fixed-point existence but not
   the selected solution as the selection control. Deliver a paper construction
   or a precise obstruction before requesting Lean model work. Stop without
   adoption if only pointwise existence can be established. This extends #319's
   finite internal-setting evidence rather than repeating #314/#315's structural
   and representation comparisons.
2. **Joint admission of conversion-changing extensions (#338).** Owner: #288,
   coordinated with #290/#289. Freeze the dependent-family/selected-section
   contract above. Compare explicit equality transport with a λΠ-modulo
   presentation for two composable equation packages. Supply the joint typing,
   confluence and independent-interpretation obligations, distinguish preserved
   old judgments from all-model expansion and conservativity, and retain the
   nonconfluent-union control. Deliver an adopt/defer decision and migration
   obligations for one bounded fragment. Do not implement a checker or importer
   merely because a paper signature typechecks. This concerns changes to
   conversion, not #317's already checked fixed-boundary constructor admission
   or #294's publication of theory views.

The two comparisons are independently executable; their order is a scheduling
choice. Promotion of a deferred tradition should replace or rescope these
priorities when its trigger appears, rather than silently starting more than
two deeper investigations under #301.

## Reconciliation and residual ownership

The [dependent reassessment](dependent-architecture-reassessment.md) treats
arguments, judgment interpretation, model construction and setting comparisons
as interacting responsibilities. The sources support keeping that interaction
open: SDT changes admissible functions through the ambient logic, nominal
semantics changes binding, inferential semantics changes admissible base
extensions, realizability ties interpretation to a pole, rewriting changes
conversion, and system observations change the retained data. None establishes
four independent implementation layers.

| Existing owner | Consequence of this report |
| --- | --- |
| #288, theory extensions | Keep expansion, conservativity and selected-section descent separate. Own the proposed conversion-extension comparison; nominal/realizability admission cannot be assumed to expand every model. |
| #289, dependent semantics | Own the proposed internal partial-setting comparison. #314/#315 remain evidence for their stated structural/source boundaries, not a filter excluding different binding or equality foundations. |
| #290, proof reuse | Retain proof requirements and encoding adequacy separately from publication. Assess proof-theoretic support or rewriting translations against selected data before claiming proof transport. |
| #295, relational transfer | A boundary relation or realizability relation needs its own adequacy and witness contract; no automatic application is established here. |
| #296, effectful realizers | First owner for the classical-realizability witness/pole question. Avoid a duplicate child until a concrete uncovered principle is selected. |
| #297, modal/higher study | Nominal alpha equality and rewrite conversion do not discharge higher identity or modal-context restrictions. |
| #298, probability models | No SDT fixed-point theorem here establishes probability measures or arbitrary random-function spaces. Coordinate only for an actual partial probabilistic client. |
| #299, quantitative observations | Relation equality and realizability do not supply quantitative precision or error bounds. Retain their separate observations. |
| #300, open systems | Reconcile the static hiding/selected-state gap with its observations; do not repeat the dedicated wiring comparison. |
| #235 | Coordinate the two proposed children, deferred triggers and future migration decisions. Continuing external discovery remains open. |

#107 remains paused. #108 has no theorem selected or prepared by this work.
#260 remains inactive. #305/#306 are outside this change. No frontend, universal
AST, global subtyping, new kernel axiom or automatic model adapter is required.

## Validation and limits

This change is a research document. Validation checks its relative links,
whitespace, source locators and the six acceptance rows; no formal definitions,
proofs, build tooling or dependency pins change. Consequently no Lean build or
proof audit is claimed. The coordinator owns independent Standards and Spec
review of the committed candidate; this document does not certify its own
acceptance.

The counterexamples are paper arguments, and the proposed comparisons are not
executed experiments. No author effort was measured. The six readings omit many
variants within each tradition, including broader nominal dependent semantics,
other realizability algebras and systems with richer time behavior. Their
absence is unassessed scope, not rejection. Later adoption must recover the
established concrete specializations under their original assumptions and
explicitly retain the equality, indices and selected witnesses each client uses.
