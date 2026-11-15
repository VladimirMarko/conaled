# External comparison for setting-parametric programming and proof

Completed first-pass assessment for [#235](https://github.com/VladimirMarko/conaled/issues/235),
coordinated with #36, #200 and #8. Research date: 2026-11-04. Local inspection
baseline: `d509582f845133fca03d912f656b2576d4b98a57`.

The next comparison should test **dependent substitution across models** and
**proof reuse across changes of computational interpretation**. These questions
challenge the language's promised ability to factor out a mathematical setting.
A successful compiler example in an already supported category cannot settle
them. This is a research recommendation, not an implementation selection or a
claim that any surveyed framework supplies the whole proposed language.

The assessment responds to the
[external-discovery brief](https://github.com/VladimirMarko/conaled/issues/235#issuecomment-6530272680)
and the [semantic selection criteria](../language-direction.md#selecting-research-by-semantic-requirements).
The earlier [#201 atlas](logic-correspondence-atlas.md) classifies logic fragments
and interpretations. It is prior evidence, not the scope owner for this
comparison. The first pass was merged locally in `c929cce`; subsequent Cousot
source inspection and transcription strengthen one entry.
#280's [completed selection assessment](external-discovery-assessment.md) records
the subsequent discovery, challenges this pass's priorities, and selects
#286/#287. #235 retains continuing architectural
discovery and integration ownership. The experiments below remain proposals.

The first pass compares selected traditions more strongly than it justifies
the selection of those traditions. Its named search families and shared
categorical vocabulary leave that selection open to challenge. #280 therefore
used discovery from author needs before exposing fresh researchers to this
shortlist, then assessed omissions that could change the priorities. Its revised
sequence supersedes the D1/D3-first recommendation below while retaining this
source assessment as the first-pass record.

## Discovery scope and limits

Start with three author needs: state the structure an argument uses; interpret
that argument in settings supplying it; and extend a setting without silently
changing old judgments. Search for accounts of those needs before asking
whether their machinery fits `SquareKit`. The two research tracks were assigned
those needs and the requirement to consider replacement architectures. One
investigated logical foundations; the other investigated computational semantics.
Their separation broadens coverage but is not a blind or statistically
representative sample: both share the project's brief and categorical vocabulary.

The retained source assessments are:

- [Foundations and changes of setting](external-language-foundations.md):
  institutions, logical frameworks, categorical logic, dependent coherence,
  parametricity, multimodal type theory and cubical identity.
- [Computation and observations](external-computational-semantics.md):
  effects, recursive denotation, matching logic, resources, games and quantitative
  semantics.
- The additional perspectives below: abstract interpretation, open-system
  interconnection and effectful realizability.

Discovery used primary author, publisher and archival sources, following the
semantic constructions rather than citation rankings. Representative search
families were “institutions satisfaction condition”, “local universes coherence”,
“multimodal dependent type theory”, “algebraic effects handlers”, “domain recursive
semantics”, “matching logic”, “game semantics”, “graded semantics”, “abstract
interpretation” and “operad open dynamical systems”. These identify the search
coverage, not a reproducible exhaustive literature retrieval. The companion
notes record the inspected versions and locators. An abstract-level lead is
marked separately from an inspected theorem; inaccessible text cannot support
a detailed theorem assessment. Publication dates are not evidence of superiority.

The stopping rule for this pass was a source-backed comparison across different
semantic commitments and a set of tests that can reject our favored design.
It was not saturation of all traditions. English-language availability, the
researchers' prior concepts, and search-engine indexing remain selection effects.
Formal verification of the papers, independent human author trials and a census
of implementations were outside this pass. Unknowns below remain open rather
than becoming low rankings.

## Additional perspectives

**Abstract interpretation.** Cousot and Cousot's 1977 paper separates semantic
soundness from computation of an approximation. Direct inspection of §6
(p. 242) and Appendix 12 (pp. 251–252) confirms monotone abstraction and
concretization maps, `α(γ(a)) = a`, `c ≤ γ(α(c))`, and local simulation
inequalities. Under the stated complete-lattice and monotonicity hypotheses,
T1/T2 bound the concrete greatest/least fixed points by concretizations of the
corresponding abstract fixed points. They do not assert equality of meanings.
Section 9.1 (pp. 245–246) separately gives a terminating approximation scheme:
a widening needs both upper-bound and sequence-termination conditions, with
widening points meeting every dependency cycle. The result can be a sound
upper bound rather than the least fixed point itself.
[Primary paper](https://www.di.ens.fr/~cousot/COUSOTpapers/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf).

The [source-inspection record](cousot-1977-source-inspection.md) replaces the
earlier summary-only assessment. OCR served as navigation; retained formulas,
diagram direction and selected proof arguments were checked against page images.
This is a bounded reading, not a formal proof audit. A separate
[corrected transcription](../references/cousot-1977/README.md) preserves §§5–9
and Appendix 12 alongside the source scan.

Proposed test: use one recursive specification with two abstract domains, record
soundness and precision separately, and compare exact fixed-point semantics with
a terminating approximation. Require a concrete loss-of-precision case and
explicit widening/iteration hypotheses. This could reject an architecture that
requires invertible interpretation or confuses analysis termination with program
termination. The test remains a proposed research contract, not a checked example.

**Open dynamical systems.** Vagner, Spivak and Lerman, arXiv:1408.1598v2 (2015),
Definition 4.2 and Proposition 4.5, organize open smooth systems as an algebra
of wiring diagrams; §5 supplies the linear subalgebra. Outputs depend on state,
while the vector field depends on state and input. The lax monoidal functor
laws express compatibility with wiring composition. They do not establish
existence of every trajectory for all time.
[Inspected text](https://arxiv.org/html/1408.1598v2).

Proposed test: compare hierarchical interconnection with a typed compiler
presentation on the same smooth-system contract, keeping the stated input/output
discipline. A new composition language may be useful even if its objects cannot
support unrestricted cartesian closed operations. Check the permitted wiring
before identifying this construction with arbitrary feedback. Authoring a
network and changing its internal decomposition should preserve the specified
vector field; numerical integration accuracy is a separate obligation.

**Effectful realizability.** Cohen, Grunfeld, Kirst and Miquey,
arXiv:2506.09458v1 (2025), Theorem 5, construct realizers from intuitionistic HOL
derivations in the monad-parameterized EffHOL framework. Its logical modality
must satisfy the given rules; arbitrary effects are not automatically valid
instances. Theorem 8 and Corollary 9 connect pure instances to evidenced frames,
triposes and realizability toposes. The extension to non-pure instances requires
the specified set-level modality laws. This qualification is more precise than
the abstract's broad description.
[Inspected text, §§V–VII](https://arxiv.org/html/2506.09458v1).

Proposed test: translate one retained-witness argument through two admitted
computational instances, recording the realizer and modality obligations.
Compare that with translating only the proposition's validity. A validity-only
success fails the witness contract. This route could reorganize the proof/program
boundary, but no claim follows that arbitrary Lean proofs can be exported or
that object-theory principles may be installed as Lean kernel axioms.

## What the approaches would change

The following comparison is our inference from the cited assessments. These
are different layers of a possible design, not interchangeable products with a
single winner.

| Design question | Alternatives worth comparing | Possible consequence for this repository |
|---|---|---|
| What is a setting and a change of setting? | Institutions and theory morphisms; indexed categorical logic; multimodal contexts | Settings may need signatures, judgments and model reducts, or context-indexed structure, rather than just an object interpretation and arrow map. |
| What is shared when a proof is reused? | LF/MMT encodings; comprehension and coherence; relational parametricity | Reuse may concern derivations and substitutions, semantic structure, or uniformity across relations. Each requires its own adequacy or preservation argument. |
| Which equality does the author need? | Extensional categorical equations; cubical paths; game observations; directed quantitative orders | A single equality quotient can discard path data, interaction distinctions or quantitative direction. A replacement must retain the selected native judgment. |
| How do computation and proof interact? | CBPV and algebraic effects; domain models; effectful realizability | Value/computation distinctions, recursive fixed points and realization modalities can change the organizing interfaces, beyond adding another compiler target. |
| What justifies extension? | Theory morphisms; matching logic; resource algebras; handlers | Adding symbols is distinct from preservation of equations, adequacy, framing and effect laws. An old proof's premises must remain valid. |
| How are many components assembled? | Wiring algebras; games; existing compositional interpretations | Hierarchical networks and interactive strategies may need composition operations absent from a chosen term grammar. |
| How can an interpretation intentionally lose information? | Abstract interpretation; relational observations; graded bounds | The contract may be soundness or an ordered approximation, with reflection and precision assessed separately. |

Dependent coherence and effectful realizability deserve early comparison because
they directly address setting-independent arguments and retained computational
witnesses. Institutions and LF/MMT deserve equal attention when the intended
reuse crosses whole theories or encoded deductive systems. Neither good fit nor
a difficult encoding is established merely by these papers' existence. Cubical
and multimodal candidates remain in the comparison even if they require larger
changes than a bounded adapter. Open-system and resource accounts test different
composition and observation contracts; they should not be rejected for failing
to supply dependent type theory themselves.

## Local fit assessed after discovery

This is a source inspection at the baseline above, not a new Lean build or a
claim of exhaustive repository coverage. The named declarations constrain what
is already available; absence from the inspected seam does not prove absence
from the whole library or Mathlib.

| Inspected public seam | Existing evidence | Question the external comparison adds |
|---|---|---|
| [STLCNaturality](../../SquareKit/STLCNaturality.lean), `Model`, `Preserves`, `naturality`, `preserves_comp`, `naturality_comp` | Object-polymorphic interpretation and operation-preserving maps for the existing typed term grammar; composed interpretation avoids another syntax induction. | Can a route also translate the theory or context discipline? These declarations do not supply a generic theory translation, parametricity theorem or dependent coherence result. |
| [DependentSheafSoundness](../../SquareKit/Internal/DependentSheafSoundness.lean), `type_substitution`, `term_substitution`, `derived_pairing` | A restricted dependent source has substitution and pairing interpretations, including explicit transport of terms. | Compare a general coherence construction under its actual hypotheses; do not infer strict substitution for arbitrary models from this selected sheaf instance. |
| [RelationTransport](../../SquareKit/RelationTransport.lean), `image_requirement`, `image_comp`, `requirement_comp` | An existential-image/universal-requirement Galois connection and relational composition. | An abstract-domain fixed-point analysis still needs its domain, transfer and approximation obligations. These predicate consequences do not extract witnesses or establish total correctness. |
| [FiniteKernel](../../Applications/Probability/FiniteKernel.lean), `kernel_comp`, `tableMeaning_laws` | Rational finite tables interpret compositionally as stochastic kernels. | Effectful and graded comparisons must preserve mass or their stated quantitative observation; support alone cannot replace the law. |
| [EquationTranspose](../../SquareKit/EquationTranspose.lean), `transpose_preserves`, `untranspose_transpose`, `transpose_untranspose` | Indexed equation-cell presentations have inverse syntax transformations and retained denotation. | This is not general data/codata duality, an adequate encoding of binders, or a foundation for every language. Compare broader presentations without treating this prior investment as a selection criterion. |

The [preservation inventory](preservation-contract-inventory.md) and
[first architecture milestone](preservation-architecture.md) already distinguish
native dependent, probabilistic and categorical evidence. The comparison does
not assume the entire library is predicate-only. It challenges whether the
existing family is the best author-facing organization and which common
requirements it actually exposes. Existing implementations establish a migration
baseline, not a reason to exclude replacements during discovery.

## Discriminating experiments and ownership

All tasks below are proposed, paper-level acceptance contracts. No result or
independent author-effectiveness measurement is claimed. Begin each comparison
by fixing identical source judgments, admissible settings and observations for
both routes. A route may report a precise unsupported case instead of weakening
the task until it passes.

| Task and owner | Matched comparison and required evidence | Result that would challenge the current approach |
|---|---|---|
| D1. Changing a dependent setting, #36/#235 | Compare native substitution interfaces with comprehension/local-universes organization. State the weak model's hypotheses, interpretation of dependent pairing, two successive substitutions and the needed equality/coherence. Retain dependent witnesses. | Native authors repeatedly rebuild coherence or need stronger assumptions; the external route shares that proof. Conversely, unavailable local-universes hypotheses rule out that route for this client. |
| D2. Theory extension and proof reuse, #200/#235 | Compare a theory-morphism/LF/MMT presentation with direct library interfaces. Extend one signature, transport an old derivation and its interpretation, and distinguish derivation adequacy from truth preservation. Include a translation that forgets a witness. | Only validity survives when the task requires a reconstructible derivation, or extending the signature forces unrelated proof rewrites. |
| D3. Effectful witness interpretation, #36/#196/#235 | Compare admitted EffHOL instances and a CBPV/handler account with the existing proof/program boundary. Record value/computation types, modality/effect equations, sequencing and an explicit returned witness. Test a changed effect law. | Current interfaces erase the realizer or hide a required effect law. A proposed handler that violates the law also fails; monad syntax alone is not evidence. |
| D4. Context and identity restrictions, #36/#200 | Compare an explicit multimodal or cubical fragment with the current representation of the same context/path data. State allowed variable access, path observations and substitution. Include a forbidden cross-mode dependency or an identity-erasing interpretation. | The route accepts forbidden context access or proves only a set-level consequence of a task requiring higher identity. Separate mathematical expressiveness from Lean elaboration cost. |
| D5. Approximation and quantitative observation, #174/#200/#235 | Compare an abstract/graded route with native relational and kernel observations on a fixed specification. State which order, mass and fixed-point assumptions compose. Include equal-support/different-mass and sound-but-imprecise cases. | A shared equality or Boolean observation cannot express the required distinction; an external route may also fail if its grade algebra loses correlations. |
| D6. Hierarchical open composition, #27/#36/#235 | Compare wiring-algebra interconnection with a chosen native presentation, retaining the same smooth vector-field contract and allowed wiring. Record decomposition invariance and separate trajectory/solver obligations. | A route needs artificial closed operations or weakens the input/output contract just to encode the network. |

The provisional first-pass recommendation is D1 and D3, with D2 assessed alongside them for
cross-theory reuse. They expose different failures: coherence of dependent
meaning and retention of computational witnesses. This is a priority for gaining
information, not a total ranking of the literature. D4 stays in scope even if
its implementation is more demanding; D5 and D6 provide independent quantitative
and open-system tests. #280 has reassessed this order and handed selected
experiments to #286/#287.
See its [decision record](external-discovery-assessment.md) for the revised
sequence and deferred D1–D6 ownership. The owner column identifies coordinating
programmes, not dedicated
experiment tickets or authorization to start all six. #235 owns reconciling
eventual experiment outcomes before selecting a retrofit. #260 remains conditional; this assessment does not activate implicit
subtyping or choose its semantic algebra. The #266–#270 duality agenda remains
one set of hypotheses to compare with these alternatives.

A later author trial should freeze the contracts and reference solutions first,
use authors who did not design either interface, alternate route order, and
retain prompts, assistance and failures. Measure required concepts, exposed
transport/coherence obligations, diagnostics and completion under recorded tool
and model conditions. A paper's concise notation is not an observed usability
result. Keep mathematical suitability, current Lean encoding, and author effort
as separate findings.

## Remaining discovery and integration boundary

This pass does not deeply assess proof-theoretic semantics and inferentialism,
classical realizability beyond the selected effectful framework, synthetic domain
theory, coalgebraic modal logic, Chu/continuation accounts beyond existing local
research, nominal binding, proof assistants based on rewriting, or the full range
of categorical systems theory. The companion notes record further omissions
within their tracks. These are unassessed candidates, not rejected alternatives.

Before an implementation decision, follow the omitted tradition most likely to
change that decision. For D1 this includes alternative coherence constructions;
for D3, realizability and effect combinations outside the selected instances.
Revisit this recommendation if those sources remove an assumed restriction or
expose a failed composition law. Keep a replacement candidate alive until its
semantic contract has been compared, even when migration is expensive.

Any eventual replacement or compatible layer needs a separate scope: affected
consumers, native judgments retained, migration/refactoring cost, recovery of
old specializations under their old assumptions, checked negative cases and
independent author evidence. Current research supplies neither that migration
nor a universal language. It supplies alternatives and falsifiable questions
for the next decision, while leaving #235's continuing discovery ownership intact.
