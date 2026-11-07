# Bialgebraic methods for dependent interpretation

Issue [#329](https://github.com/VladimirMarko/conaled/issues/329) reassesses the
published constructions against the dependent contract established by #314–#320.
Retain bialgebraic compatibility for construction and observation. Investigate a
comparison that acts on dependent families and selected sections before adopting
it for dependent interpretation. The inspected results do not yet supply that
comparison, contextual J, or the required higher model. This is a missing
construction, not a theorem that a bialgebraic approach cannot supply them.

The strongest immediate opportunity is to reuse compatibility through changes
of presentation. The direct guarded approach already derives preservation for
compound source arguments from primitive model-map laws. Repackaging those laws
without deriving any of them would add obligations without an established gain.
A competing presentation remains eligible even if it replaces the current
syntax; promotion requires mathematical recovery, not an adapter as an entry fee.

## Status after the dependent follow-ups

This assessment records the inspected baseline `701023ce` and the proposals
made against it. Subsequent results are collected in the
[current dependent assessment](dependent-architecture-reassessment.md#current-follow-up-results).
In particular, [#325's groupoid comparisons](coherent-groupoid-comparisons.md)
now supply scoped family/section comparisons and composition laws;
[#326](reference-dependent-calculus.md) supplies a bounded forward reference
translation; [#327/#331](primitive-dependent-sums.md) compare pair contracts;
and [#321](cubical-model-construction.md) and
[#322/#336](strict-two-groupoid-checkpoint.md) supply the bounded higher models.
The missing-work entries below describe the original assessment, not the
current absence of those results. No generic bialgebraic replacement follows
from their completion. A successor must first identify which proposed
compatibility results remain beyond the completed comparisons and which
consumer needs them.

## Required capability, independent of representation

Use the already selected [dependent memo](dependent-coherence-discovery/292-external-memo.md),
not a new theorem from #108. Its context contains

```text
x,y,z : A; p,p′ : Id_A(x,y); h : Id(p,p′); q : Id_A(y,z); u : B(x)
v(p) = tr(q,tr(p,u))
K(p) = Id_B(z)(v(p),tr(p·q,u))
η(p) : K(p)
apd_η(h) : Id_K(p′)(tr_K(h,η(p)),η(p′)).
```

The requirement concerns the chosen certificate η and action, including the
transported source `tr_K(h,η(p))`. Inhabitation of their endpoint types is
insufficient. Changing contexts by `σ : Δ → Γ` and `τ : Θ → Δ` must preserve
the dependent families, selected terms and their types, both sequentially and
under `σ ∘ τ`. Reconstructing the argument after substitution must agree with
substituting its retained recipe. These are object substitutions, not merely
renaming schematic parameters. Contextual J must support every admitted finite
dependent tail and motive, with beta and substitution laws.

For a change of setting, specify the context map and the family comparison
first; it determines where a section and its certificate land. Require identity,
composition and constructor compatibility for those comparisons. A strict map
may preserve equality without reflecting it. A coherent map may require
transport through an isomorphism; arbitrary equality of unaligned raw values is
not its contract. Retain a path-sensitive example and keep the separate
nontrivial second-identity observation as a model-construction gate.

The retained indexed client is the exact parser in
[IndexedParserComposition](../../Examples/IndexedParserComposition.lean).
Its intended output is `Decision (P word)`, with the selected witness, for every
word within the stated depth. The `fullMixed` client combines nullable star,
concatenation, scalar evidence, intersection and witness transport. Repeated
restriction must retain the same witness. The companion ordinary client is
[weighted composition](../../Applications/Languages/Compositional.lean), whose
meaning is a coefficient at each word; multiplication order matters over a
noncommutative semiring. A replacement must preserve both contracts and recover
the ordinary case without making those clients provide J or binding structure.

These requirements were used to assess the frameworks below. Neither an
operational step observer nor a common syntax tree is part of the specification.

## Evidence, versions and what changed

Local source inspected: `701023ce73ff297604fb21f2b6caada9e727c10c`, the reviewed
baseline requested by the issue and the integration base of this documentation
change. The seven issue-listed reports were read, including the
[previous adoption assessment](bialgebraic-semantics-adoption.md),
[construction/observation assessment](construction-observation-research-assessment.md),
[total higher-order comparison](higher-order-extensional-comparison.md),
[weak comparison](weak-higher-order-comparison.md),
[dependent architecture assessment](dependent-architecture-reassessment.md),
[guarded judgment report](dependent-judgment-representation.md), and
[constructor admission](dependent-constructor-admission.md).

Primary texts were reopened on 2026-11-05 at the versions linked below. The
arXiv version histories still list 2405.16708v5 (2026-05-29), 2602.18295v2
(2026-06-30), 2302.08200v4 (2023-09-28), 1503.02447v2 (2015-08-05), and
1307.2538v2 (2013-09-27). These match the pinned versions in the earlier reports;
this reassessment identifies no intervening revision of those papers. The
Turi–Plotkin text is the authors' LICS 1997 paper, rather than a claim about a
new edition. The changed evidence is the local dependent interpretation,
constructor and author work. Rechecking an old theorem against that evidence is
not a new published extension of it.

Labels below distinguish **published result**, **checked local theorem**
(inspected source with earlier acceptance, no new build here), **proposed
derivation**, **missing construction**, and **established obstruction**.
This is a targeted applicability comparison. #301 retains broader external
discovery; no exhaustive ranking of foundations is claimed.

## Published contracts and their applicability

**Turi–Plotkin: published result.** Abstract GSOS uses a natural rule
`Σ(Id × B) ⇒ BT`, with free syntax monad T. Sections 5 and 7 connect this to
lifting and distributive laws; the monad/comonad account assumes the relevant
free/cofree constructions. Theorem 7.1 equates distributive laws with the two
liftings. Corollaries 7.1–7.3 give initial/final bialgebra semantics when the
corresponding initial/final base objects exist. In Set, Corollary 7.4 obtains
full abstraction for B-bisimulation when B preserves weak pullbacks. This
conclusion concerns the selected B, not any independently chosen equality.
For our finite client, a lift of syntax preserving coalgebra maps is the
applicable pattern. A dependent signature/category, its free construction and
comparison to the memo remain missing constructions. [Turi and Plotkin,
*Towards a Mathematical Operational Semantics*, LICS 1997, §§5, 7](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf)

**Higher-order GSOS: published result.** Assumptions 4.2 require finite limits
and colimits, variables V, `Σ = V + Σ′` with free algebras, a mixed-variance
`B : Cᵒᵖ × C → C`, and a final `B(μΣ,−)` coalgebra. Definition 4.3 requires
dinaturality in pointed input X and naturality in successor Y. Theorem 4.14
makes the operational behavior kernel a congruence if C is regular, Σ preserves
reflexive coequalizers and B preserves monomorphisms (epimorphisms in its
contravariant input). Section 5 uses finite untyped contexts and renamings for
binding and substitution. This supplies a candidate theorem for sharing
higher-order congruence proofs. It supplies neither our dependent context
category nor a translation of its typed Id/J judgments. Calling the base a
presheaf category does not construct those objects or laws. [Goncharov et al.,
*Higher-order bialgebraic semantics*, v5, §§4–5](https://arxiv.org/pdf/2405.16708v5)

**Locally final denotation: published result.** Assumption 3.1 requires final
`B(X,−)` coalgebras. A locally final `Z → B(Z,Z)` is final for `B(Z,−)`;
Theorem 3.9 extends it to a compatible algebra under relative flatness
(Definition 3.5). Remark 3.8 diagnoses nested Y recursion against that format.
Theorem 3.11 gives denotational equality ⇒ behavioral equality for every
compatible bialgebra. Theorem 4.13 constructs Z in a stable M-category with a
terminal object and chain limits, contravariant local contractiveness,
covariant local non-expansiveness, inhabited `C(1,B(1,1))`, and convergent
final sequences. Inhabited hom-sets add uniqueness. Section 6 leaves the
converse/full abstraction and weak denotation open. The construction is useful
when such Z is wanted; comparison to our independently specified dependent
meaning is additional work. [Goncharov et al., *Towards a Higher-Order
Bialgebraic Denotational Semantics*, v2, §§3–4, 6](https://arxiv.org/pdf/2602.18295v2)

**Weak/lax congruence: published result.** Theorem VIII.6 uses IV.1 and VIII.1:
a complete, cocomplete, well-powered, locally distributive base with
pullback-stable strong epimorphisms; Σ preserving strong epimorphisms and
generating a free monad; preordered mixed-variance B with a lifting good for
simulations; and a pointed GSOS law admitting a relation lifting. Definition
VIII.2 requires lax-to-strict simulation conversion, identity-relation
reflexivity and its composition inequality. A weakening as in VI.4 must form
a lax bialgebra (VIII.4). The resulting weak similarity is a congruence;
Appendix E checks the call-by-name binding/substitution instance. It does not
supply a weak locally final domain or an identification with our chosen
partial denotation. Our call-by-value client still owes that instance's laws.
[Urbat et al., *Weak Similarity in Higher-Order Mathematical Operational
Semantics*, v4, §§IV, VI, VIII–IX and Appendix E](https://arxiv.org/pdf/2302.08200v4)

**Quotient descent: published result.** Under Assumption 2.2, `Alg(T)` has
coequalizers and U, TU, EU take its regular epimorphisms to base epimorphisms.
For equations `l,r : E ⇒ T`, Theorem 4.3 says a law `λ : TF ⇒ FT` descends
uniquely to the quotient monad precisely when
`Fq ∘ λ ∘ lF = Fq ∘ λ ∘ rF`. Propositions 4.10 and 4.12 extend the result
to copointed functors/comonads. This makes exact observation preservation an
explicit admission test for quotient equations. Supplying a dependent quotient,
transported output families and an appropriate law is still necessary for the
memo; the theorem does not manufacture them from raw Horn equality. It also
does not select representatives. [Bonsangue et al., *Presenting Distributive
Laws*, v2, §§2, 4](https://arxiv.org/pdf/1503.02447v2)

**Modular recursion: published result.** Assumption 2.1 requires binary
products/coproducts, a terminal H-coalgebra C and free K-algebras; 3.4 fixes an
abstract GSOS law. Theorems 3.5–3.6 construct completely iterative structures.
Theorem 4.8 extends these by guarded recursive program schemes under the
iteratability requirements of Definition 4.5. Theorems 5.14 and 5.23 give
unique interpreted solutions and extended iterative structure for the
specified GSOS-relative and sandwiched schemes. Solved operations can then be
used in later admissible definitions. This is relevant to recursive stream
clients, but our finite J recipe requires neither infinite behavior nor a
recursive solution theorem. Guarded recursion in this source and guards on
partial typing operations are different conditions. [Milius, Moss and
Schwencke, *Abstract GSOS Rules and a Modular Treatment of Recursive
Definitions*, v2, §§2–5](https://arxiv.org/pdf/1307.2538v2)

## What the direct approach already derives

[IndexedCompositional](../../SquareKit/IndexedCompositional.lean) proves
`Rule.layer_natural`, `fold_morphism`, `bind_morphism`, `join_morphism`,
`map_morphism` and `Behavior.observe_morphism`. These are **checked local
theorems** for a fixed index type and fixed output/request families. The output
is retained exactly at the final path index. The
[ordinary recovery](../../SquareKit/IndexedCompositionalOrdinary.lean) is also
checked. This is a bounded rule format, not a checked instantiation of all the
published categorical hypotheses.

For dependent arguments, [Theory.interpret](../../SquareKit/Internal/DependentJudgments/Theory.lean)
uses direct rule validity; [ContextualMaps.interpret_map](../../SquareKit/Internal/DependentJudgments/ContextualMaps.lean)
lifts primitive strict model-map laws to defined expressions.
[TypedMaps](../../SquareKit/Internal/DependentJudgments/TypedMaps.lean) obtains
definedness from source typing and transports suitable equality assumptions.
[FrozenMemo](../../SquareKit/Internal/DependentJudgments/FrozenMemo.lean)
compares the actual two substitutions and composite for value, family,
certificate, action and transported source;
[MemoUniformity](../../SquareKit/Internal/DependentJudgments/MemoUniformity.lean)
inherits their strict-map preservation. These are **checked local theorems**.
They already remove per-argument interpretation and map proofs from ordinary
authors. Primitive J preservation remains a model-builder obligation.

The [Sigma capability](../../SquareKit/Internal/DependentJudgments/Sigma/Capability.lean)
derives dependent elimination using both inverses of its comprehension
isomorphism. [Recovery](../../SquareKit/Internal/DependentJudgments/Sigma/Recovery.lean)
retains the old value, certificate, action and transported source exactly.
Those **checked local theorems** do not establish beta-only Sigma admission,
all-model expansion or conservativity. #327 owns the weaker comparison.

The following distinctions determine whether a generalization has supplied a
new capability.

| Requirement | Evidence now | Missing construction or proposed derivation |
| --- | --- | --- |
| Functions accepting functions; binding | Published higher-order results above; local `HigherOrderComparison.comparison` and `denote_subst` | Construct a rule-format instance if reusable operational congruence is the client need. This alone adds no dependent type formation. |
| Families varying over Γ; context extension | Local comprehension/pullbacks and guarded family/term rules | A proposed indexed or fibred bialgebraic presentation must define its base, families, substitutions and comprehension. A family over fixed I does not supply substitutions between varying Γ. |
| Dependent congruence and conversion | Direct guarded rule soundness | Establish presuppositions and correspondence to conventional judgments under #326. Generic untyped equality cannot be assumed to be that correspondence. |
| Arbitrary-tail contextual J | Local full-model law validation and constructed groupoid J | Show admissible dependent motives/branches and J compatibility in the competing presentation. Encoding a constructor name in Σ is insufficient. |
| Changes of setting | Generic strict maps; coherent native Type comparison | #325's general coherent comparisons need dependent transport and identity/composition laws. Naturality in a fixed base is not a construction of arbitrary changes of base or model. |
| Nontrivial higher identity | Source evidence and separate model programme | #321/#322 must supply the required sound higher interpretation. Function input variance and binding indices do not supply higher paths. |

The **proposed derivation** worth testing is a compatibility theorem over
reindexing families: construct the comparison for extension, then derive its
composition and telescope action, and use a stated J comparison to obtain the
memo's selected certificate/action comparison. The dependent premise cannot be
hidden inside an assumed theorem about the final memo. A successful result
could share infrastructure with an exact witness transport client. This has not
been constructed here, and it may belong more naturally to comprehension/model
maps than to coalgebraic behavior. #325's work should settle that allocation
before adding a second interface with the same obligations.

## Equality directions and discriminating failures

For clarity, let D be the independent client meaning and O a chosen observer.
`D(p)=D(q) ⇒ O(p)=O(q)` is preservation of D-equality by that observer. The
converse is reflection by O. Congruence only says a specified relation survives
constructors/contexts; it proves neither direction between D and O. A
full-abstraction claim must name both the semantic equality and contextual or
behavioral relation and prove both directions. Source adequacy in #326 instead
compares derivable typing/equality judgments. These statements have different
subjects even when called adequacy.

**Established obstruction: strong observation cannot factor through the chosen
extensional meaning.** [HigherOrderComparison.no_strong_adapter](../../SquareKit/HigherOrderComparison.lean)
uses zero and its identity redex: both denote zero, but their beta counts differ.
[WeakHigherOrder.no_strong_adapter](../../SquareKit/WeakHigherOrder.lean) retains
the obstruction for partial meaning. The failed condition is the factorization
of that strong observer through D, hence the proposed D-equality-to-strong-
behavior implication. It is not a refutation of the published theorem with its
own compatible denotation. The local `weak_iff` results identify ground weak
observations with their selected meanings; neither proves higher-order
contextual full abstraction or a general weak domain theorem.

**Established obstruction: Boolean agreement loses selected evidence.**
[ExactParserRewrites](../../Examples/ExactParserRewrites.lean) retains two
parsers with equal recognition and distinct left/right selected witnesses.
`selected_incompatible` rejects extending the recognition contract to those
selected observations. `IndexedParserCompositionExamples.resetting_cut_fails`
rejects replacing a retained nullable-star witness by the canonical empty
witness during restriction. Both recognize the same word. An equation making
that replacement therefore fails the exact output compatibility law. An
exact-witness quotient cannot admit it merely because recognition descends.
This gives a concrete rejection test for any proposed shared quotient layer.

**Established obstruction: raw evaluation need not commute with a lossy map.**
[GuardedJudgmentBoundaries.no_unconditional_interpretation_map](../../Examples/GuardedJudgmentBoundaries.lean)
exhibits malformed family substitution becoming valid after indices collapse.
The failed hypothesis is source definedness. `TypedMaps` retains the guard;
turning all raw expressions into a total algebra homomorphism would assert a
false stronger contract. Separately, `no_source_equality` rejects reflection
from agreement in one interpretation. These are local counterexamples, not
claims that every categorical encoding must use this totalized representation.

A further strictness discriminator is
[GroupoidComprehensionBoundary.shear_not_horizontal](../../Examples/GroupoidComprehensionBoundary.lean):
a commuting total-space square need not preserve the chosen horizontal lifts.
Consequently all display squares cannot silently become strict
cleavage-preserving family maps. A coherent comparison may be viable, but must
construct the appropriate comparison data. Likewise the existing groupoid memo
retains first-path sensitivity while its second identity is reflexive; it is
not the missing higher-model witness. See
[GuardedGroupoidMemo](../../Examples/GuardedGroupoidMemo.lean).

## Recommendations, promotion conditions and ownership

| Component | Decision | Concrete promotion condition / consumer |
| --- | --- | --- |
| Local algebra/observation compatibility | Adopt and retain | Keep the indexed parser and ordinary weighted contracts and direct APIs. No new framework is needed to preserve already proved finite composites. |
| Dependent comparison across settings | Investigate with #325/#289 | Use the fixed memo and exact parser transport as consumers. Derive a reusable family/section/telescope comparison, retain chosen η and transported apd source, prove unit/composition, and identify a primitive or repeated proof it removes. |
| Higher-order congruence format | Adapt only for an operational congruence client | A successor under #235 must construct the law, variance and existence hypotheses and recover the selected total/partial higher-order client's observations. Binding alone does not promote it to the dependent foundation. |
| Locally final domain construction | Defer for these dependent clients | Select an independently needed domain; construct its hypotheses and a typed relation/map to D with application/substitution compatibility. State strong/weak observations and each equality direction separately. |
| Weak/lax lifting | Investigate when weak congruence is required | Use the partial higher-order caller, construct its actual CBV weakening and lax law, and retain return/divergence distinctions. Do not substitute the published CBN instance. |
| Quotient descent | Adapt for an actual exact-observation quotient | First retain the parser transport-fusion/context theorem and reject selected-witness collapse. Construct quotient and descent, including output-family transport if indices change. Existing semantic rewrite equality is not already a quotient monad. |
| Modular guarded recursion | Retain bounded stream method; defer generic retrofit | A new recursive consumer must exceed the existing coordinate-guarded/compiler contract and recover every independent sequence coordinate. Coordinate uniqueness does not solve J or source adequacy. |
| Entire framework as dependent foundation | Defer adoption, keep investigation eligible | Recover the specified judgments, exact selected data, ordinary/indexed clients and model-change contract. A source-to-model theorem and the higher-model gate require separate evidence. |

The suggested dependent successor is an extension of #325's comparison work,
not authorization to duplicate it: first record whether existing comprehension
laws already derive the proposed infrastructure. Only if a distinct reusable
bialgebraic construction remains should #235 scope a new implementation issue.
Its acceptance must name the comparison category, derive compatibility beyond
per-client assumptions, exercise two nontrivial substitutions and unequal
family presentations, and retain the failure cases above. If it proposes a
replacement for indexed composition, also recover the native parser's exact
`Decision` values, weighted noncommutative order, fold/bind/map laws and ordinary
specialization. No replacement is recommended by this report.

#326 owns conventional source adequacy; #327 owns weaker Sigma; #321/#322 own
higher models. Those results are dependencies only for claims that use them,
not blockers to this applicability assessment. #295–#301 retain their
comparisons and discovery; #306 stays with its current session. #107 remains
paused, #108 unselected/unprepared, and #260 inactive. No universal AST,
observation functor, equality policy or module hierarchy is selected.

## Validation boundary

This change contains research prose and links only. Source declarations and
primary theorem statements were inspected; their existing proofs were not
changed or revalidated by a Lean build. Documentation validation checks relative
link targets and whitespace. Independent Standards/Spec review and integration
acceptance are recorded by the coordinating implementation workflow. No new
formal specialization was needed to decide the present applicability question:
the existing selected-witness, step-count and malformed-map counterexamples
already discriminate the proposed shortcuts.
