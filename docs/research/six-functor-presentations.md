# Indexed and higher presentations of six-functor arguments

Retain the ordinary Künneth construction and its derived coherence interfaces.
Investigate higher correspondence semantics through a bounded comparison that
retains the selected boundary witnesses. Add exceptional internal Hom locally,
without requiring a full six-operation model of existing slice clients.

This is the comparative research deliverable for
[#571](https://github.com/VladimirMarko/conaled/issues/571), at repository base
`b202bc865dc3aaf135e117b647bef23bf3b269fa`, Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. It adds no Lean declarations.
Existing proofs were inspected; proposed constructions below remain unimplemented.
The [K/H/T contract](six-functor-reusable-argument.md) and
[current Künneth implementation](kunneth-formalization.md) jointly define the
checkpoint. The earlier contract's proposed K implementation is already delivered
by #570. It must not be scheduled again from that historical next-step paragraph.

## Sources and independent assessments

Scholze's October 2025 Definitions 2.3–2.5 use a groupoid of correspondences,
a lax symmetric monoidal interpretation, and right adjoints. For an ordinary
base the correspondence category has invertible apex comparisons. Definition/
Proposition 3.2 describes its simplices by cartesian diagrams; the general
coherence theorem requires mathematical construction. Lecture I supplies the
proper Künneth example. [Primary notes, printed pp. 6–8, 16–19](https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf).

Cisinski–Déglise's Theorem 2.4.50 supplies exceptional operations for separated
finite-type maps and the PF/Hom formulas. Examples 1.4.3 and 2.4.48 identify
`SH` as an instance. Sections 1.1.15–16 and 1.1.31–32 specify adjunction-derived
exchange maps and their compatibilities. These support the paper contracts;
they do not constitute a local Lean motivic model. [Primary book, arXiv v4,
printed pp. 8–12, 28, 77–79](https://arxiv.org/pdf/0912.2110v4).

The source PDF SHA256 hashes are respectively
`9bbe7e452401b2a9bbe8bdeb719704cb336ccc889e2b2289320ecc2ac930d1b3` and
`ef936de6073bd1108673610fb767d1aad19c73b57ea0762d5fdc240962bdc477`.
The repository stores this analysis, not copies of those PDFs.

Three design assessments share a [neutral brief](six-functor571-design/brief.md):
[Foundations](six-functor571-design/foundations.md),
[Use](six-functor571-design/use.md), and
[Alternatives](six-functor571-design/alternatives.md). Their initial versions are
preserved. The use assessor's [factual correction](six-functor571-design/use-update.md)
withdraws its initial proposal to rebuild K/T after inspecting the newer modules.
Two assessors had fresh context. Host thread limits required reusing the third,
whose prior #687 review is disclosed. No assessor read another's report before
saving its own. The use assessor sent an early factual progress message; this
departure from the brief is recorded in its report. These assessments are design
evidence, separate from independent Standards/Spec acceptance.

The reports agree on retaining ordinary proof reuse. They propose different
next tests: a groupoid boundary, or a genuinely higher cell connected to
composition. Both matter. The first has the smaller missing construction;
it does not answer the second. The plan below keeps that distinction explicit.

## Capabilities already constructed

| Contract | Current construction | Provider obligations and remaining limits |
|---|---|---|
| K: the specified proper Künneth isomorphism | [Kunneth](../../SquareKit/Kunneth.lean) defines the PF/BC/PF map, identifies BC with its mate, proves its counit characterization E, and separately constructs its inverse. | Invertibility of the three actual components is required. The local map itself permits oplax monoidal inputs. No exceptional operations or internal Hom are needed. |
| Indexed K | [KunnethIndexed](../../SquareKit/KunnethIndexed.lean) constructs the square from pseudofunctor comparisons and `pushComp` by chosen-adjoint uniqueness; `kunnethIso` and `kunneth_counit` retain those choices. | Supply indexed monoidal fibers, chosen adjunctions, monoidal identity/composition comparisons, admissibility closed under identity/composition/pullback, canonical PF for all coefficients and appropriate BC. |
| T: preservation of the named K map | [KunnethTransport](../../SquareKit/KunnethTransport.lean) derives tensor-transpose transport, conjugation and inverse transport. Native monoidality derives tensor compatibility. | Routes supply the component evaluation equations and actual endpoint comparisons. A universal indexed route builder is not implemented. Endpoint isomorphism alone does not prove T. |
| H: exceptional internal Hom | The natural Hom-chain is specified in the contract report. | A local checked theorem still needs closed fibers, ordinary and exceptional adjunctions, and exceptional PF. No such package was found in the audited modules. H transport needs further compatibility beyond T. |
| Native dependent operations | [DependentBaseChange](../../SquareKit/DependentBaseChange.lean), [ExponentiablePullback](../../SquareKit/ExponentiablePullback.lean), [AdjointComparison](../../SquareKit/AdjointComparison.lean), and [AdjointSquareTransport](../../SquareKit/AdjointSquareTransport.lean) construct changed adjoints, chosen-adjoint comparison, evaluation/curry laws and mate pasting. | Preserve actual pullbacks and chosen adjunctions. Their proofs do not assert general mate invertibility. |
| Maps of bases | [MixedBaseChange](../../SquareKit/MixedBaseChange.lean) constructs comparison and pasting before requiring preservation for invertibility. | Pullback preservation suffices. [GeometricMorphism](../../SquareKit/Internal/GeometricMorphism.lean) has the stronger finite-limit-preserving adjoint contract; it is not required of ordinary span clients. |

[KunnethPredicates](../../SquareKit/KunnethPredicates.lean) supplies a complete
ordinary example: fibers `Set (X × I)`, intersection tensor, preimage pullback,
universal-quantifier pushforward, and surjections as admissible maps. Recoloring
supplies a nonidentity interpretation and transports K through canonical mates.
[Its client](../../Examples/Kunneth.lean) uses `Bool × Bool → Bool`, variable
coefficients, an object outside the recoloring image, and inverse transport.
Its separate nonthin selected map retains a Boolean tag and deliberately fails
surjectivity. That control is not a complete nonthin indexed K/T model. The
generic proofs do not depend on thinness; model-level coherence currently does.

Constructed ordinary examples, source expressibility, and proof transport are
three distinct results. None establishes a motivic model, full higher semantics,
or an author productivity comparison. #572, #573 and the frozen #604 author trial
retain their respective scopes.

## Universes, legs and dimensions

The indexed provider has base `C : Type u`, `[Category.{v} C]`, fiber objects
`Type z`, and fiber homs `Type w`. Its target is `Cat.{w,z}`, whose bundle is in
`Type (max (z+1) (w+1))`; functors and transformations between fixed fibers are
in `Type (max z w)`. The local K calculation allows four independent object/hom
universe pairs. No smallness of a motivic category follows from this signature.

The slice action has `Over X : Type (max u v)` and slice homs in `Type v`, hence
target `Cat.{v,max u v}`. Its base only needs pullbacks. Both span leg classes are
unrestricted. `SpanInterpretation` currently aligns the two base universe pairs;
`MixedBaseChange` already permits independent pairs. That local alignment is an
interface limit, not a mathematical obstruction.

For K, the proper class needs identity, composition and pullback closure. For the
full higher proposal take arbitrary left legs, right legs in `E`, finite limits,
and `E` containing isomorphisms and closed under composition, pullback and the
diagonals specified in the frozen Lecture III setup. Tensor and exceptional
structure are additional capabilities. The slice action's `Over.map` is dependent
sum, not K's right-adjoint pushforward; the shared composition example does not
identify these operations.

| Dimension | Ordinary indexed/derived representation | Higher proposal |
|---|---|---|
| Objects and coefficients | Actual objects and dependent selected payloads. | Actual objects with their higher identity structure. |
| Arrows and comparisons | Morphisms, functors, apex maps, natural transformations and specified isomorphisms are data. | Edges and higher comparison cells with specified faces are data. State whether noninvertible apex maps are included. |
| Laws between comparisons | Equality of composites lies in `Prop`; associator and unitor components themselves remain data. | An observable path between comparisons needs a further data type and its boundary/composition operations. Laws about those data may remain propositions. |
| Further dimensions | No independent observable proofs of equality. | Either explicitly stop at a finite dimension or supply a coherent unbounded representation. |

A proposed simplicial representation can fix base simplices in `Type κB` and
fiber simplices in `Type κF` at each level; the collection of such small structures
uses successor universes. This is a size convention, not an implemented
`Cat∞`/motivic size theorem. The bounded groupoid pilot below uses object and arrow
universes `uG,vG`, comma objects in `Type (max uG vG)` and arrows in `Type vG`.
Its finite client uses `Type 0`.

There is already relevant higher infrastructure. Mathlib's quasicategory
certificate is propositional, but its simplices remain data; a selected filler
must be retained when observed. Passing to a homotopy category discards further
observations. [DoubleDelooping](../../SquareKit/DoubleDelooping.lean) and
[SecondIdentity](../../Examples/SecondIdentity.lean) retain distinct 2-cells,
compose them, transport their labels, and reject reconstruction from a locally
discrete category or host equality. The [strict two-groupoid checkpoint](strict-two-groupoid-checkpoint.md)
also retains dependent cells and contextual identity elimination. Thus Lean's
proof irrelevance is not a general obstacle to encoding higher objects as data.
None of these modules constructs the proposed higher correspondence interpretation.

Scholze's correspondence hom-groupoids retain invertible apex comparisons.
Our ordinary span bicategory also has noninvertible apex maps. A restriction to
the correspondence core cannot recover that whole API. Keep the ordinary route,
or prove an extension with the needed noninvertible cells. Conversely, the
ordinary equality interface cannot promise to recover all higher paths.

## Composition and preservation under the original assumptions

[SpanAction](../../SquareKit/SpanAction.lean) sends `X ←l W →r Y` to
`Over.pullback l ⋙ Over.map r`. `compositionIso` goes from the composite action
to sequential action. Its whole-isomorphism theorem identifies it with the
independently assembled Beck–Chevalley construction; projection lemmas recover
the payload and both apices. `pseudofunctor` derives whiskering, associator and
both unit laws. Those laws are proved rather than added as caller obligations.

The [three-span example](../../Examples/SpanAction.lean) duplicates `(n,b)`,
matches doubled indices, then forgets the final base while retaining another
witness. Input payload `(3,last : Fin 4)` and apices `(3,true)`, `3`, `(4,1)` survive
both compositors. The associator is evaluated on that input and both units are
checked. An odd matching index fails. A noninvertible collapse identifies the
Boolean branches while preserving payload. Final-base equality at `PUnit` would
miss these observations.

[SpanInterpretation](../../SquareKit/SpanInterpretation.lean) uses an actual
pullback-preserving functor `F`, its selected pullback comparison and `Over.post F`.
The resulting `StrongTrans` need not have equivalence components. Whole
`composition_transport` and `beckChevalley_transport` preserve the chosen
composite-apex comparison. [Its client](../../Examples/SpanInterpretation.lean)
composes `Over base → Over Bool → Type`, retaining the dependent payload and apex
through successive comparisons. Forgetting from `Over Bool` preserves pullbacks
but fails finite-limit preservation. Inhabitedness truncation fails the actual
pullback of false/true point maps. Both distinguish the required hypothesis.

`native_recovery`, `native_twice_recovery` and `native_tagged_recovery` recover
whole original `Selected` values for arbitrary type families and substitutions,
including the alternative chosen adjunction. They do not add exceptional,
monoidal or geometric-morphism assumptions. Native twice-recovery and the explicit
three-span associator are separate checks. #633 owns the further interpretation-
variable pseudofunctor comparisons and invertible modifications; the current
component equations do not close it.

## Author expressions and rejection points

The ordinary K endpoint already exists:

```text
Indexed.kunnethIso laws square proper_f proper_g A B
```

Its builder installs the indexed structure and proper laws once. A caller supplies
the actual square, original admissibility witnesses and coefficients. Elaboration
must derive admissibility of the pulled-back leg and select the actual PF/BC maps
and chosen-adjoint composition. `empty_projection_not_iso` rejects the predicate
empty-map example despite its ordinary adjunction.

Proposed H syntax is `exceptionalHom f A B`; it is not an implemented parser.
For a fixed map it should construct the natural chain

```text
Hom(T, [f_! A,B]) ≅ Hom(T ⊗ f_! A,B)
  ≅ Hom(f_!(f* T ⊗ A),B) ≅ Hom(f* T ⊗ A,f^! B)
  ≅ Hom(f* T,[A,f^! B]) ≅ Hom(T,f_*[A,f^! B]).
```

The obligations are closed symmetric monoidal fibers, `f* ⊣ f_*`,
`f_! ⊣ f^!`, and the specified natural exceptional PF isomorphism. Yoneda consumes
naturality in `T`; the result must also retain variance in `A,B` and inverse laws.
This local theorem needs neither a BC square nor purity. An ordinary K provider
must reject H at its missing exceptional adjunction/PF. Substituting `f_*` for
`f_!` does not solve the nonproper open-immersion contract.

For `transportSpecifiedK route K`, the route must preserve the specified tensor
transpose and its endpoint conversions. Monoidality and counit compatibility
supply the existing T proof. The Foundations report gives a paper control: using
minus identity as an arbitrary pushforward comparison in a constant rational-
vector-space model makes input signs cancel and output sign persist. The endpoint
isomorphisms exist but violate the required unit/counit law. This is not a new
checked Lean example. Strong monoidality also need not preserve internal Hom;
H transport therefore has its own compatibility obligations under #573.

A higher author expression must declare whether its comparison denotes an
ordinary isomorphism or a selected higher cell. Missing coherent interpretation
or mapping-space adjunction data cannot be filled by proof irrelevance. This is
a missing model input, not a failure of the ordinary K theorem or a measured
elaboration problem.

## Bounded next implementations and decisions

**First higher checkpoint: retain the groupoid boundary through composition.**
Reuse Mathlib `Comma` and the boundary-retaining pattern in
[QuotientPointedArcs](../../SquareKit/QuotientPointedArcs.lean). That module proves
a specialized quotient-chart equivalence; it does not already implement a generic
groupoid-span compositor. The proposed pilot is:

1. Form the comma groupoid of `1 → B(C₂) ← 1`. Its objects retain the selected
   boundary arrow. Construct the two distinct labels and their observations.
   Prove that forgetting the boundary to the strict object-level pullback cannot
   reconstruct both labels.
2. Compose `1 ← 1 → B(C₂)`, `B(C₂) ← 1 → 1`, and
   `1 ← Discrete Bool → 1`. Construct both iterated comma presentations and their
   reassociation equivalence, preserving the boundary label and Boolean. Check
   the selected associativity and unit comparison equations. Do not claim a
   generic pseudofunctor pentagon from one chain.
3. Use the existing `SecondIdentity.Bit ≃* Label` representation change. Prove
   preservation of the actual boundary and composite projections. On discrete
   groupoids, prove recovery of ordinary chosen pullbacks through the explicit
   equivalence, and connect to the existing span/native recovery observations
   without strengthening their assumptions. Keep arbitrary apex maps available
   through the ordinary API.
4. Record constructed versus supplied laws and the exact truncation. Reuse
   `SecondIdentity` as the independent second-dimensional control. The comma
   boundary is a lower-dimensional test: passing it does not establish a
   dependent 2-cell comparison between transformations.

That last, genuinely higher comparison remains under #555: connect a selected
nonzero dependent cell to actual composition/transport and threefold reassociation,
using the existing two-groupoid model. A disconnected cell tag is insufficient.
A full higher correspondence model, unbounded coherence and its interpretation
maps remain further obligations. The pilot is chosen for its bounded information
boundary, not as a replacement for those goals.

**Independent ordinary checkpoint: construct H locally.** Use the Hom-chain above,
with naturality and inverse laws, then specialize to set families over
`f : Bool → Unit`: `f_!` is dependent sum, `f*` reindexing, `f_*` dependent product,
`f^! = f*`, tensor is product, and internal Hom is functions. The example must
retain an actual function on the selected dependent pair and reject application
without exceptional PF/adjunction structure. This is a proposed ordinary model,
not a geometric claim of properness or a full K proper-law model. Scope this
checked theorem separately from #573's sourced motivic transport study.

| Decision | Consequence |
|---|---|
| Adopt/retain | Direct small-contract K and native APIs, with their existing derived indexed/coherence layers and whole selected-map recovery. |
| Investigate | The bounded boundary pilot and local H theorem; a complete nonthin K/T route as additional evidence under #555. Add a generic route builder only for demonstrated repeated obligations. |
| Defer | Full higher interpretation adoption, motivic realization construction and any foundation migration. Keep #572/#573 and #555's wider mathematics owned. No productivity ranking before #604's independent trial. |
| Reject | Mandatory six-operation migration for slice clients, general mate invertibility, endpoint-only T, erasure of observable witnesses, and claims that mere notation constructs a model. |

The next implementations need checked applications, statement review, full
applicable build/audit and independent acceptance. This research deliverable uses
source/contract inspection, preserved independent assessments and documentation
validation. It provides neither fresh execution results for the unchanged Lean
library nor resource/productivity measurements. Mathematical information-loss
controls, missing encodings and unmeasured elaboration costs remain separate.
