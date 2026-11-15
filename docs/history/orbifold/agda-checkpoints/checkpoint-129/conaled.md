# Handoff for conaled

This is the single outward-facing comparison report. Exact reference pins,
resolution metadata and the selected upstream Git blob identities live in
[environment.json](../environment.json). Current Agda acceptance is determined
by [state.json](../state.json) and its applicable raw evidence. This report supplies
mathematical scope, not a second proof ledger.

Repository access now works through the GitHub connector. The selected immutable
commit was resolved from master and rechecked before this refresh. All retained
reference bytes were checked against their Git blob identities at that commit;
newly copied files were checked in full. These are selected references, not a full
Lean checkout. No fresh local Lean build or cross-checker proof import is claimed.
The bounded smooth-source account is
[smooth-source-interpretation.md](../references/conaled/docs/research/smooth-source-interpretation.md).
Its final acceptance is recorded in
[issue #433's completion comment](https://github.com/VladimirMarko/conaled/issues/433#issuecomment-6781234863),
and the adopted documentation clarification is now present in the selected bytes.
The native cubical universe, compositional transport and weak groupoid-unit
constructions have their own source and acceptance boundaries, described below.
The current selection has 76 files. All 50 files from the preceding selection
remain byte-identical; their previously verified relation to accepted #420 is
unchanged. The eight new #528 modules, their example and report also have the
same Git blob identities at the accepted #528 commit and the refreshed tip.
The remaining additions retain actual mixed-change and manifold/action comparison
interfaces and the new six-functor research note. All selected bytes were checked
against the complete current Git tree. This does not establish equality of an
entire import closure or constitute a local Lean build. Exact pins and attributed
upstream validation metadata remain in `environment.json`.

## The external finite-action request is satisfied

At the retained reference, the construction uses literal `G × M`, the actual unit,
inverse and composition maps, the composable-pair equivalence, fixed-label local-
diffeomorphism charts, and exact Mathlib `IsProperMap` for the anchor. A label `g`
followed by `h` composes as `h*g`. The general compact-label properness theorem and
the finite discrete smooth specialization retain their stated continuity,
Hausdorff and smoothness hypotheses.

Neither effectiveness nor compactness of the object space is required. The disk,
ineffective trivial S3 action on the noncompact real line, multiplication-order
checks and trivial-group diagonal are useful controls. The classical Lean
dependencies remain explicit. The selected report is
[finite-action-presentation.md](../references/conaled/docs/research/finite-action-presentation.md),
and the implementation is
[FiniteActionPresentation.lean](../references/conaled/Applications/Orbifolds/FiniteActionPresentation.lean).
The finite-action implementation, disk specialization and example, and both
finite-action/properness reports have unchanged Git blob identities at the refreshed
pin. That identity check is not a new local Lean build.

## Properness transport retains its genuine obstruction

The independent replay in
[myers-properness-096-10-verification.md](../references/conaled/docs/research/myers-properness-096-10-verification.md)
agrees with the internal obstruction. For a set, the stated unrestricted
`DPProper` diagonal criterion forces decidable equality. The displayed Kock-field
and first-order Kock–Lawvere assumptions supply the conflicting nondiscreteness
condition. The external real-line diagonal is proper, even for the trivial group.
Thus these exact predicates cannot simply be identified under those assumptions.
This neither invalidates the external theorem nor excludes every possible
foundation for Myers's paper.

A valid transport theorem must specify admitted internal predicates/subobjects,
their interpretation, the exact external predicate, and the direction of
preservation. Restricting a quantifier, replacing a predicate, or strengthening
admission changes the theorem and must be explicit. The Agda compact-preimage
predicate `Compact.ProperData` is not silently identified with Mathlib
`IsProperMap` or unrestricted `DPProper`. The topological constructions below do
not alter this boundary.

## Newly available bounded source interpretation and generated descent

The accepted #433 integration includes the work previously separated as #445,
#446 and #447. Its source is still the unchanged
`Typed.Authoring.UniversalTransfer.proof`, consumed through the existing interpreter;
the quotient torsor groupoid and deformation family are assigned externally as its
base and fiber. The source-consuming theorem is not replaced by the semantic
`transport_comp` used to set up that family.

The following current interfaces were read at the resolved commit. Namespace names
are not necessarily module filenames; the source locations are explicit here.

| Interface and retained source | Constructed statement useful to this bridge |
| --- | --- |
| [SmoothQuotientGeneratedMatching](../references/conaled/SquareKit/SmoothQuotientGeneratedMatching.lean) | The same typed context derivation at local, double and triple overlap stages; actual local objects and overlap arrows with diagonal/triple equations. `restrictionFunctor` uses the actual parameter restriction on objects and arrows. No global extension is an input. |
| [SmoothQuotientCechContextEffectivity](../references/conaled/SquareKit/SmoothQuotientCechContextEffectivity.lean) | Constructor/normalized-context reasoning proves matching evaluation equivalence. Under local surjectivity, `SmoothQuotientGeneratedMatching.descentEquivalence` is built from the actual canonical restriction functor, not a freely supplied equivalence. |
| [SmoothQuotientGeneratedSectionDescent](../references/conaled/SquareKit/SmoothQuotientGeneratedSectionDescent.lean) | `restriction_substitution` is an equality of whole functors. `sectionTotalEquivalence` and `sectionTotalProjection` provide the total dependent comparison and its base projection, then `sectionDescent` reconstructs sections with vertical comparison data. |
| [SmoothQuotientCoverMatching](../references/conaled/SquareKit/SmoothQuotientCoverMatching.lean) | The diagram uses the original cover's actual categorical double/triple pullbacks. Constructed maps to and from its split presentation have both inverse laws; `matchingEquivalence` retains overlaps and selected arrows, and `restriction_toSplit` identifies the canonical restriction routes. |
| [SmoothQuotientGeneratedBaseChange](../references/conaled/SquareKit/SmoothQuotientGeneratedBaseChange.lean) | `primitive_square` is proved from actual quotient/deformation comparison maps. Its selected base natural isomorphism induces context comparison and a family modification; this is not equality of arbitrary groupoid objects. |
| [SmoothQuotientGeneratedBaseChangeSource](../references/conaled/SquareKit/SmoothQuotientGeneratedBaseChangeSource.lean) | `sectionCoherence` applies to typed contexts, families and terms. `universalTransfer_square` instantiates it with the original context, type and unchanged transport-composition proof. |

The integrated report supplies the larger account of family-constructor closure,
finite dependent tails, selected J comparisons and original-cover full-section
compatibility. The retained interface selection is not its complete transitive
implementation. Its reported checks preserve four origin automorphisms, nonzero
isotropy, distinct ineffective loops and the torsor without a global chart lift.
The acceptance comment reports a successful fresh run of 2,729 project modules
plus the exhaustive audit (2,730 checked modules total), exact-candidate receipt
verification, independent Standards/Spec review, and transitive axiom union
`propext`, `Classical.choice`, `Quot.sound`. This is attributed upstream validation;
we have not independently rerun that Lean build here.

The updated
[smooth-descent-prerequisites.md](../references/conaled/docs/research/smooth-descent-prerequisites.md)
now explicitly marks its primitive construction and remaining-work list as a
historical partial checkpoint. Its mathematics remains useful within that scope.
The integrated report now includes the exact #433 acceptance reference. These
are verbatim upstream changes, not local edits to the reference files.

### Consequences for the actual Agda bridge

These are now available external comparison targets, not tasks we should keep
reporting as absent from conaled. The pending work on our side is to connect the
actual Agda sources and substitutions to the admitted typed fragment, with exact
constructor preservation and universe levels. In particular:

* Compare local Čech data, descended objects and arrows, and actual restriction
  functors, rather than just the quotients' object sets. The selected total-space
  projection comparison is part of the section transport obligation.
* Relate the Agda torsor/action conventions to the quotient convention `m = g·n`:
  forward quotient transport uses the inverse label. Geometric action composition
  is still `h*g` for `g` followed by `h`. The bridge must prove the change of
  convention and all action/restriction equations, not identify notation.
* Interpret an admitted source derivation and its substitution/J rules, then apply
  the proved selected square to that derivation. A direct proof of its target
  equality would not establish source transport. The Lean `Type 1` quotient
  objects and explicit universe lifts do not authorize resizing in Agda.

This is a direction for further construction, not a new Agda theorem. The bounded
source does not provide source terms for general dependent sums, universes, BG,
univalence, cohesion or crisp judgments. Its completed generated descent does not
supply a model of the whole Myers development, general microlinearity or hyperdescent,
and it does not change the properness obstruction. The classical axiom ledger
stays external to our constructive branches.

## Native small universes and constructed univalence

The selected new implementation supplies actual code-valued natural maps and
chosen lawful operations. It is a separate semantic construction from the bounded
source interpreter above.

| Retained source | Constructed interface and exact boundary |
| --- | --- |
| [SmallFamilyClassification.lean](../references/conaled/SquareKit/Internal/Cubical/SmallFamilyClassification.lean) | `LocalFamily.code` constructs the contextual code map; `decode` constructs its native family. Coding and decoding commute with context substitution. `decodedLocalFilling` constructs the chosen filler and proves its boundary and uniformity under every cube morphism. The decoding/coding isomorphism preserves that actual selected filler. |
| [SmallFamilyConstructors.lean](../references/conaled/SquareKit/Internal/Cubical/SmallFamilyConstructors.lean) and [SmallFamilySubstitution.lean](../references/conaled/SquareKit/Internal/Cubical/SmallFamilySubstitution.lean) | Actual Sigma, Pi, dependent Path and discrete codes use the existing lawful providers after decoding. The exported decoding comparisons are isomorphisms of the actual families, with selected-operation substitution laws. These interfaces use explicitly raised small contexts; they do not assert unrestricted cumulative universe closure. |
| [NativeUnivalence.lean](../references/conaled/SquareKit/Internal/Cubical/NativeUnivalence.lean) | For `Γ : Context.{u+1}` and actual maps `a b : Γ ⟶ smallFamilyCodes.{u}`, `univalence a b` constructs `HomotopyEquivalence (pathToEquiv a b)`. Inverse homotopies and contractions are constructed, not supplied as the conclusion's hypotheses. |
| [NativeUnivalenceSectionBeta.lean](../references/conaled/SquareKit/Internal/Cubical/NativeUnivalenceSectionBeta.lean) and [NativeUnivalenceInverse.lean](../references/conaled/SquareKit/Internal/Cubical/NativeUnivalenceInverse.lean) | Section beta and the right inverse preserve the entire pair of map and selected homotopy-equivalence witness under arbitrary substitution. The left inverse uses the same constructed `equivToPath`/`ua`. Equality of maps alone does not discard the chosen witness. |
| [NativeUnivalenceMapNaturality.lean](../references/conaled/SquareKit/Internal/Cubical/NativeUnivalenceMapNaturality.lean) | `pathToEquiv_conjugate_reindex` identifies the actual natural transformation after reindexing and conjugation. Its section calculations are followed by a generic-term/extensionality argument; the final univalence theorem therefore concerns the specified actual map. |

The classifier has fibers at level `u` and codes at `u+1`. Its raised contexts and
the large-context native decoder use explicit `ULift`; no resizing follows. The
final univalence declarations are noncomputable semantic constructions. They are
not an evaluator, normalization theorem, or source-language judgmental conversion.

The live completion reports for
[#419](https://github.com/VladimirMarko/conaled/issues/419#issuecomment-6821507447)
and [#420](https://github.com/VladimirMarko/conaled/issues/420#issuecomment-6853892202)
record accepted publication, integrated checking, exhaustive axiom inspection and
independent review at their stated commits. The #420 report supersedes the retained
research report's earlier pending integrated-validation wording. The reported
axiom union is `propext`, `Classical.choice`, `Quot.sound`. These are attributed
upstream results; their temporary raw validation receipts have not been imported
as our proof evidence.

The [source-rule ledger](../references/conaled/docs/research/cubical-glue-source-rule-ledger.md)
keeps the exact pinned Agda empty-face `equivProof` computation and split
`transp`/`hcomp` reductions as separate source-admission obligations in #422.
Circle elimination remains #421. The newer semantic constructions do not enlarge
the unchanged #433 typed source fragment automatically.

For the selected finite-branch theorem, these codes address a real kind of missing
semantic ingredient: maps into a universe with actual contextual decoding. The
specific `predicate-code` in [Source interpretation](source-interpretation.md)
still needs codes for its actual domain and target, dependent Sigma and ordinary
identity/J admission, its decoding/substitution comparisons, and a derivation of
the actual Agda term. Native Cubical Path codes are not that ordinary identity/J
interpretation. Native cubical presheaf codes also do not by themselves classify
the current sheaf families or construct their smooth/higher interpretation.

Three construction patterns are useful now: retain the complete certified term
through substitution; separate its section computation from equality of the
actual comparison maps; derive both inverse laws for the operation already
constructed. These guide our own proofs without adding conaled's model as an
Agda premise or changing the crisp, properness or universe boundaries.

## Compositional univalence and selected transport

The live [#528 completion report](https://github.com/VladimirMarko/conaled/issues/528#issuecomment-6885492858)
is accepted and closed. Its actual retained constructions extend the previously
available native universe:

| Source | Actual construction and retained scope |
| --- | --- |
| [HomotopyEquivalenceComposition](../references/conaled/SquareKit/Internal/Cubical/HomotopyEquivalenceComposition.lean) and [its substitution laws](../references/conaled/SquareKit/Internal/Cubical/HomotopyEquivalenceCompositionSubstitution.lean) | Construct the equivalence of the actual composite from genuine contractible fibers and lawful selected fillers. `comp_reindex` retains the complete selected equivalence, including contraction data. The input is not restricted to an isomorphism. |
| [DependentTransportComposition](../references/conaled/SquareKit/Internal/Cubical/DependentTransportComposition.lean) and [NativePathComposition](../references/conaled/SquareKit/Internal/Cubical/NativePathComposition.lean) | Actual dependent transport has native identity, reversal and concatenation comparisons. The chosen dependent square and comparison body commute with substitution. Constant-path transport is not assumed strictly regular. |
| [CompositionalUnivalence](../references/conaled/SquareKit/Internal/Cubical/CompositionalUnivalence.lean) | Constructs ua identity/composition comparisons and a selected inverse from transport along reversed ua, with both inverse homotopies. This inverse remains restricted to universe-admitted codes. |
| [NaturalUnivalenceLaws](../references/conaled/SquareKit/Internal/Cubical/NaturalUnivalenceLaws.lean), [UnivalenceLawParameters](../references/conaled/SquareKit/Internal/Cubical/UnivalenceLawParameters.lean) and [NativeUniverseSquares](../references/conaled/SquareKit/Internal/Cubical/NativeUniverseSquares.lean) | Classifiers retain full equivalence records. Their public identity/inverse/binary-composition comparisons have exact whole-square recomputation laws. At fixed endpoints `comparisonSquare_injective` retains the entire native two-path, not only endpoint observations. |

There is an explicit two-path between the two triple bracketings and four
boundary equations. There is no claimed pentagon or chosen recomputation law
for that additional triple comparison. The [example](../references/conaled/Examples/CompositionalUnivalence.lean)
uses Boolean negation twice, successor/predecessor, both triple bracketings and
a genuinely varying Fin(n+1) family. Its equivalences on that finite family are
identities. Native paths remain distinct from host equality; the Boolean path
term distinction does not compute a fundamental group. The [report](../references/conaled/docs/research/compositional-univalence.md)
states these limits explicitly. Upstream reports a full candidate build, exhaustive
three-axiom audit and independent Standards/Spec acceptance; none was rerun here.

### The useful next upstream task: arbitrary-context constructors

Live [#529](https://github.com/VladimirMarko/conaled/issues/529) is open and
explicitly incorporates completed #528. The gap is visible in the signatures:
`sigmaCode`, `piCode` and `pathCode` take a small `Gamma : Context.{u}` and
produce code maps on `raisedContext Gamma`; the existing `liftedDecode` and
`NativeDecode.filling` already work for arbitrary `Xi : Context.{u+1}`.
Constructor decoding isomorphisms and selected-filling substitution laws over
raised small contexts are delivered capabilities to reuse. They do not yet
provide those constructor operations over arbitrary larger code contexts.

This matters to the full Myers code context, whose parameters include types
and families themselves. It is not legitimate to treat every such larger
context as the raising of a smaller one. A useful new consumer starts with
actual code parameters Y over Xi, an actual count n, the constructed Fin(n)
code and its label context Lambda, a code D over Lambda, a target section s
over the D extension, and an endpoint section e of Y. It constructs

```text
P(gamma,i) = Sigma d : D(gamma,i), Path_(Y gamma)(s(gamma,i,d), e(gamma))
```

as a code with an actual decoding comparison. The outer Sigma over finite
labels is a further consumer of the same constructor. The endpoint should also
be instantiated as the actual generic variable after extending the context by
Y. A universal small discrete finite-family code can be pulled back along n;
the family must not be replaced by one fixed external Fin set. The genuinely
large code-parameter context remains present when applying the new constructors.

For two nonidentity substitutions and their composite, compare substitution of
the original construction with independent reconstruction from substituted
inputs. Retain the actual display lifts, weakened endpoints, decoder maps,
selected fillers and full records at every claimed equality. Inputs are the
actual code maps and typed sections; the output code, decoder isomorphism and
substitution square are not additional premises. Retain empty-domain behavior
and reject incompatible endpoints or spurious inhabitants. Native Path stays native Path; an eventual
proposition-valued specialization needs its own stated hypotheses.

This would supply a checked semantic constructor/transport interface shaped like
our missing code formation. It would not interpret our current Dedekind sheaf
model, ordinary Agda identity/J, generic BranchChart, source judgmental conversion
or the full crisp/modal foundation. Those remain separate local obligations.

### Other live work and a later finite-action adapter

Live [#532](https://github.com/VladimirMarko/conaled/issues/532) owns preservation
under a concrete nonidentity change of semantic setting. Context substitution
from #528 is an input test, not that theorem. [#554](https://github.com/VladimirMarko/conaled/issues/554)
owns inverses directly from arbitrary native contractible fibers, with actual
Glue recovery as its consumer. Neither is a prerequisite to be silently added
to #529. [#555](https://github.com/VladimirMarko/conaled/issues/555),
[#556](https://github.com/VladimirMarko/conaled/issues/556) and
[#557](https://github.com/VladimirMarko/conaled/issues/557) are open research
owners. The [six-functor report](../references/conaled/docs/research/six-functor-language.md)
does not claim an implemented full formalism. Actual
[mixed ambient/context comparisons](../references/conaled/SquareKit/Internal/GeometricMixedChange.lean),
[dependent base change](../references/conaled/SquareKit/DependentBaseChange.lean) and
[adjoint comparisons](../references/conaled/SquareKit/AdjointComparison.lean)
already retain projections and named identity/composition/evaluation laws;
they should not be requested anew as missing generic coherence.

The same applies to torsor descent: #433 and #445--#447 are closed. The current
[sheaf quotient](../references/conaled/SquareKit/SheafActionQuotient.lean)
constructs `chartArrowEquiv` from actual arrows to labels satisfying m = g·n.
Its [selected descent base change](../references/conaled/SquareKit/SheafActionQuotientDescentBaseChange.lean)
has recovery, uniqueness, naturality, identity and composition laws. The original
cover [matching](../references/conaled/SquareKit/SmoothQuotientCoverMatchingNaturality.lean),
[family](../references/conaled/SquareKit/SmoothQuotientCoverFamilyNaturality.lean) and
[section](../references/conaled/SquareKit/SmoothQuotientCoverSectionNaturality.lean)
comparisons handle actual commuting cover squares and compatible full gluings.
These split sheaf identities do not replace our whole continuous-bundle laws.

A separate useful proposed development is to generalize
`SmoothDiskPresentation.smoothChartEquiv` from C4/disk to the generic finite
smooth action, initially within the existing Type-sized finite-dimensional real
boundaryless [manifold realization](../references/conaled/SquareKit/SmoothManifoldModel.lean).
The external finite-action presentation allows broader ModelWithCorners inputs;
that wider scope is not automatically represented by this model. Use the actual
[map interpretation](../references/conaled/SquareKit/SmoothManifoldInterpretation.lean),
[full-faithfulness](../references/conaled/SquareKit/SmoothManifoldFullFaithfulness.lean),
[principal-open maps](../references/conaled/SquareKit/SmoothManifoldPrincipalMaps.lean)
and [constant action](../references/conaled/SquareKit/SmoothConstantAction.lean)
to construct the sheaf action from the given smooth action. Compare its actual
trivial-chart arrows with independently specified smooth maps into G times M,
retaining source/target triangles, both inverses and smooth restriction.
The quotient label k becomes external forward label inverse(k); forward labels
g then h compose as h*g. Recover the disk comparison and add the ineffective
S3 action on the noncompact line, disconnected varying labels and empty-domain
controls. Atlas comparison must use the existing actual naturality maps.
This is an unimplemented proposal under #36/#32, not a new request to redo
generic descent or a proof of unrestricted DPProper. No issue was created.

### Copyable agent handoff for #529

Complete existing conaled issue #529, "Extend small-universe constructor
interfaces to arbitrary contexts and dependent transport." Start from current
master, check the current issue and repository instructions, and preserve the
accepted #419/#420/#528 constructions. The reviewed source identity and exact
upstream validation references are recorded in this checkpoint's environment.json.

The concrete gap is that sigmaCode/piCode/pathCode work over raisedContext Gamma
for Gamma : Context.{u}, while SmallUniverse.liftedDecode and its lawful selected
fillers already support arbitrary Xi : Context.{u+1}. Construct the corresponding
Sigma/Pi/Path code operations over arbitrary admitted larger contexts using
represented small charts. Reuse SmallFamilyConstructors, SmallFamilySubstitution,
UniverseDecode, DependentTransportComposition, NaturalUnivalenceLaws and
UnivalenceLawParameters. Construct decoding comparisons, lawful selected fillers
and substitution laws, stating every universe level and presentation map.
Distinguish code equality, family isomorphism, native path and semantic term
equation in the public contracts.

Meet the issue's dependent pair and dependent function transport requirements
along an actual supplied universe path, with explicit endpoint comparisons.
Preserve the actual selected maps, fillers and complete equivalence data wherever
the theorem claims exact recovery or recomputation. Reuse the delivered transport
and ua composition laws, and retain the existing whole-package consumer.

Add a concrete client motivated by finite-branch chart predicates. Keep an actual
larger context containing code parameters. Construct a varying Fin(n) code from
an actual count term, then its label context Lambda and projection. Take actual
code maps Y over Xi and D over Lambda, a target section s of the weakened decoded
Y over the D extension, and an actual endpoint e of decoded Y. Construct the code
for Sigma d:D(gamma,i), Path_(Y gamma)(s(gamma,i,d),e(gamma)), its decoding
isomorphism and selected-filling compatibility; also exercise the outer Sigma
over labels. Include an instance where e is the generic variable in the context
extended by Y. Reuse the existing varying finite-family construction, but keep
the larger code-parameter context so the new API is actually exercised.

Use two explicit nonidentity substitutions that change count, endpoint or code
data. Prove compatibility with each and their composite, comparing the substituted
original construction with the one independently rebuilt from substituted inputs.
Retain the actual dependent display maps, endpoint weakenings, decoder maps and
selected operations. The desired code, decoder equivalence and substitution
comparison must be outputs. Retain empty-domain and incompatible-endpoint
controls and genuinely varying fibers.

Keep the semantic boundary explicit: this is a native cubical client, not an
interpretation of the Myers Dedekind sheaf model or ordinary Agda Id/J. Any
proposition-valued specialization requires stated hypotheses. Do not infer
resizing, a cumulative hierarchy, source judgmental conversion or a full
smooth/cohesive model. Record the exact remaining source-admission and
model-comparison obligations; #422 retains its distinct source-conversion work.

Deliver reusable APIs, checked clients and rejecting cases, a statement/source
correspondence report, the repository's full candidate acceptance build and
exhaustive axiom audit, and independent Standards/Spec review. Report the exact
accepted commit and remaining work. Work under existing #529; no duplicate issue
is needed.

## Constructed weak groupoid-unit elimination

[WeakUnit.lean](../references/conaled/Applications/LocalUniverses/WeakUnit.lean)
constructs dependent elimination for arbitrary groupoids from a functor `p` and
actual `NormalizedLifts p`. The data selects lifts and normalizes identity lifts;
it assumes neither lift-composition coherence nor the desired eliminator. Given
a motive, branch and its strict projection equation, `direct` constructs the
whole functor. Its projection, beta, arbitrary substitution and composite
substitution theorems include the arrow components.

The independent parameter construction builds the parameter groupoid, evaluation,
naming representation with both inverses, generic eliminator, and instantiated
eliminator. `instantiated_agreement` compares that actual route with `direct`.
The [examples](../references/conaled/Examples/WeakGroupoidUnit.lean) retain distinct
fillers with identical objects, a branch-fixing swapping automorphism, and actual
normalized lifts that fail composition. They also consume substitution along a
non-faithful functor.

The [#448 completion report](https://github.com/VladimirMarko/conaled/issues/448#issuecomment-6805484906)
records accepted publication and independent validation. The earlier description
of #448 as open and only paper mathematics is superseded. This is a constructed
weak-unit example with supplied lift data; it does not choose lifts from mere
isofibration existence or prove the general local-universes theorem, full LF,
ambient comprehension, or the selected finite-branch source interpretation. The
[finite-set comparison note](../references/conaled/docs/research/local-universes-concrete-comparison.md)
still explicitly distinguishes its general paper construction from its existing
Lean specializations. Those separate obligations remain separate.

## Selected bridge contract and foundation audit

The user approved the following route after reviewing the properness and joint
foundation obstructions. This is the current construction plan, not a claim that
these semantic obligations have already been discharged. It retains the full
formalization goal and the original conditional results rather than silently
replacing their hypotheses.

### Properness-free finite-branch comparison

The intended chain is external proper etale presentation -> constructed local
finite branches -> the internal finiteness conclusion. There is no intervening
claim that external `IsProperMap` implies unrestricted internal `DPProper`.
The existing argument and exact Cubical/ordinary scope distinction are in
[Finite presentations](finite-presentations.md). In particular,
[FiniteBranchPresentations](../src/Orbifolds/FiniteBranchPresentations.agda)
constructs an embedding of each hom-type into a finite label type from the actual
branch equivalence and setness of the target object type. The proposition beneath
a supplied label need not be decidable or inhabited. Its identity-groupoid example
therefore does not decide equality of arbitrary objects. The ordinary
`Orbifolds.Intensional.FiniteBranchAtlas` theorem retains its separately specified
subfiniteness and geometric locality conclusion; it must not be silently identified
with the Cubical `ProperlyFinite` theorem.

First instantiate a finite smooth action. Construct and compare the actual
labelled arrows, torsors, descended quotient objects and their transport. The
comparison must prove the inverse-label convention, multiplication order, both
inverse laws and compatibility with base restriction and cover refinement. Use
conaled's canonical matching restriction, its dependent-total projection comparison
and its interpreted-source square where their hypotheses apply. A bijection on
objects or a direct proof of the target transport equality is insufficient.

The end-to-end controls are the trivial group on the line, noncommuting labels,
ineffective actions with distinct arrows, and a torsor with no global chart choice.
The trivial-group comparison must not demand unrestricted `DPProper` of the smooth
line's diagonal. Distinguishing supplied arrows must not be confused with deciding
whether an arrow between arbitrary objects exists. A nontrivial torsor must not
be replaced by a global trivialization to make the comparison work.

For general proper etale presentations, the paper construction of local finite
bisections must be formalized with its stated separation/manifold hypotheses and
interpreted over the actual admitted parameters. Ordinary global-point calculations
alone do not construct that interpretation. The remaining orbifold conclusion
also requires constructed manifold microlinearity, the actual atlas's infinitesimal
lifting property, and quotient/descent comparison. A supplied record merely
asserting any of those desired conclusions does not complete the model.

### Exact source admission before expanding the model

The manual source audit already exists in [Source interpretation, Section 5](source-interpretation.md).
Its exact project closure is `Intensional.Identity`, `BoundedTruncation`, and
`FiniteBranchAtlas`, together with the ordinary Agda primitives/naturals. It uses
ordinary dependent sums/functions, inductive identity and J, natural/finite
indexing, explicit lifts, and the stated `FunExt ell ell`. Carriers live at ell;
chart/witness codes at `Code ell`; bounded truncation and the finiteness conclusion
at `Truth ell`. The source's `rec-low` lifts its target explicitly and does not
resize. General cohesion, crisp judgments, univalence and `DPProper` are not
requirements of this selected theorem.

Do not repeat that manual footprint audit as if it were still absent. The missing
admission work is a mechanized interpretation of these actual declarations and
of `Geometry.Tests.finite-branch-atlas-orbifold`, with constructor/substitution
preservation and independently constructed model inputs. Conaled #433 does not
by itself admit all the listed operations. A mathematically justified external
interpretation and a mechanized translation of the native Agda source remain
separate deliverables; do not credit the former as the latter.

The sheaf identity-elimination and substitution queue and the topological
refinement/base-change queue serve this actual end-to-end theorem. Their completion
would still not automatically establish higher identities, smooth stack descent
or every modal/crisp rule. Extend the smooth/formal instance and the admitted test
family explicitly; finite Weil tests must not be relabelled all infinitesimal tests.

### Constructed set-valued source-constructor prerequisites

The current Agda work constructs the categorical equivalence between actual
presheaf families over a context and displays in its slice, including both
functors, full faithfulness, natural unit/counit, both triangle identities,
and the explicit map/substitution squares. The concrete SheafFamilyDisplayRecovery
and SheafFamilyDisplayComparison now have their own fresh complete native gates,
retaining the actual sheaf maps and certificates. The certified-term identity and
composite substitution laws are also accepted. The remaining whole-term display
substitution and nested-identity adapters retain their separate pending gates.

For the truncation operation, `SheafPropositionalTruncation` now constructs
local mere inhabitation from the actual site's covering sieves. It proves
sheafhood and a Hom equivalence into every proposition-valued sheaf.
`DependentSheafTruncation` constructs this family in each existing sheaf
context using the element-site/total-sheaf comparison. The actual isomorphism
under parameter substitution, its unit equations, arbitrary-family-map
naturality and identity/composition coherence are constructed in
`PresheafTruncationBaseChange` and `PresheafTruncationCoherence`.

This uses the Cubical metatheory's mere inhabitation to construct the support
sieve, not a global representative selector. A native finite-site control
rejects the erroneous pointwise-truncation sheaf shortcut for a presheaf input.
The new ordinary `MonicImageElimination` derives a section/branch equivalence
from a categorical image factorization, and constructs restriction of sections
through actual pullbacks. This supplies the algebraic dependent-elimination and
substitution argument, not the concrete sheaf image instance. The local
`section-from-over` lemma avoids silently replacing pointwise-proposition-fiber
hypotheses by a universal assertion about all categorical monomorphisms.
`SheafTruncationImage` now supplies the concrete relative-image universal
property into displays with explicitly proposition-valued component fibers.
`MonicPresheafDisplays` supplies categorical cancellation and section computation
from that particular fiber hypothesis. The concrete
`DependentSheafTruncationElimination` and its actual relative-image
certified-term/substitution owners have now passed their native gates, including
certified computation, uniqueness, both section/branch inverse laws, motive
restriction and actual source-family substitution. The separate identity and
composite source-substitution comparison adapters remain to be constructed.
These are real set-valued model operations useful for source admission, not
an interpretation of all native `Code ell`/`Truth ell` levels or a replacement
for higher quotient semantics. Exact native bounded-truncation source admission
retains its separate proof obligation. The argument
and current constructor boundaries are in [Presheaves](presheaves.md); the
source-bound ledger alone supplies native acceptance.

### Separate audit of the joint foundation package

The existing [joint-obstruction analysis](joint-obstruction.md) and
[WeilFullPostulateIncompatibility](../src/Orbifolds/WeilFullPostulateIncompatibility.agda)
are binding alongside, not interchangeable with, the properness obstruction.
In its displayed crisp ring/Kock-field/crisp-identity context the latter takes
`StrictOrder`, `CrispPullbackPreservation`, `RealFlat`, `KockLawvere` and
`WeilTinyness` and derives the empty type. Review the exact record signatures and
universe/computation rules before attempting to realize them jointly. This is a
conditional contradiction of that exact package, not a theorem that every Myers
foundation or smooth higher model is inconsistent.

Do not promise a nondegenerate model of that same package unchanged. Determine
which formalized conditions match the intended mathematics and which require an
explicit correction or weaker, differently sized statement. A right adjoint in a
larger universe is not automatically the source's same-level tininess witness.
Preserve the original conditional theorems and name a revised theory separately.
Every proposed modal/crisp/tininess extension needs actual model evidence; this
review has not yet selected or proved a replacement foundation.

## Adopted upstream documentation clarification

The retained [documentation-only patch](../references/conaled-descent-status.patch)
was sent and adopted upstream according to the user. The newly selected upstream
bytes now contain its clarification, so it is not an outstanding request. It marks
`smooth-descent-prerequisites.md` as a partial-stage account and replaces the
integrated report's stale pre-acceptance wording with the exact #433 acceptance
reference. The patch retains the historical preimage Git blob IDs; those are no
longer the selected files' identities. It changes no Lean declaration,
mathematical premise or scope boundary. This local refresh copied the already
adopted upstream files and made no upstream write or message.

## Actual action presentations and recovered verification

Retained complete Agda checks support `LabelledActionPullbackTopology`,
`ActionGroupoidTopologicalStructure`, `ContinuousActionArrowFamilies`,
`FiniteActionEtalePresentation` and `FiniteActionTopologicalPresentation`, with
exact current source closures. The source constructs the literal action-groupoid
structure and arrow topology, local charts, and comparisons of continuous
categorical arrow families with locally constant labels. The existing
represented-path and literal trivial-torsor comparisons retain their precise
pending status in the ledger; they are not re-certified by this report.

The bridge checking mode admits the exact cohesion-free shared source
`Orbifolds.GroupoidCompletion` with unchanged safe/completeness/without-K flags.
This narrowly reviewed compiler-mode boundary is not an interpretation of the
crisp/cohesive source language. Likewise, a represented ambient path family is
admitted with a local-constancy condition on recovered labels; arbitrary ambient
paths do not become smooth stack arrows by renaming them.

## Constructed fixed-cover descent interfaces

The following are actual new Agda constructions, with full-target-closure native
evidence in the source ledger. Their arguments and precise limitations are in
[Descent](descent.md); all modules named below except `FinalTopology` are under
`Orbifolds.SemanticBridge`.

| Interface | Constructed content and boundary |
| --- | --- |
| `CechTorsorQuotient` | Independent transitions `c_aa = 1`, `c_bc*c_ab = c_ac`; the actual set quotient `(a,g) ~ (b,c_ab*g)`; local chart/recovery with both inverse laws; right torsor action; compatible-map gluing and uniqueness; equivariant anchored descent. Mere coverage stays truncated. |
| `CechTorsorRefinement` | Actual pullback-cocycle map `[a,g] ↦ [r(a),g]`, equivariance, recovery compatibility, identity/composition equations; mere refined coverage proves equivalence of that exact map without choosing charts. This is fiberwise, not yet topological change of cover. |
| `CechTorsorOrdinaryBridge` | Uses the project's actual ordinary group/action operations and inductive identity proofs, builds the Cubical quotient data, and returns ordinary chart/orbit equivalences and anchor laws through explicit equality conversion. |
| `CechTorsorGauge` | Actual maps between independent cocycles with `d_ab*b_a = b_b*c_ab`, inverse gauges, both inverse laws, equivariance, composition, refinement naturality and preservation of matching anchors. |
| `Intensional.FinalTopology` | Constructs the final `OpenFragment` of actual chart maps, chart continuity, the continuous-out criterion in both directions, and the open-subspace restricted criterion. Desired continuity conclusions are not inputs. |
| `CechTorsorTotalSpace` | Actual `Σ z, Fiber(z)`, equivalence with the projection's inductive-identity fibers, orbit equivalences, final topology of the specified chart maps, continuous projection/action/anchor, and unique continuous descent of compatible local maps. |
| `CechTorsorLocalCharts` | From locally constant original overlap transitions, proves continuity of the inverse charts and constructs actual homeomorphisms `G × U_i ≅ projection⁻¹(U_i)` with the projection triangle. |
| `CechTorsorTopologicalGauge` | Locally constant gauge coefficients give actual same-cover total-space homeomorphisms over the base, compatible with right action, inverses and composition. Inverse regularity is derived. |
| `CechTorsorControls` | Noncommuting permutation labels remain distinct through the quotient even for an ineffective action; negative controls expose missing diagonal and refinement-coverage hypotheses; a covered refinement supplies a positive control. |
| `CechTorsorRecovery` | From an actual right torsor and local sections, derives transition cocycles and proves equivalence of the reconstructed quotient with the original torsor. Mere chart inhabitation remains truncated; anchors are recovered with their equations. |
| `CechTorsorGaugeRecovery` and `CechTorsorAnchoredGaugeRecovery` | Recover gauge coefficients from actual equivariant maps, prove the coefficient law and both function-level inverse laws, and restrict to anchor-preserving maps with the derived local anchor equation. |
| `Intensional.ContinuousLabelRecovery` and `CechTorsorContinuousGaugeRecovery` | Derive local constancy of recovered labels from continuity. The gauge converse assumes locally constant target transitions; the bundled equivalence additionally retains `OpenIsProp` for certificate equality. |
| `CechTorsorRecoveryControls` | Distinct noncommuting gauge labels remain distinct arrows despite ineffective anchors; a constant map without equivariance is rejected. |

These results do not require effectiveness or commutativity of the group. The
fiber algebra permits independent universe levels; the ordinary topological
interface uses its stated shared small universe without resizing. No global chart
selection, untruncation of mere coverage, or hidden choice principle was added.
The constructed topology is the project's precise `OpenFragment`; this report
does not identify it with the entire Mathlib topology interface.

The next useful comparison with conaled's now-accepted generated/original-cover
descent is on these actual maps and their local equations, keeping base substitution,
refinement and source scope explicit. Correspondence of prose or similar interfaces is
not yet cross-checker theorem transport.

## Constructed change-of-cover and parameter comparisons

The Agda descent branch constructs a homeomorphism for the actual refinement
map between chart-final torsor totals. Its hypotheses are mere fine-cover
membership, locally constant coarse transitions, and the explicit `MerelyLocal`
neighborhood law. The latter is constructed for the existing Dedekind real and
finite Cartesian rational-ball topologies, not merely asserted for every
`OpenFragment`. Identity/composition of refinements and the forward/inverse
parameter-change squares retain the same quotient maps.

Parameter change has an actual continuous cone lift: its underlying map uses
dependent transport in the quotient fiber; continuity follows from local chart
recovery and mere-neighborhood gluing. Its two projection triangles and uniqueness
are proved. Uniqueness from separate projection equations retains setness of the
old base; the identity-fiber carrier equivalence needs no setness. This is a
universal property for merely-local test domains. The lift is equivariant for
an invariant/equivariant input cone. Gauge arrows, inverse maps and composition
order commute with parameter change.

The interfaces are `CechTorsorTopologicalRefinement`,
`CechTorsorTopologicalRefinementLaws`, `CechTorsorBaseChange`,
`CechTorsorRefinementBaseChange`, `CechTorsorBaseChangePullback`,
`CechTorsorEquivariantPullback` and `CechTorsorGaugeBaseChange`, under
`Orbifolds.SemanticBridge`. [Descent](descent.md) supplies the arguments and exact
scope; `state.json` alone binds current sources to applicable native evidence.
These actual topological maps can be compared with conaled's generated
restriction and total-projection interfaces. They do not themselves interpret
the generated source substitutions, construct a smooth/higher quotient, or
transport unrestricted `DPProper`.

## Remaining joint obligations

The accepted bounded source interpretation and its generated/original-cover
descent are useful upstream interfaces, not a model of the whole native Agda
foundation. The current upstream scope is recorded in
[smooth-source-interpretation.md](../references/conaled/docs/research/smooth-source-interpretation.md).
The complete task still requires actual source interpretation and substitution,
universe closure, required higher/modal/crisp operations, smooth/formal/manifold
instances, stack-level quotient and arrow descent, and obstruction-compatible
properness transport.

The topological results now include actual covered-refinement homeomorphisms and
parameter-change/refinement squares as described above. The concrete continuous
bundle functor/comparison coherence, smooth local maps and higher quotient
comparison remain explicit obligations. Local topological trivializations are
not a full smooth stack model.

The recovered arbitrary-motive sheaf identity-elimination suite remains pending.
Its endpoint construction has been factored through generic presheaf modules.
The minimal-dependency repeated-context module has applicable completed evidence;
the endpoint compatibility, sheaf specialization and nested J targets still
need complete native checks. The represented-path/trivial-torsor comparison also
remains pending; its retained killed check does not identify the cause.
Detailed current diagnostics and next actions belong
only to the effort note and exact evidence ledger. No interrupted check contributes
proof acceptance, and no new combined aggregate release is claimed.

No external message or issue comment was sent by creating this handoff.
