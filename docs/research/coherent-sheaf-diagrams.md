# Categories of systems over fixed contexts

Assessment under [#708](https://github.com/VladimirMarko/conaled/issues/708),
implemented under [#726](https://github.com/VladimirMarko/conaled/issues/726).
Source baseline: `ba7ee812cbcc3024c235e72832d1f4aa840a5139`; Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean `v4.35.0`.

## Decision and mathematical benefit

Package the local-code/slice-sheaf total equivalence as an equivalence between
categories of systems over an arbitrary fixed context diagram `K : I ⥤ D`.
Also restrict it to cartesian systems, retaining arbitrary vertical natural
transformations between them. Use Mathlib's based functors and based natural
transformations for the underlying categories.

The benefit is categorical transport of whole-system universal properties.
For example, a vertical map satisfying two compatible constraints is a universal
solution among local-code systems exactly when its decoded fork is a universal
solution among sheaf systems over the same `K`. The equivalence lets this use
Mathlib's preservation and reflection of equalizers. It supplies the comparison
needed for that argument; it does not by itself prove that equalizers exist.
A statement transferring existence must assume existence on one side.

The prior [diagram examples](../../Examples/CoherentSheafFibration.lean) already
recover individual systems, arrows and compatible transformations. The added
capability packages their fixed-context restriction into a category equivalence
that other categorical constructions can consume. This is a mathematical reuse
claim, not a measured author-productivity result.

## Objects, maps and cartesian systems

For a projection `p : C ⥤ D`, an object over `K` consists of a functor
`A : I ⥤ C` with `A ⋙ p = K`. Its maps are natural transformations whose
components project to the identity of the corresponding object of `K`.
They may be noninvertible. Mathlib's `BasedFunctor` and `BasedNatTrans` supply
these objects, maps, composition and whiskering with independently sized
categories.

Selecting objects with `A ⋙ p = K` as a full subcategory of the ordinary
functor category would be wrong: it would retain transformations that move the
base. With the identity projection on types and a constant Boolean context,
the constant-false endomorphism is an ambient natural transformation but is
not vertical. Both the fibre-of-postcomposition and based-functor presentations
correctly exclude it.

Cartesian systems form a full subcategory of the fixed-context category.
Every transition of such a system must be cartesian. Its maps remain arbitrary
vertical transformations; requiring their components to be invertible would
lose valid maps. Constant systems illustrate the distinction: their identity
transitions are cartesian, while a vertical collapse can be noninvertible.

## Selected construction and alternatives

The generic construction starts with an ordinary equivalence over a common
base, its two projection equations and its original vertical unit and counit.
Postcomposition gives the two functors on systems over `K`; whiskered recovery
gives their original unit and counit. This is restriction of an established
equivalence, not a new assumption of the desired restricted equivalence.
Two-way preservation of cartesian arrows then restricts those functors and their
recovery to the cartesian full subcategories.

The sheaf specialization discharges these premises using #725's total
functors, projection equations, recovery and cartesian-preservation theorems.
It retains the original full-faithfulness, cover density, specified
structured-arrow limits and independent site/value universes. Callers supply
their system, its projection equation and vertical maps, plus cartesian
transition proofs when selecting the restricted category.

| Presentation | Assessment |
| --- | --- |
| Mathlib based functors | Selected. Existing composition, componentwise verticality and based natural isomorphisms support the direct postcomposition construction. Use the independently sized definitions without forcing the fixed-universe bicategory instance. |
| Categorical fibre of postcomposition | Equally faithful mathematical contract. A good alternative for a general theorem about fibres; this task needs no second presentation or conversion layer. |
| Ordinary functor-category equivalence | Already supplied by `Equivalence.congrRight`; it does not enforce the fixed-context morphism condition. |
| New sheaf-specific section records | Would repeat existing category laws and restriction machinery without a sheaf-specific requirement. |
| General pseudonatural sections framework | Outside this bounded contract. No retained requirement calls for additional coherence infrastructure. |

The cartesian restriction can directly restrict both functors and the original
recovery. Alternatively, Mathlib's `congrFullSubcategory` applies after deriving
predicate reflection and closure under isomorphism. Neither formulation should
ask sheaf callers to prove those consequences anew.

## Assessment evidence and limits

The [brief](coherent-sheaf-diagrams-design/brief.md) and initial
[contract](coherent-sheaf-diagrams-design/contract.md),
[use](coherent-sheaf-diagrams-design/use.md) and
[alternatives](coherent-sheaf-diagrams-design/alternatives.md) reports record
three assessments. Contract and Use used fresh contexts. The host refused a
third fresh agent, so Alternatives reused the prior #725 review coordinator;
that exposure is disclosed. Reports were saved before they were shared.

The contract probe checked both presentations, vertical-map semantics, a
Boolean rejection control and heterogeneous composition. The use probe checked
standard equalizer preservation/reflection and conditional existence transfer,
assuming the proposed fixed-context equivalence as its missing producer.
The alternatives probe checked heterogeneous based-functor postcomposition and
a noninvertible vertical Boolean endomorphism. These Mathlib-only checks were
selection evidence. They did not implement the complete equivalence or
cartesian restriction. Initial sheaf imports failed because the current
checkout lacked their compiled artifacts; this was not a mathematical failure.
The [probe sources](coherent-sheaf-diagrams-design/probes.md) preserve the checked
selection examples; the initial reports retain temporary paths as execution
provenance.

All three assessments support the bounded capability. Their representation
preferences differ: Use favors categorical fibres; Alternatives favors based
functors; Contract accepts both. Inspection of the existing based composition
and whiskering operations supports the latter for this task. No new category
implementation or heterogeneous bicategory is needed.

#708 retains its broader usage survey, adapter ranking and source coverage.
[#723](https://github.com/VladimirMarko/conaled/issues/723) owns shared coherence
across the indexed-family and stackification consumers. This result adds no
stackification, effective descent, strict type-former stability or compulsory
migration of direct clients.

## Public interface and checked applications

[BasedDiagram](../../SquareKit/BasedDiagram.lean) reuses the based-functor
category through `Over p K`. Its `equivalence` acts by postcomposition and
retains both directions of the original unit and counit componentwise.
`CartesianOver p K` is the full subcategory on cartesian transitions;
`cartesianEquivalence` restricts both functors using two-way preservation and
lifts the original recovery through the fully faithful inclusions. This direct
restriction needs no extra iso-closure field or chosen cleavage.

[CoherentSheafDiagrams](../../SquareKit/Internal/CoherentSheafDiagrams.lean)
provides `diagramEquivalence G J K` and `cartesianDiagramEquivalence G J K`.
Their object and map formulas use the existing `totalDecode` and `totalCode`,
and their recovery components use `totalRecovery` and `totalCounit`.
The [applications](../../Examples/CoherentSheafDiagrams.lean) connect these
interfaces to equalizer universal properties and the existing Boolean model.
The original totalization and individual diagram APIs remain available.

The retained application module checks preservation and reflection of a
supplied equalizer fork through each public equivalence, without assuming
limits exist. Its cartesian constant system has a vertical collapse that
remains noninvertible after decoding, with recovery naturality on that map.
A parallel-pair system uses the Boolean composite `p ≫ d` for its transitions:
these are cartesian and their base map is not identity. A separate identity-base
projection control rejects a nonvertical ambient transformation. Unequal and
reversed universe signatures check both diagram interfaces under their stated
hypotheses; they do not construct sites at every universe size.

Focused builds of the generic construction, sheaf specialization and application
module passed at this pin. Acceptance additionally requires integrated
exact-candidate build, exhaustive axiom audit and independent Standards/Spec
review. The issue records that delivery evidence.
