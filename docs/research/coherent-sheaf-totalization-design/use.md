# Coherent-sheaf totalization: implementation and use

Independent initial assessment for #708, 27 November 2026. Project revision
`f96e378241012feae903d6e06211c26bfe0f94b3`, Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean `v4.35.0`.

## Recommendation

Proceed toward a bounded implementation of the coherent equivalence and its
CoGrothendieck totals, retaining the existing fibre interfaces. Its useful
capability is recovery of systems of local sheaf data over changing contexts,
including arbitrary transition maps and their composition. This merits an
interface even without an existing blocked client. The mathematical benefit is
coherent, all-map recovery of such systems; the author benefit is using ordinary
functors and naturality for arguments that currently require explicit
substitution comparisons.

The smallest justified contract uses the existing `LocalCode`, `reindex` and
`sheafOverClassification`, derives their missing coherence, and applies existing
totalization. It should not require callers to supply the final total equivalence
or additional coherence laws already forced by the definitions. Adoption should
include a general diagram-recovery application and the concrete separating case
below. Neither implementation difficulty nor author productivity was measured in
this assessment.

The strongest evidence for retaining this proposal is the combination of three
inspected facts: the code reindexing is already conjugation by equivalences;
Mathlib supplies the sheaf pseudofunctor and total-category laws; and local
`CoGrothendieckMap` already transports modifications and arbitrary cartesian
arrows. Most of the proposed mathematical structure therefore has existing
components with applicable contracts. The remaining proof work connects these
components coherently. Sources: [substitution](../../../SquareKit/Internal/CoherentSheafOver.lean),
[Mathlib sheaf pseudofunctor](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/PseudofunctorSheafOver.lean#L37),
and [total-map support](../../../SquareKit/CoGrothendieckMap.lean).

## Existing capability and actual obligations

Write `CΓ` for `LocalCode G J Γ`, `SΓ` for `Sheaf (J.over Γ) (Type w)`,
and `EΓ : CΓ ≌ SΓ` for `sheafOverClassification G J Γ`. The current
reindexing along `σ : Δ ⟶ Γ` is exactly

`CΓ --EΓ.functor--> SΓ --σ*--> SΔ --EΔ.inverse--> CΔ`.

`reindexId`, `reindexComp`, `decodeReindex_id` and `decodeReindex_comp`
already exist. The last two prove decoder compatibility with the chosen identity
and composition comparisons. Describing all coherence as absent would overlook
these proofs. Remaining packaging must establish the code pseudofunctor's
associativity/unit equations, the strong decoder and inverse, and compatible
unit/counit modifications. These are candidate derived theorems, not new
primitive caller fields. On paper, applying the faithful decoder reduces the
code coherence to target coherence, the displayed compatibility equations and
equivalence triangle identities. This report does not provide checked Lean
proofs of that reduction. See [the existing definitions and equations](../../../SquareKit/Internal/CoherentSheafOver.lean).

The classification assumptions are substantive. `G` is full and faithful;
`CostructuredArrow.toOver G Γ` is cover dense for each context used; and the
specified `StructuredArrow` limits exist in `Type w`. Totalization over all of
`D` requires these hypotheses uniformly in `Γ`, just as the existing
`Substitution` section does. It must retain independent site, hom and value
universes. Subcanonicity enters `codeDisplayClassification` and the represented
context sheaf; it is absent from general sheaf substitution. The independent
local objects retain their rooted sheaf conditions and all natural
transformations. See [Dense, DenseDisplay and Substitution](../../../SquareKit/Internal/CoherentSheafOver.lean).

The existing #705 route does not remove these obligations. Its
[diagrams and families](../../../SquareKit/Internal/RepresentableCoherentRecovery.lean)
are strict functors based on precomposition along element functors. Its
[total equivalence](../../../SquareKit/Internal/CoherentFamilyFibration.lean)
uses already supplied strong transformations and recovery modifications.
Coherent-sheaf reindexing instead inserts equivalence units/counits. Reusing
#705's total-map construction is justified; substituting its fibres for local
sheaf fibres is not.

## A useful author construction: recovery of diagrams over contexts

The following is a proposed mathematical application, not an implemented client.
Let `I` be a small indexing category and `K : I ⥤ D` a diagram of contexts.
A diagram of local sheaf presentations over `K` consists of:

- a local code `Aᵢ` over each `K.obj i`;
- for each `h : i ⟶ j`, a map `Aᵢ ⟶ (K.map h)* Aⱼ`;
- identity and composition laws with the chosen reindexing comparisons.

The maps can be noninvertible. This describes, for example, a commuting square
of sheaf families whose four sides change context, with local maps between
chosen presentations. Recovering that whole square is a mathematical use of
coherent classification: independently classifying its vertices does not itself
supply the square's arrows and equations.

With a code total category, those data become a functor
`A : I ⥤ CodeTotal` whose projection is `K`. Its decoded system is simply
`A ⋙ totalDecode`. Functoriality proves preservation of every composite and
commuting square. Coding back yields a natural isomorphism from `A` to its
round trip, obtained by whiskering total recovery. Because recovery components
lie over identity maps, this is recovery over the same `K`. Compatible maps
between such diagrams are retained too. Cartesian transition arrows remain
cartesian in both directions.

The unrestricted functor-category equivalence is directly the existing
[`Equivalence.congrRight`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Equivalence.lean#L414)
applied to the proposed total equivalence. Restricting to diagrams over a fixed
`K` also needs the projection equations and vertical unit/counit. That restriction
is a paper consequence here, not an already identified packaged Mathlib theorem.
One can demonstrate the useful application by proving projected recovery and
naturality for an arbitrary `A`, without first introducing a new category of
such diagrams. If a caller asks for cartesian sections, the same construction
restricts to them using cartesian preservation; it does not assert that every
transition is cartesian.

Current callers can already achieve each finite instance by decoding all objects
and maps, inserting `decodeReindex`, and applying its composition equation.
For a round trip they also supply the relevant naturality and compatibility
arguments. Totalization pays those arguments once, then uses ordinary category
and functor interfaces across arbitrary diagram shapes. It adds no new sheaf
existence theorem and no effective-descent theorem. Its benefit is a reusable
coherent form of the existing mathematics, consistent with the project's
[complementary-presentation criterion](../../language-direction.md#complementary-presentations-and-reconstruction).

## Separating example and what it demonstrates

Use the existing `pairProjection : Bool × Bool → Bool`, called `p`, and
`diagonal : Bool → Bool × Bool`, called `d`. In Lean composition notation,
`d ≫ p = id`, whereas `p ≫ d` sends `(true, false)` to `(true, true)`.
Use `pairDisplay` and its endomorphism `collapse`, which resets the second
coordinate to `false`. The source proves `collapse_not_iso` and
`code_collapse_not_iso`; these are stronger controls than testing only
isomorphisms. See [the concrete definitions and controls](../../../Examples/CoherentSheafOver.lean).

Let `A` be the local code obtained from `pairDisplay`, and `k : A ⟶ A`
the corresponding collapse. Consider the successive canonical lifts

`(Bool, d*(p*A)) → (Bool × Bool, p*A) → (Bool, A)`.

Their bases are `d` and `p`. Precompose the first lift with the vertical map
`d*(p*k)`. The resulting composite has identity base, but after the reindexing
comparison its fibre map is the collapse `k`, not an isomorphism. This prevents
an implementation from confusing identity base with identity arrow or retaining
only cartesian arrows. A second sequence, starting over `Bool × Bool` and using
`p` then `d`, must retain the nonidentity base map just computed.

A future checked client should verify the decoded fibre maps, naturality of
round-trip recovery for these composites, and the actual projection equations.
It should use the public total functors and their laws. Merely proving the two
Boolean function calculations independently would not exercise the bridge.
The case distinguishes direction, map loss and non-strict comparison handling.
It does not prove uniform diagram recovery, universe generality or productivity;
the abstract application above and signature review cover different obligations.

The existing `support_map_not_iso` supplies another boundary. Under the bottom
topology, all represented local views of that map are isomorphisms although the
original map is not. Consequently, subcanonicity alone cannot replace cover
density. Totalization must not make this unsupported inference. This is an
inspected existing counterexample, not a new experiment.

## Builder cost, caller cost and maintenance

| Route | Builder responsibility | Caller responsibility and reuse |
| --- | --- | --- |
| Current fibre API | Existing classification, reindexing and decode comparisons | Supply local data and geometric/size hypotheses; insert comparisons for changing-context diagrams. Best for isolated fibre calculations. |
| Direct sheaf total | Instantiate `CoGrothendieck (J.pseudofunctorOver (Type w))` | Supply actual sheaves and transition maps. Gets ordinary diagram composition immediately. Does not recover an independently supplied local-code diagram without the coherent bridge. |
| Proposed code/sheaf total equivalence | Derive transport coherence and inverse modifications once; apply existing totalization | Same local-data and classification hypotheses, plus ordinary total arrows/functors when needed. Composition and diagram recovery reuse common proofs. |
| Direct display/fibration interface | Supply comparison of display pullback, local reindexing and recovery over contexts | Natural for supplied display maps, but the present represented-display route needs subcanonicity and its value-universe specialization. These extra assumptions should not enter general sheaf substitution. |

The main maintenance cost is coherence at the equivalence-transport boundary,
including dependent equalities for bases and the chosen identity constraints.
Mathlib's [`CoGrothendieck.Hom`, composition and `map`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Grothendieck.lean#L248)
already maintain the category and functor proofs. Its
[fibration instance and fibre inclusions](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean)
supply the cartesian lifts and actual fibres. Local
[`CoGrothendieckMap`](../../../SquareKit/CoGrothendieckMap.lean) maintains action on
modifications and preservation of arbitrary cartesian arrows. Reimplementing
those three layers for sheaves would create unnecessary maintenance.

A smaller intermediate deliverable is the coherent indexed equivalence alone.
It is already useful through
[`StackDescentTransformation.map`](../../../SquareKit/StackDescentTransformation.lean),
which transports descent data and compatible maps under a strong
transformation. That reuse does not require proving a stackification theorem.
For the proposed total-arrow application, however, stopping there leaves a small
existing machinery application undone. A generic transport construction may be
worth extracting if its interface is genuinely smaller than local proofs; this
assessment does not require a universal coherence framework.

## Boundary with #723

#708 should own the exact local-code adapter, its hypotheses and recovery
contract, plus the above application and separating test. #723 can assess common
coherence across indexed-family and descent clients without blocking #708.
The inspected sources provide concrete evidence to compare:

- [`StackificationUniversal.inverseSquare`, `inverseSquare_spec` and `inverseSquare_comp`](../../../SquareKit/StackificationUniversal.lean)
  derive inverse comparisons and composition from equivalences and compatible
  forward squares. The earlier version has a common source category `A`.
  The later `inverseSquareAcross`, `inverseSquareAcross_spec`,
  `inverseSquareAcross_comp` and `inverseSquareAcross_canonical` support
  independently varying source and target categories and independent universes.
  They are directly relevant generic mathematics, despite their location in
  the stackification file. Set `E` to the fibre classifications, `R` to sheaf
  pullback, `L` to code reindexing, and the forward square to
  `decodeReindex.symm`. The constructor then supplies the inverse comparison;
  its specification and canonical equation give counit/unit compatibility,
  while its composition theorem needs the forward compatibility equation
  already represented by `decodeReindex_comp`, with orientation adjusted.
  This is a paper specialization, not a checked Lean application.
  `inverseSquare_identity` handles a normalized identity case; aligning the
  nonliteral code identity functor through `reindexId` still needs explicit
  comparison work.
- [`StackDescentTransformation.mapHom_pullHom`, `comparison_comp_hom` and modification transport](../../../SquareKit/StackDescentTransformation.lean)
  express the same strong-transformation coherence in descent arguments.
  These are candidates for shared lemmas or transport interfaces, not evidence
  that the sheaf adapter has already been packaged.

A bounded #708 implementation can use existing lemmas where their hypotheses fit
and record the exact repeated proof for #723 when they do not. Do not impose
stack descent, local generation or target-stack assumptions on the sheaf
classification merely to reuse the surrounding stackification module.
The [#678/#679 results](../action-stackification-morita.md) concern adding effective
objects and atlas-independent stackification; totalization retains the existing
objects in varying fibres and has a different contract.

## Evidence and remaining uncertainty

This report inspected the pinned project and dependency source definitions,
proofs and examples linked above, plus the existing
[family-fibration record](../coherent-family-fibration.md) and
[presentation-search assessment](../reconstructible-presentations-search.md).
The online pinned `PseudofunctorSheafOver.lean` was also accessed on 27 November
2026. Its actual declaration resides in that separate module, while `Sites/Over`
supplies its comparison laws.

The derivation of the missing code coherence, the diagram-recovery application
and the combined Boolean total-arrow case are paper arguments. A local-link check passed after resolving paths against the intended durable
location. Its first invocation could not find Python outside the development
environment; the rerun used `direnv exec .`. No new Lean
code was written or compiled, no build or proof audit ran, and no performance or
author trial was executed. Source inspection establishes availability and
statement shape, not fresh validation of the checkout. Universe compatibility
of the proposed full total equivalence remains an elaboration obligation.

This agent received the shared brief and the implementation/use assignment,
read no other initial assessment, and did not coordinate conclusions or delegate
further work. Before finalizing, the coordinator supplied a source pointer to
`inverseSquareAcross` and `inverseSquare_identity`; the signatures and proofs
were then inspected independently. No other lens findings were supplied. The recommendation is conditional on checking the stated
coherent contract and applications, not on demonstrating an already blocked
consumer or on a claimed universal reduction in author effort.
