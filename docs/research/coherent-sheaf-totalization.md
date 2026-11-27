# Coherent local sheaves over changing contexts

Assessment for [#708](https://github.com/VladimirMarko/conaled/issues/708),
27 November 2026. Source baseline `f96e378241012feae903d6e06211c26bfe0f94b3`,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean `v4.35.0`.

## Recommendation

Develop a bounded total equivalence between coherent local sheaf presentations
and sheaves over changing contexts. Retain the independently defined local
codes, all their maps, the existing substitution operation and the fibrewise
entry points. The benefit is uniform recovery of constructions that combine
context changes with maps of sheaves. An existing blocked application is not
required: this is useful mathematical structure for the
[language direction](../language-direction.md#complementary-presentations-and-reconstruction).

Select the native-arrow contract below. The #725 implementation checkpoint
compared explicit universe lifts with a heterogeneous total functor and selected
the latter; see the checked comparison below.
The recommendation does not depend on a universal coherence framework, a
rewrite of existing clients, or completion of #723.

The assessment supplies the mathematical contract and acceptance criteria for
[#725](https://github.com/VladimirMarko/conaled/issues/725). Its implementation
is recorded below. Neither the construction nor its examples establish a
measured productivity improvement or complete #708's broader survey.
Here “coherent” means compatible local diagrams, not coherent modules in
algebraic geometry; “totalization” means a category over contexts, not a
total complex or a homotopy limit.

## Native total interface

Write `CΓ = LocalCode G J Γ`, `SΓ = Sheaf (J.over Γ) (Type w)` and
`EΓ : CΓ ≌ SΓ` for the existing
[sheaf classification](../../SquareKit/Internal/CoherentSheafOver.lean).
For `σ : Δ ⟶ Γ`, the current reindexing is

```text
Lσ = EΓ.functor ⋙ sheafPullback σ ⋙ EΔ.inverse.
```

A native total arrow `(Δ,A) ⟶ (Γ,B)` consists of this actual base map `σ`
and an arbitrary map `f : A ⟶ Lσ B`. Decoding gives

```text
(σ, EΔ.functor.map f ≫ (decodeReindex σ).hom.app B).
```

`decodeHomEquiv` gives a bijection between native and decoded maps over each
fixed `σ`. Identity/composition compatibility gives `totalDecode`. The coherent
inverse and vertical recovery give `totalEquivalence` over the same base, with
both projection equations, original fibre recovery and preservation of cartesian
arrows in both directions.
This includes noninvertible fibre maps. It does not equate arbitrary chosen
pullbacks or cartesian lifts by equality.

The sheaf total already exists through Mathlib's
[pseudofunctorOver](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/PseudofunctorSheafOver.lean)
and CoGrothendieck construction. The added theorem connects the independent
local presentation to that capability. The existing
[coherent-family total bridge](../../SquareKit/Internal/CoherentFamilyFibration.lean)
uses different fibres and strict precomposition; its total-map machinery is
reusable, but its fibres cannot replace the local-sheaf category.

## Coherence and total recovery

[CoherentSheafFibration](../../SquareKit/Internal/CoherentSheafFibration.lean)
packages `codePseudofunctor` using the existing `reindex`, `reindexId` and
`reindexComp`. Associativity and both unit equations follow by applying the
faithful sheaf decoder, rewriting with `decodeReindex_id/comp`, and using sheaf
pullback coherence, including equality transports on base arrows. Callers
supply no new coherence fields.

[CoGrothendieckTransport](../../SquareKit/CoGrothendieckTransport.lean) supplies
heterogeneous comparison and total recovery machinery. Its `fullyFaithful`
recovers maps over each fixed base arrow. The inverse keeps the specified
native fibre objects and recovers arrows by taking the preimage of counit
conjugation. The original units and counits are natural for these total functors.
The equivalence proves its triangle identity directly, so its packaged unit is
the original unit; no `Equivalence.mk` adjustment is needed. Both directions of
both recovery isomorphisms are vertical.

`totalDecode` and `totalCode` commute with projection to contexts. Their
restrictions to each fibre recover the original classification on objects and
maps. `totalDecode_cartesian` and `totalCode_cartesian` preserve arbitrary
cartesian arrows. Forward preservation factors a cartesian arrow through a
canonical lift and a vertical isomorphism. Reflection uses the fixed-base
preimage and the universal property; inverse preservation then follows by
conjugating with the vertical counit. These proofs do not identify arbitrary
chosen cartesian lifts by equality.

## An application that tests the benefit

Let `K : I ⥤ D` be a diagram of contexts. A system of local presentations has
a code over each `K.obj i`, and maps into reindexed codes along each arrow of
`I`, satisfying identity and composition laws. Maps need not be invertible.
A commuting square of such data is one example.

The checked [diagram application](../../Examples/CoherentSheafFibration.lean)
expresses this system as a functor `A : I ⥤ CodeTotal`
with projection `K`. Its decoded system is `A ⋙ totalDecode`. Whiskering total
recovery gives a natural round-trip isomorphism over the same `K`, recovering
the whole system and its compatible maps. Cartesian transition arrows are
retained when present; they are not imposed on every transition.

This makes a mathematical setting and its context changes available through
ordinary functor composition. Currently each such client can insert the
fibrewise decoder comparisons by hand; a coherent total bridge discharges
that work once. The generic diagram application checks projected recovery, arrow naturality,
compatible natural transformations and preservation of cartesian transitions.
It uses ordinary functors and whiskered recovery without introducing a new
framework of sections. A category of diagrams
over fixed `K` would require the corresponding restriction proof in addition
to the unrestricted functor-category equivalence.

For a separating concrete case, reuse
[pairProjection, diagonal and collapse](../../Examples/CoherentSheafOver.lean).
With `p : Bool × Bool → Bool` and `d : Bool → Bool × Bool`,
`d ≫ p = id`, while `p ≫ d` sends `(true,false)` to `(true,true)`.
Take the code `A` of `pairDisplay` and its noninvertible collapse `k`.
The successive lifts

```text
(Bool, d*(p*A)) → (Bool × Bool, p*A) → (Bool, A)
```

have identity composite base. Precomposing with the vertical map `d*(p*k)`
must still recover `k` under the substitution comparison. Identity base is
not identity arrow, nor does it imply invertibility. Test the opposite base
order too, and round-trip naturality on the composed total arrow. Do not
assume arbitrary reindexing reflects isomorphisms: this example uses the
specific round trip `d* ∘ p* ≅ Id`. The `Boolean` application checks these total arrows, their decoded composite,
its noninvertibility, and recovery naturality on that composite. It derives
noninvertibility after two reindexings from the specific round-trip comparison.
The existing source still proves `collapse_not_iso`, `code_collapse_not_iso`
and the density control `support_map_not_iso`.

## Assumptions and the universe checkpoint

Retain the existing `Substitution` assumptions: full and faithful `G : B ⥤ D`,
cover density of the represented slice site for every context, and the
specified structured-arrow limits in `Type w` for every context. Retain the
independent universes `B : Type u`, `Category.{v} B`, `D : Type a`,
`Category.{b} D` and values `Type w`. No additional base pullbacks,
subcanonicity or sheafification assumption is needed for general substitution.
The separate `codeDisplayClassification` uses subcanonicity and `Type b`;
that specialization must not narrow the generic total bridge.

The contract lens ran an isolated elaboration probe against existing artifacts:

| Fibre | Object universe | Hom universe |
| --- | --- | --- |
| Local codes | `max u v b (w+1)` | `max u v b w` |
| Sheaves over the context | `max a b (w+1)` | `max a b w` |

The ordinary fibre equivalence handles these different sizes. Directly applying
`.toCatHom` to its functor fails because Mathlib's strong-transformation route
requires a common `Cat` universe. The initial naive lifted-equivalence chain also failed
typeclass synthesis; the implementation checkpoint below repairs it. The
[reproducer and diagnostics](coherent-sheaf-totalization-design/contract.md#reproducible-checked-probe-and-validation-limits)
preserve the evidence. These failures identify an encoding obligation, not a
mathematical impossibility.

### Checked packaging comparison for #725

Both routes passed isolated Lean checks at the recorded Mathlib pin, with
independent site/value universes and unchanged `Type w`. The lift repair enables
Mathlib's `uliftCategory` instance locally and supplies the hom-lift level
explicitly. Its common category has hom universe `max u v a b w` and object
universe `max u v a b (w+1)`. Conjugating the original fibre equivalence by
`ULiftHomULiftCategory.equiv` then admits `.functor.toCatHom`.

The lifted probe checked composition for arbitrary fibre maps over composable
context maps, using the actual `reindexComp` and `decodeReindex_comp`. A native
wrapper recovers exactly the decoder formula above. Polymorphic signatures and
the specializations `.{0,1,2,3,4}` and `.{4,3,2,1,0}` elaborate. These are
signature checks, not constructed examples of sites at each size. The probe did
not package lifted pseudofunctors or a total equivalence.

The native probe checked an ordinary functor between Mathlib `CoGrothendieck`
categories with independently sized fibres, its composition on arbitrary total
arrows, and its projection equation. Components are ordinary functors and
natural isomorphisms with identity/composition compatibility. The sheaf
specialization derives that compatibility from `decodeReindex_id/comp`; it
does not request additional coherence from callers.

Select the native route. Both routes retain the same mathematical obligations
for code coherence and recovery. Lifting adds two lifted indexed systems and
native recovery through their conversions. The native route instead adds a
bounded heterogeneous map/recovery helper while retaining Mathlib's total
categories, projections and cartesian API. It exposes the existing native arrow
types directly. This comparison supports the choice for this adapter; it does
not establish a general productivity advantage or an impossibility for lifts.
The earlier failed lift probe records an elaboration problem that this
checkpoint resolved.

## Alternatives and ownership

| Route | Assessment |
| --- | --- |
| Direct sheaf total | Already useful without density assumptions. Keep it for callers supplying sheaves; it does not provide native local-code total recovery. |
| Transported pseudofunctor and existing totals | Preferred mathematical route. Derive coherence from fibre equivalences; resolve the common-universe packaging explicitly. |
| Native totals with heterogeneous comparison | Selected after the checked comparison above; uses a heterogeneous total-map helper and retains the original universes. |
| Induced total whose homs are decoded sheaf arrows | Credible fallback. Recover native `A ⟶ Lσ B` homs and their composition explicitly; defining homs through the decoder alone does not prove native recovery. |
| Displayed/fibred presentation | Legitimate alternative foundation. With these native substitutions it still owes coherent composition. The current represented-display specialization has extra hypotheses. |
| Split replacement or local universes | Relevant when strictly stable logical structure is required. This total equivalence needs coherent substitution, not a new strict type-theoretic model. |

The [alternatives report](coherent-sheaf-totalization-design/alternatives.md)
compares primary treatments of displayed categories and local universes, with
their hypotheses and access limits. nLab page retrieval failed; search-index
orientation is not a completed page survey. No claim of exhaustive literature
coverage or completion of #708's nLab coverage requirement follows.

[#723](https://github.com/VladimirMarko/conaled/issues/723) owns shared coherence
extraction. The #725 implementation extracts
`CategoryTheory.inverseSquareAcross`, its specification, composition and
canonical equations into [EquivalenceSquare](../../SquareKit/EquivalenceSquare.lean).
These unchanged lemmas operate on ordinary equivalences and compatible squares
with independent universes; stackification remains their original consumer.
The second consumer specializes the forward square to `decodeReindex.symm`
for inverse comparison and recovery compatibility. Identity normalization
follows from the forward identity law and counit naturality; composition uses
the extracted square-composition theorem. The
[use report](coherent-sheaf-totalization-design/use.md#boundary-with-723)
records that mapping. The extraction preserves public names and introduces no
stack assumptions
into the sheaf contract. It supplies a concrete two-consumer result for #723;
that issue retains the broader shared-coherence assessment.

## Implementation acceptance and assessment limits

The implementation is bounded by these requirements:

1. Resolve native universe preservation with the signature/composition checkpoint.
2. Derive code coherence and both directions of the indexed comparison from
   existing data; preserve the selected reindexing comparisons.
3. Establish all-map total equivalence, both base projections, native fibres,
   vertical original and packaged recovery, and arbitrary cartesian preservation.
4. Check generic diagram recovery and the composed Boolean/collapse case through
   the public adapter; retain the density and noninvertibility controls.
5. Preserve current direct clients under their original hypotheses, validate
   unequal universe parameters, and run the integrated build/audit and independent
   reviews. Record any reusable extraction under #723 with its actual consumers.

The [brief](coherent-sheaf-totalization-design/brief.md),
[contract report](coherent-sheaf-totalization-design/contract.md),
[use report](coherent-sheaf-totalization-design/use.md) and
[alternatives report](coherent-sheaf-totalization-design/alternatives.md)
preserve the initial assessments. All recommend the bounded capability. The
contract report qualifies the common-Cat implementation route with executed
negative evidence; that qualification takes precedence over an untested direct
reuse plan. Contract and Use had fresh contexts. Alternatives reused a prior
cleanup reviewer after the host refused a third fresh thread; prior involvement
is disclosed. Reports were not shared before their initial versions were saved.
Afterward, the Use reviewer read the contract report's universe evidence and
confirmed that it changes the packaging recommendation, not the diagram-recovery
contract. Its initial report is preserved unchanged; the first-checkpoint
requirement above incorporates that reconciliation.

The initial reports predate implementation. The new modules and examples retain
independent universes and the original substitution assumptions. The public
facade imports the new application beside the unchanged direct sheaf clients.
Acceptance requires an integrated build, exhaustive transitive axiom audit and
independent Standards/Spec review of the exact candidate; focused compilation
alone does not replace them. Broader facade-aware usage sampling,
remaining-family ranking, deeper categorical coverage and other #708 acceptance
items remain open.
