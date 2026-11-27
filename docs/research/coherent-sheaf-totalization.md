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

Select the native-arrow contract below. Before choosing its Lean packaging,
resolve an observed universe mismatch with a small polymorphic signature test.
Explicit universe lifts and a heterogeneous total functor are competing
implementations of the same contract; neither has been implemented here.
The recommendation does not depend on a universal coherence framework, a
rewrite of existing clients, or completion of #723.

This assessment supplies a mathematical derivation plan, an application and
implementation acceptance criteria. It does not claim a checked totalization,
measured productivity improvement, or completion of #708's broader survey.
Here “coherent” means compatible local diagrams, not coherent modules in
algebraic geometry; “totalization” means a category over contexts, not a
total complex or a homotopy limit.

## What the interface would add

Write `CΓ = LocalCode G J Γ`, `SΓ = Sheaf (J.over Γ) (Type w)` and
`EΓ : CΓ ≌ SΓ` for the existing
[sheaf classification](../../SquareKit/Internal/CoherentSheafOver.lean).
For `σ : Δ ⟶ Γ`, the current reindexing is

```text
Lσ = EΓ.functor ⋙ sheafPullback σ ⋙ EΔ.inverse.
```

A native total arrow `(Δ,A) ⟶ (Γ,B)` consists of this actual base map `σ`
and an arbitrary map `f : A ⟶ Lσ B`. Decoding should give

```text
(σ, EΔ.functor.map f ≫ (decodeReindex σ).hom.app B).
```

Full faithfulness and `decodeReindex` yield, on paper, a bijection between
native and decoded maps over each fixed `σ`. Identity/composition compatibility
then gives a functor. A coherent inverse and vertical recovery give an
equivalence over the same base. Require both projection equations, original
fibre recovery and preservation of cartesian arrows in both directions.
This includes noninvertible fibre maps. It does not equate arbitrary chosen
pullbacks or cartesian lifts by equality.

The sheaf total already exists through Mathlib's
[pseudofunctorOver](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/PseudofunctorSheafOver.lean)
and CoGrothendieck construction. The added theorem connects the independent
local presentation to that capability. The existing
[coherent-family total bridge](../../SquareKit/Internal/CoherentFamilyFibration.lean)
uses different fibres and strict precomposition; its total-map machinery is
reusable, but its fibres cannot replace the local-sheaf category.

## Missing proofs towards that contract

| Obligation | Existing evidence | Remaining work |
| --- | --- | --- |
| Substitution forms a pseudofunctor | `reindex`, `reindexId`, `reindexComp` | Prove associativity and both unit equations for these chosen comparisons, including base equality transports. |
| Decoding commutes coherently with substitution | `decodeReindex`, `decodeReindex_id`, `decodeReindex_comp` | Package a strong transformation after resolving universes; respect contravariant argument order and comparison orientation. |
| Encoding and both round trips commute with substitution | Fibre equivalence units/counits and their triangle identities | Derive inverse comparisons, their coherence and compatible unit/counit modifications. |
| Total recovery retains maps and base changes | Mathlib totals/maps and local `CoGrothendieckMap` | Apply them or a bounded heterogeneous variant; prove projection, fibre and cartesian preservation results. |

The first row is derivable on paper by applying the faithful decoder, rewriting
with the existing compatibility equations, and using sheaf substitution
coherence. Inverse coherence follows from naturality and the equivalence
triangle identities. These are proof obligations, not new sheaf axioms or
caller-supplied fields. The [contract assessment](coherent-sheaf-totalization-design/contract.md)
records the exact orientations and proposed derivations. None is presented as
an already checked new theorem.

Keep the original recovery isomorphisms accessible. If `Equivalence.mk` adjusts
the unit, separately prove verticality of the packaged unit; do not identify
it with the supplied unit without proof. Cartesian preservation concerns the
universal property of substitution, not just the chosen lift constructor.
The [Stacks Project's account](https://stacks.math.columbia.edu/tag/02XJ)
supports the relevant distinction: an equivalence over a base with vertical
recovery preserves strongly cartesian arrows. An equivalence of underlying
categories alone does not state that contract.

## An application that tests the benefit

Let `K : I ⥤ D` be a diagram of contexts. A system of local presentations has
a code over each `K.obj i`, and maps into reindexed codes along each arrow of
`I`, satisfying identity and composition laws. Maps need not be invertible.
A commuting square of such data is one example.

The total interface expresses this system as a functor `A : I ⥤ CodeTotal`
with projection `K`. Its decoded system is `A ⋙ totalDecode`. Whiskering total
recovery gives a natural round-trip isomorphism over the same `K`, recovering
the whole system and its compatible maps. Cartesian transition arrows are
retained when present; they are not imposed on every transition.

This makes a mathematical setting and its context changes available through
ordinary functor composition. Currently each such client can insert the
fibrewise decoder comparisons by hand; a coherent total bridge discharges
that work once. The useful acceptance example is generic diagram recovery
with projected naturality, not only a closed Boolean calculation. It need not
introduce a new framework of sections: the ordinary functor and whiskered
recovery theorem suffice for the first application. A category of diagrams
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
specific round trip `d* ∘ p* ≅ Id`. These total-arrow tests remain proposed.
The existing source proves `collapse_not_iso` and `code_collapse_not_iso`.

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
requires a common `Cat` universe. A naive lifted-equivalence chain also failed
typeclass synthesis; it is not a verified repair. The
[reproducer and diagnostics](coherent-sheaf-totalization-design/contract.md#reproducible-checked-probe-and-validation-limits)
preserve the evidence. These failures identify an encoding obligation, not a
mathematical impossibility.

The first implementation checkpoint should compare explicit object/hom lifts
with recovery to native fibres against a small heterogeneous total-map
construction. Require a passing polymorphic signature and one abstract arrow
composition before selecting the route. Keep `Type w` unchanged and lifts
internal to the adapter; equalizing site universes is not an acceptable fix.
No general claim about which encoding costs less follows from the failed probe.

## Alternatives and ownership

| Route | Assessment |
| --- | --- |
| Direct sheaf total | Already useful without density assumptions. Keep it for callers supplying sheaves; it does not provide native local-code total recovery. |
| Transported pseudofunctor and existing totals | Preferred mathematical route. Derive coherence from fibre equivalences; resolve the common-universe packaging explicitly. |
| Native totals with heterogeneous comparison | Same intended mathematics and original universes; may need a small total-map helper rather than Mathlib's common-Cat transformation API. Compare at the first checkpoint. |
| Induced total whose homs are decoded sheaf arrows | Credible fallback. Recover native `A ⟶ Lσ B` homs and their composition explicitly; defining homs through the decoder alone does not prove native recovery. |
| Displayed/fibred presentation | Legitimate alternative foundation. With these native substitutions it still owes coherent composition. The current represented-display specialization has extra hypotheses. |
| Split replacement or local universes | Relevant when strictly stable logical structure is required. This total equivalence needs coherent substitution, not a new strict type-theoretic model. |

The [alternatives report](coherent-sheaf-totalization-design/alternatives.md)
compares primary treatments of displayed categories and local universes, with
their hypotheses and access limits. nLab page retrieval failed; search-index
orientation is not a completed page survey. No claim of exhaustive literature
coverage or completion of #708's nLab coverage requirement follows.

[#723](https://github.com/VladimirMarko/conaled/issues/723) owns shared coherence
extraction. A concrete overlap is already visible:
`CategoryTheory.inverseSquareAcross`, its specification, composition and
canonical equations in [StackificationUniversal](../../SquareKit/StackificationUniversal.lean)
operate on ordinary equivalences and compatible squares with independent
universes. Specializing the forward square to `decodeReindex.symm` is a
paper route to inverse comparison and recovery compatibility. It still needs
identity normalization and a checked specialization. The
[use report](coherent-sheaf-totalization-design/use.md#boundary-with-723)
records that mapping. Reuse or move the small generic lemmas if justified;
do not import stack assumptions into the sheaf contract. #723's two-consumer
criterion governs shared extraction, not whether this adapter may be developed.

## Implementation acceptance and assessment limits

The recommended next task is bounded by these requirements:

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

Only the universe probes executed new Lean elaboration, using existing artifacts;
there was no adapter implementation, integrated build, audit or author trial.
The remaining arguments and examples are paper-level plans backed by inspected
source. Documentation receives content/link checks and separate Standards/Spec
acceptance review. Broader facade-aware usage sampling, remaining-family ranking,
deeper categorical coverage and other #708 acceptance items remain open.
