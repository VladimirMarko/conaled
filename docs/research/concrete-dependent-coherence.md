# Concrete dependent models: when to construct categorical coherence

Assessment for [#318](https://github.com/VladimirMarko/conaled/issues/318),
under [#289](https://github.com/VladimirMarko/conaled/issues/289).
**Defer a new categorical strictification package for the present consumer;
retain the direct construction investigation.** No current implementation
demonstrates a capability or recurring model-builder obligation that the
package would improve. This is a conditional construction decision, not a
failure of local universes in groupoids or a claim that their hypotheses have
all been proved. The promotion conditions below keep the Kan-fibration route
available if it supplies the required higher interpretation or avoids a
demonstrated coherence burden.

The evidence begins with the [architecture reassessment](dependent-architecture-reassessment.md),
its three independent assessments, [#292](dependent-coherence-comparison.md),
and the unchanged [external memo](dependent-coherence-discovery/292-external-memo.md).
The [#314 reconstruction](dependent-structure-audit.md) supplies new structural
proofs; the [#316 investigation](https://github.com/VladimirMarko/conaled/issues/316) supplies a checked
external dependent higher test and an exact remaining Lean construction.
The inspected revisions are #314's independently approved
`3484ce523bf23524f715a3a2029c290a2d43c4c0` and #316's supplied candidate
`ca54f31646bd60e1866efc39f257db5b27dc17fc`, pending independent review at this
assessment. The latter's report is `docs/research/dependent-higher-identity.md`
at that revision; its validation receipt is external source evidence, not a
Lean interpretation. No new Lean definition, assumed-law record, or
replacement source judgment is introduced by this assessment.

## The consumer and the possible gain

All four routes below are compared against the memo's same fragment: a terminal
context, dependent context extension and substitutions, schematic `A` and `B`,
object-language Σ,
intensional Id, reflexivity, and contextual J for arbitrary admitted motives
and finite dependent tails, with computation and substitution. The selected
terms are `w=(v,η)` and `apd_η(h)`, including its transported source. Substituting
by σ and then τ must agree with their composite on the term **and its type**.
The first observation distinguishes integer-action transport values 3 and 2;
the higher observation retains a nontrivial second identity through
`β⁻¹ · ap_T(h) · β = h`. It does not demand that `apd_η(h)` itself be nontrivial.
Neither an object-language universe nor univalence occurs in this generic
argument. A contextual package without a Σ interpretation cannot silently
replace the specified dependent pair.

| Construction route | Evidence for this consumer | Potential gain and present decision |
|---|---|---|
| Direct strict model | Ordinary groupoid substitution and contextual J are constructed. #316's external source test checks the full higher observation, but its Lean direct higher interpretation is still missing. | Continue the strict higher-family/J construction in #322. Recovering the existing ordinary substitution laws supplies no new gain. |
| Local universes for a weak model | #292 checks Type-family Σ and dependent currying. No Kan comprehension/LF/weak-elimination package is constructed in Lean here. | A selected Kan model could obtain strict elimination from weakly stable filler existence. Defer construction until that model is selected for the higher consumer or demonstrates reusable savings. |
| Coherent right splitting | No coherent pseudo-stable higher eliminator package is exhibited by #314 or #316. Existing ordinary strict J needs no such repair. | Eligible if a provider already supplies coherent comparisons of the whole constructor. Weak filler existence alone does not provide that input. |
| One chosen classifying universe | No selected classifier and closure construction for the memo's families is supplied by these investigations. | Eligible if a classifier is already needed or makes this consumer's closure/computation construction simpler. Schematic `A,B` do not themselves justify that additional implementation. |

This is not a claim of equal capability among the routes. The ordinary groupoid
model has discrete identity fibers and cannot supply the nontrivial second
identity. #316's direct higher route is a proposed construction with a precise
remaining theorem, while Kan and chosen-universe models have external existence
results. A lack of an adapter to current annotations is not a reason to reject
either alternative.

In particular, #316's failure of a strict-natural contraction on the `B²ℤ`
path family does not identify a substitution-strictification problem. The
missing family data include the action of a base 2-cell on fiber functors;
the contraction needs coherent 2-cell witnesses. A general strictifier cannot
manufacture those semantic operations from the present ordinary family record.
The exact dependent-family and all-motive-J prerequisite belongs to
[#322](https://github.com/VladimirMarko/conaled/issues/322). Its closure under
the proposed finite-dimensional restriction is also unproved.

Warren's Theorem 7.1 establishes the strict ω-groupoid interpretation of
intensional Π/Σ/Id, including the stated η-rules. The Grothendieck, open identity
and elimination constructions in §§3, 5–6 are evidence for a direct route.
They do not constitute a checked restriction to this project's proposed
2-groupoids or its Lean judgment interpretation.
[Warren, *The Strict ω-Groupoid Interpretation of Type Theory*](https://mawarren.net/papers/crmp1295.pdf)

## Which category of families has been reconstructed

Use the **all-square display category** for the structural comparison.
Its objects are `(Γ,A)` from the existing `StructuralModel`; an arrow is an
arbitrary commuting square between the two context projections. In
[`DisplayCategory`](../../SquareKit/Internal/PathTransport/DisplayCategory.lean),
`comprehensionFullyFaithful` constructs the inverse on homs,
`displayPullback` proves the chosen square is a pullback, and
`display_cartesian` proves unique factorization over each chosen reindexing.
Fullness is therefore a checked result for those arrows. It does not require
another fullness field in the generic model.

The concrete comparison has two different outcomes:

- For Type families,
  [`FamilySquares.equivalence`](../../SquareKit/FamilySquares.lean) identifies
  all dependent functions over a base map with all squares of dependent-sum
  projections. Both inverses and preservation of identity/composition are
  proved. #292's `displayCurry` and `displayCurry_natural` supply the relevant
  Type-family section representation, rather than an assumed adjunction.
- For groupoid families, #314's `sectionsOver` concerns actual functors into
  total groupoids over a specified base functor. It retains arrow coherence;
  it is not merely an objectwise section. The full-square presentation can be
  used as defined. A separate equivalence with a chosen transformation category
  of functors `Γ ⥤ Grpd` has not been proved.

There is a checked obstruction to replacing those arrows by maps that strictly
preserve the chosen cleavage. In
[`GroupoidComprehensionBoundary`](../../Examples/GroupoidComprehensionBoundary.lean),
the constant C₂ family over C₂ has a total-groupoid shear
`(g,h) ↦ (g,g+h)`. Its projection square commutes, but the nonzero horizontal
lift `(1,0)` goes to `(1,1)`. Thus the identity-on-objects inclusion of
chosen-lift-preserving maps into all squares misses this arrow. This excludes
that fullness claim; it proves neither failure of the all-square comprehension
category nor failure of LF.

If a future implementation chooses transformations of concrete families as
its public arrows, #289 must require an explicit comparison functor with the
all-square presentation: map objects and arrows, prove functoriality, and
establish exactly which homs it covers. Pseudonatural comparison data are a
candidate, not a theorem already supplied by #314. If the chosen arrows remain
strictly cleavage-preserving, use a theorem appropriate to that restriction
instead of transferring the all-square fullness result. These choices concern
family morphisms; they do not change the object-language identity witnesses
into equalities of arrows in the metatheory.

## Transfer theorem scope

Lumsdaine–Warren Theorem 3.4.1 requires full comprehension, LF and the relevant
weakly stable constructors. For this consumer use Σ and Frobenius Id, including
dependent tails (§3.4.3). LF requires finite products and dependent exponentials
along display maps for display maps and product projections. Lemma 2.4.2 instead
uses pseudo-stability of whole constructors, including elimination. Section 4.1
does not transfer additional type-equality rules. Theorem 4.2.2 and Examples
4.2.5 give applications to the stated logical model structures, including
canonical groupoids and Kan simplicial sets; they do not identify our restricted
family presentation with those categories.
[Lumsdaine–Warren, §§2.4, 3.1, 3.4, 4](https://arxiv.org/html/1411.1736v2)

For a chosen universe, Kapulkin–Lumsdaine Proposition 1.3.3 constructs a
contextual category from a terminal object, a map `Ũ→U`, and chosen pullbacks.
Theorem 1.4.15 transfers the specified constructor structures on that universe
in the locally cartesian closed setting. Definition 1.4.8 includes an internal
lifting operation for Id, not just an identity code. Theorem 2.3.4 constructs
the simplicial closure structures for an inaccessible size bound; its internal
universe result uses a second inaccessible. These are assumptions of the cited
construction, not lower bounds for the memo's universe-free fragment.
[Kapulkin–Lumsdaine, §§1.3–1.4 and 2.3](https://arxiv.org/pdf/1211.2851v5)

## Remaining obligations for a concrete application

The following are construction obligations for this project, not new premises
added to every `Model`. No blanket LF failure is inferred from their absence.

**Ambient products and size.** The groupoid instance actually uses
`Context := Grpd.{u,u}`, families `Γ ⥤ Grpd.{u,u}`, and lifted sections and
substitutions in `Model.{u+1}`. The object/arrow carriers of individual groupoids
and the collection of all such groupoids live at different levels. A package
must track those levels through total groupoids, section objects and parameter
objects. The existing `universeModel` handles independent carrier universes for
the current instance; it is not a proof of closure for new higher families.

For the ambient ordinary groupoid category, a candidate terminal object is the
one-object, one-arrow groupoid, and products have componentwise objects and
arrows. The missing package must prove unique functors into the former and the
pairing/projection hom bijection for the latter, including its naturality in
the source. This assessment does not add those Lean proofs. A Kan variant must
make the same statements in its actual category of bases, with a declared size
bound and proof that the chosen bases contain the representing objects below.

Do not infer these ambient properties from the word `empty`. #314 distinguishes
the full Bool countermodel with no ambient terminal object, its reachable
component, and `ReachableLoops`, where a reachable empty object still has
distinct ambient endomorphisms. Its generated empty substitution proves
existence, not source uniqueness or ambient terminality. Restricting to
generated contexts and generated arrows is a third category. That restriction
must separately admit products and the parameter objects used by the chosen
construction; source Π-free syntax alone gives no such closure. Alternatively,
construct in an adequate ambient category and prove the interpretation of the
generated fragment lands there.

**LF representation with the actual arrows.** For the all-square groupoid
candidate, let `f:Γ.A→Γ` be a display map. For each `g:Z→Γ.A` that is a display
map or a product projection, the missing deliverable is an object `P→Γ` with
an equivalence of the actual sets of slice morphisms

```text
Hom/Γ(W,P) ≃ Hom/(Γ.A)(W ×Γ (Γ.A), Z),  for every W→Γ.
```

Construct evaluation and both directions, prove both inverse equations, and
prove that precomposition by every `W′→W` over Γ commutes with this equivalence.
For a display `g`, a proposed fiber of P consists of sections over the fiber
of A, including their coherence. Its arrows and base action still have to be
constructed and checked. For a projection `g:(Γ.A)×V→Γ.A`, the candidate
representation concerns functors from each fiber to V with their arrow data.
Objectwise functions or a count of objects do not establish either universal
property. P need not itself be an object-language type. Proving the stronger
right adjoint on every slice object is an option, but is not the minimum
deliverable here. These are the specialized LF obligations of
[Definitions 3.1.2–3.1.3](https://arxiv.org/html/1411.1736v2#S3.SS1).

**Constructor data for the fragment.** A local-universe candidate needs a
weak-model interpretation of the *whole* admitted Σ and Id rules. For Σ this
includes dependent second components and dependent elimination with its branch
and computation. For Id it includes the reflexivity map, every finite tail T,
each motive D over the extended identity context, and each branch d over the
reflexive pullback. Reindexing the chosen Id/reflexivity structure must leave
it able to eliminate every newly supplied motive and branch over that base,
with reflexive computation; reindexed Σ/pair data need the corresponding
dependent elimination property. Weak stability does not demand preservation
of a previously selected eliminator. Merely supplying
path objects or fillers for the transport motive does not discharge this
obligation. The project must also record any choice principle used to select
operations from existence proofs.

A right-splitting candidate must additionally provide the chosen eliminators'
comparison data: how a reindexed motive and branch determine the compared
section, and how those comparisons compose and act at identity substitutions.
Objectwise isomorphisms of Id or Σ cannot replace that comparison. This is
exactly where a hypothetical weak Kan provider with only existence of fillers
would leave more work than a provider with a coherent chosen filling operation.
No impossibility of coherent choices for the concrete candidate is proved.

A chosen-universe candidate has a different first obligation: exhibit codes
and decoding comparisons for the two parameter instances, the path family,
Σ/Id outputs, and all admitted motives/tails. Then construct their generic
constructor and elimination structures and show the chosen decoding comparisons
commute with substitution. If using Π to derive contextual J, prove that closure
too. No current report supplies that classifier or its coverage. An additional
strict code-decoding type equation, if promised later, must be checked as its
own judgment rather than inferred from the present transfer result.

**Selected clients and comparisons.** Any adopted replacement must recover
`Typed.Authoring.UniversalTransfer.proof` and its groupoid interpretation,
the dependent conversion in `DependentCongruence.DependentArguments.dependentPair`,
and the native #292 Type-family pair. Their retained baseline contracts are in
the [fixture inventory](dependent-coherence-fixture.md). New Σ judgments must
also interpret the memo's actual `w`. The comparison must act on contexts,
families, sections and substitutions, carry terms through the specified type
comparison, and satisfy unit/composition and J branch compatibility.

For the higher candidate, attach the detector to the interpreted
`β⁻¹ · ap_T(h) · β`, preserving the selected h and the substituted `apd_η`
source. Equivalence of endpoint types alone is insufficient. A deliberately
lossy interpretation remains valid for its stated lower-dimensional
observations, but cannot certify the higher gate. None of these comparison
obligations is discharged by decoding two local-universe presentations to the
same Type; #292's presentation counterexample rules out that shortcut.

## Promotion conditions and ownership

The decision is based on present constructions, not a limit on research effort:

| Decision | Owner and next evidence |
|---|---|
| Adopt #314's derived comprehension results for their stated arrows | #315/#317 can reuse them without assuming fullness or imposing LF on every interpretation. |
| Investigate the direct higher construction | #322 under #289 owns higher families, coherent contraction, dimension closure and arbitrary-motive contextual J, then the actual connected interpretation and detector. |
| Defer a new local-universes package | #289 promotes it when a selected weak model supplies the needed higher dependent capability and strict stability remains the missing step, or when a matched construction records recurring coherence proofs that the transfer eliminates. Then construct the obligations above for that model and recover the selected clients. |
| Keep right splitting and chosen universes eligible | #289 selects right splitting when coherent whole-constructor comparisons are available, or the chosen-universe route when an actual classifier with required coverage/closure offers a concrete gain. Compare on this same fragment before construction. |
| Keep the cubical alternative separate | #321 owns cubical calculus/model/source compatibility. Its selection would trigger a new model-specific comparison, not automatically an LF requirement. |
| Defer higher adoption and author-cost claims | #316's Agda test is positive source evidence, not a Lean model or interpretation. #320 must retain that boundary; #315/#317 own judgment and constructor admission. |

For example, a future Kan-family implementation with the memo's nontrivial h,
arbitrary-motive weak J and reindexed dependent branches would give a named
consumer for local universes if chosen fillers were the remaining strictness
burden. At that point the benefit is a constructed higher interpretation from
that provider, and #289 must assign its categorical package and comparison
proofs. The present ordinary groupoid J already supplies strict stability;
#322 has not yet reached the corresponding higher weak-J provider. Absence of
that evidence is the reason for deferral today. It is not a finding that Kan
models lack a benefit in general.

Model-builder effort, ordinary-author effort and host encoding cost remain
separate. The report compares mathematical obligations; it times no builder or
author and establishes no productivity saving. Strictification alone would not
repair the paused fresh-versus-substituted annotation problem. #107 remains
paused, #108's independent theorem is neither selected nor prepared, and #260
is not activated.

## Evidence and validation boundary

This report reads the cited primary theorem statements and their relevant
construction sections, the #314 reconstruction and shear example, the current
groupoid implementation, and #316's source-test report and exact continuation.
It adopts no unproved categorical hypothesis as a library field. Failed
inferences are retained explicitly: generic nonterminality is not concrete
groupoid failure; all-square fullness is not cleavage-preserving fullness;
strict type substitution is not arbitrary-motive J; higher contraction data
are not generated by renaming ordinary records; decoded equality is not source
conversion.

Validation for this documentation-only change checks the cited local targets,
declaration names, immutable memo and evidence revisions, Markdown whitespace,
and the exact candidate diff. The #314 build/audit and #316 external source
receipt remain evidence from their own work; no new Lean build, proof audit,
Agda run, categorical theorem or higher interpretation is claimed here.
Independent Standards and Spec review of this assessment is recorded in the
implementation handoff.
