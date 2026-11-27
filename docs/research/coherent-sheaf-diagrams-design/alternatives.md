# Alternatives and generality assessment

Recommend a bounded generic diagram-category construction with a thin sheaf specialization. Reuse Mathlib's existing category of based functors, or its categorical fibre of postcomposition, rather than defining sheaf-specific objects and morphisms. Of the inspected alternatives, the based-functor category is the smallest existing interface for direct callers: it already stores a diagram over K, arbitrary vertical natural transformations, composition and whiskering. The fixed-K categorical-fibre presentation is equally faithful mathematically, and may be preferable if the implementation establishes a reusable equivalence-on-fibres theorem. There is no evidence that a new general section or pseudofunctor framework is needed.

This is selection evidence, not implementation acceptance. Baseline inspected: `ba7ee812cbcc3024c235e72832d1f4aa840a5139`. I coordinated #725's earlier independent acceptance reviews and read their completed reports. I have that prior exposure to the implementation; I have not read or discussed the current contract/use assessments. No repository source was edited and no agent was spawned.

## Existing constructions

1. `Functor.Fiber` in Mathlib `CategoryTheory/FiberedCategory/Fiber.lean:36–46` already supplies the exact strict fibre category. Apply it to `(Functor.whiskeringRight I X D).obj p` at `K : I ⥤ D`. Objects are pairs `(A, A ⋙ p = K)`. A morphism is a natural transformation whose image under postcomposition lifts `𝟙 K`; the equality transports are handled by `IsHomLift`. Thus it includes every vertical natural transformation, including noninvertible ones. `fiberInclusion` and `inducedFunctor` already provide the forgetful and factoring interfaces. I found no existing equivalence-on-fibres construction in that file or the related fibre modules inspected.
2. `BasedCategory.ofFunctor`, `BasedFunctor`, and `BasedNatTrans` in `CategoryTheory/FiberedCategory/BasedCategory.lean:51,57,138` provide another existing presentation:
   `BasedFunctor (BasedCategory.ofFunctor K) (BasedCategory.ofFunctor p)`.
   Its objects have `toFunctor : I ⥤ X` and `w : toFunctor ⋙ p = K`. Its morphisms are arbitrary natural transformations with componentwise `p.IsHomLift (𝟙 (K.obj i))`. The category instance at line 184 and whiskering operations at lines 258 and 269 already perform the required bookkeeping. The source and target of `BasedFunctor` have independent object/hom universes. This differs from using the single-universe bicategory instance at the bottom of the file; that instance is unnecessary here.
3. `Equivalence.congrRight` in `CategoryTheory/Equivalence.lean:418` already lifts any ordinary equivalence to the unrestricted functor categories, retaining explicit whiskered unit and counit. It does not restrict the objects to fixed K or the morphisms to vertical maps. The remaining generic work is that restriction, not a new proof of diagram recovery.
4. `Equivalence.congrFullSubcategory` in `CategoryTheory/ObjectProperty/Equivalence.lean:66` can restrict an equivalence along a property invariant under isomorphism. It applies to the cartesian-object condition *after* the category of diagrams over K has been built. It cannot be applied directly to the property `A ⋙ p = K` inside the ordinary functor category: the fixed-base morphism condition is not full.
5. The other inspected section APIs address different objects. `Functor.sections` in `CategoryTheory/Types/Basic.lean:221` is the set of compatible elements of a Type-valued functor. `Over.sections` in `CategoryTheory/LocallyCartesianClosed/Sections.lean:68` is an internal object of sections, with closed-object and chosen-pullback assumptions. Neither supplies a category of arbitrary lifts of K, and importing their stronger assumptions would be unnecessary.

All Mathlib statements above refer to the repository's pinned source, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The repository implementation already supplies total equivalence, strict projection equations and vertical recovery (`SquareKit/Internal/CoherentSheafFibration.lean`, especially `totalEquivalence` at line 308). The existing `Examples/CoherentSheafFibration.lean:29–146` proves recovery, projected recovery, compatible maps and cartesian preservation for individually supplied diagrams. Packaging makes these usable as a category equivalence; it should not add sheaf hypotheses or replace the direct diagram theorems.

## Proposed bounded contract

For independently universe-polymorphic categories X, Y, D and I, let `p : X ⥤ D`, `q : Y ⥤ D`, and `K : I ⥤ D`. Define at most a convenience abbreviation

```lean
DiagramsOver p K :=
  BasedFunctor (BasedCategory.ofFunctor K) (BasedCategory.ofFunctor p)
```

Use its existing category instance. Given an ordinary `e : X ≌ Y`, its two strict projection equations `e.functor ⋙ q = p` and `e.inverse ⋙ p = q`, and proofs that the supplied unit/counit components lift the corresponding identity base arrows, construct

```lean
DiagramsOver p K ≌ DiagramsOver q K
```

with forward/inverse operations exactly postcomposition, and original unit/counit components exactly the supplied components whiskered by A. The based-functor version can accept the two functors already bundled as `BasedFunctor`s and the vertical isomorphisms already bundled as `BasedNatIso`s. This is an adapter of an established equivalence, so accepting that equivalence is not a circular premise; the new result is its restriction to the fixed-K category. Avoid a new structure bundling redundant versions of these inputs. Keep the original recovery explicit rather than rebuilding an arbitrary equivalence from full faithfulness and essential surjectivity.

For cartesian diagrams, use the object predicate that every transition `A.map f` is cartesian for p over its projected base arrow. This condition is meaningful for any p, without a global fibration or selected-cleavage hypothesis. Use the full subcategory of **DiagramsOver**, retaining all its arbitrary vertical morphisms. Restrict the generic equivalence once preservation and reflection of that object predicate have been proved. Two-way cartesian preservation and vertical recovery provide the required invariance, and vertical diagram isomorphisms preserve cartesianness by conjugation. That last generic proof is paper-level here, not executed.

The sheaf specialization should discharge all projection, recovery and cartesian premises from the existing public total API. Its arguments stay exactly the original full-faithfulness, cover-density, structured-arrow-limit and independent-universe hypotheses. Do not expose those generic coherence proofs as new sheaf caller arguments.

## Comparison and concrete concerns

| Choice | Reused mathematics | Remaining work and cost |
|---|---|---|
| Retain current individual diagram theorems | Existing total equivalence and whiskering | No new setup; clients cannot directly use a category equivalence at fixed K without rebuilding the vertical-map category. Reasonable if that categorical result is not adopted. |
| Based-functor category | Objects, vertical morphisms, category laws, map preservation, whiskering and based natural isomorphisms already exist | Small generic postcomposition/equivalence adapter and cartesian object restriction. Callers use `toFunctor`, `w`, and existing morphism fields. No shared universe is forced by the hom-category construction. Preferred starting point. |
| Fibre of postcomposition | Exact same intended object/morphism contract, fibre inclusion and generic factoring | A generic equivalence restriction on fibres, plus whiskering. More whole-natural-transformation `IsHomLift` bookkeeping than the componentwise based interface; not a mathematical defect. Prefer if that theorem yields wider reuse with comparable caller setup. |
| New sheaf-specific section records | Little beyond existing total API | Repeats category laws, vertical-map conditions and equivalence restriction. No sheaf-specific operation in this task justifies the duplicated definitions. |
| Pseudonatural/lax sections of a pseudofunctor | Potential access to a different, richer mathematical framework | Introduces coherence structures and universe packaging already avoided by native total functors. No retained requirement here needs it. Do not reject it generally; it is outside this bounded contract. |

An established representation error to prevent is treating fixed-K diagrams as a full subcategory of `I ⥤ X`. For example, take `p = 𝟭 (Type)`, I terminal, and K constant at Bool. The constant-false natural endomorphism exists in the ambient functor category but does not project to `𝟙 K`. A full subcategory would admit it. Conversely, once diagrams are cartesian, do not require their vertical natural transformations to be invertible or cartesian: that would discard valid arbitrary maps.

The equivalence's projection equations alone do not identify an arbitrary supplied recovery with vertical recovery. The proposed restriction must use the actual established vertical unit/counit, not silently manufacture compatibility fields. A generic based-equivalence wrapper could be useful later, but this task does not justify adding a new bicategory of such objects or a general adjoint-equivalence framework.

## Checked experiment and limits

`/tmp/conaled-diagrams-assessment/alternatives/Probe.lean` compiled successfully with

```sh
direnv exec . lake env lean /tmp/conaled-diagrams-assessment/alternatives/Probe.lean
```

The final command exited 0; log: `alternatives/probe.log`. The scratch file contains no admission or axiom. It checks:

- Both categorical-fibre and based-functor diagram category signatures with independent object/hom universes for I, D, X and Y.
- A generic postcomposition functor on the based diagram categories, using Mathlib's `BasedFunctor.comp` and `BasedCategory.whiskerRight`, including its actual map formula and identity/composition proofs.
- A concrete Bool diagram over a terminal base with its constant-false vertical endomorphism. The endomorphism is idempotent, differs from identity, and is not invertible. Thus the proposed existing category genuinely retains noninvertible vertical maps.

The scratch construction is a selection probe. It does not implement the generic equivalence or cartesian restriction, does not prove equivalence between the two candidate presentations, and does not measure productivity. No integrated build or exhaustive audit was run for this assessment. Initial failed attempts were namespace/import/coercion proof obligations, repaired without changing the expected mathematical statements.

If adopted, retain the Bool control through the *new equivalence* and add a nontrivial changing-context diagram using the existing sheaf total functors. Check cartesian objects separately while retaining arbitrary vertical maps. The current sheaf examples already give the context-changing and noninvertible ingredients; those should be connected to the categorical interface rather than duplicated. Generic proofs must then receive statement review and normal candidate validation.

The recommendation is bounded to packaging the existing mathematics into reusable fixed-K categories and their cartesian full subcategories. It does not settle #708's other presentation comparisons, #723's shared-coherence survey, arbitrary-base natural transformation transport, effective descent or stackification.
