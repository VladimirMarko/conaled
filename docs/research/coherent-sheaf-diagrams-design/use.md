# Implementation and use assessment

Recommend a bounded fixed-context categorical equivalence and its restriction to cartesian sections. The useful addition is access to universal-property transport for systems and vertical maps over a chosen context diagram. Existing diagram recovery already handles objectwise and arrowwise round trips; repeating that result in another structure would not justify the work.

This assessment uses source inspection and a checked conditional consumer. It does not construct the proposed equivalence or prove that these section categories have equalizers.

## Mathematical use

Let `A`, `X`, and `Y` be systems over the same `K : I ⥤ D`, with arbitrary vertical transformations `h : A ⟶ X` and `f,g : X ⟶ Y`. Suppose `h ≫ f = h ≫ g`. The desired application is:

> `h` is the equalizer of `f,g` among systems over `K` exactly when its decoded fork is the equalizer of the decoded transformations among sheaf systems over `K`.

This gives a representation-independent category of solutions to a pair of compatible constraints. A sheaf-side construction can establish its universal property there, and the equivalence reflects that property to local codes. The statement quantifies over whole systems and their compatible vertical maps, including noninvertible maps. It is not merely componentwise recovery. The same use applies within cartesian sections, provided the fork and its universal property are stated in that restricted category.

No equalizer-existence hypothesis is needed for preservation or reflection of a supplied limiting fork. Transferring existence requires a separate assumption that the sheaf-system category has the relevant limits. Neither the existing total equivalence nor this proposal alone proves that assumption. In particular, do not silently infer that pointwise equalizers form cartesian sections without checking their compatibility with reindexing.

The restriction to vertical maps matters to this application. As a paper-level separating example, take `I` terminal, `C = D = Type`, projection the identity, and `K` the object `Bool`. The categorical fiber has only identity vertical endomorphisms and is equivalent to the terminal category. The full subcategory on objects projecting to `K` retains all endomorphisms of `Bool`, including both constant functions; its sole object is not terminal. Thus an unrestricted diagram-category limit theorem does not establish the corresponding fixed-context universal property.

## Proposed contract

For any projection `p : C ⥤ D`, define diagrams over `K` using the existing Mathlib category:

```lean
Functor.Fiber ((Functor.whiskeringRight I C D).obj p) K
```

An object is `(A, hA : A ⋙ p = K)`. An arrow from `(A,hA)` to `(B,hB)` is a natural transformation `η : A ⟶ B` with

```lean
Functor.whiskerRight η p = eqToHom (hA.trans hB.symm)
```

The actual Mathlib representation expresses this through `IsHomLift`; the displayed equation states its intended meaning.

Specialize to the code and sheaf total projections and provide an equivalence between these fibers. Its forward and inverse functors must have underlying objects `A ⋙ totalDecode` and `A ⋙ totalCode`, and underlying maps the corresponding whiskered transformations. Unit and counit should recover the existing whiskered total unit and counit. Retain the original site/value assumptions and independent universe parameters. No cartesian condition belongs in this unrestricted fixed-context category.

Cartesian sections form the full subcategory *inside that fiber* whose objects map every index arrow to a cartesian total arrow. Restrict the equivalence to these full subcategories. Maps between cartesian sections remain arbitrary vertical natural transformations; requiring their components to be invertible or cartesian would discard the equalizer application and existing noninvertible maps. Context arrows in `K` remain arbitrary. Keep the existing unrestricted functor-category and total APIs for transformations involving changing context diagrams.

## Existing infrastructure and remaining obligations

Inspected sources:

- `Examples/CoherentSheafFibration.lean:29–144` already supplies both diagram round-trip isomorphisms, projected recovery, naturality for arbitrary transformations, compatibility over `K`, and forward/recovered cartesian preservation.
- `SquareKit/Internal/CoherentSheafFibration.lean:183–214`, `:274–376`, and `:401–413` supply total functors, projections, original vertical unit/counit in both directions, total equivalence, and cartesian preservation in both directions.
- Mathlib `CategoryTheory/Equivalence.lean:418` supplies `Equivalence.congrRight`. Thus unrestricted functor-category equivalence needs no new generic construction.
- Mathlib `CategoryTheory/FiberedCategory/Fiber.lean:38–132` supplies the category with restricted morphisms, inclusion, constructors and `inducedFunctor`. Its inclusion is faithful; it is not declared full. Reuse this category instead of inventing another section record with its own identity/composition laws.
- Mathlib `CategoryTheory/ObjectProperty/Equivalence.lean` supplies `Equivalence.congrFullSubcategory`. It can handle the cartesian restriction after proving the predicate correspondence and closure under isomorphism. It cannot directly implement the first fixed-context restriction, because that restriction changes homs.
- Mathlib `CategoryTheory/LocallyCartesianClosed/Sections.lean` supplies the dependent-product/right-adjoint sections functor for objects of an over category. That is a different operation from the category of functorial lifts of `K` considered here.
- Mathlib `CategoryTheory/Limits/Preserves/Shapes/Equalizers.lean:52–60` supplies preservation/reflection of limiting forks. `CategoryTheory/Adjunction/Limits.lean:259` transfers existence along equivalences.

The new proof work is restriction to the categorical fibers, including verticality of images and of inverse homs, and descended unit/counit. After that, the cartesian restriction needs predicate preservation/reflection and closure under vertical natural isomorphism. The supplied total data make these obligations plausible; they are not discharged by merely exhibiting an equivalence of all functor categories.

The smallest useful reusable abstraction is a fiber-equivalence adapter for an ordinary equivalence commuting with two projections and having vertical unit/counit. Apply it to the postcomposition equivalence. If that adapter becomes cumbersome, a direct fixed-diagram specialization is a bounded alternative. Do not add a new general theory of sections, pseudofunctors or descent at this checkpoint.

## Checked consumer and author cost

`/tmp/conaled-diagrams-assessment/use/Consumer.lean` passed:

```sh
direnv exec /home/vlad/Code/conaled lake env lean /tmp/conaled-diagrams-assessment/use/Consumer.lean
```

The final run exited zero with no Lean diagnostics. It checks:

1. The proposed system categories elaborate as fibers of postcomposition, and ordinary `(A,hA)` objects enter them directly.
2. `Equivalence.congrRight` packages the unrestricted diagram equivalence.
3. Given an equivalence of the fixed-context fibers, a supplied limiting fork maps to a limiting fork using `isLimitForkMapOfIsLimit`.
4. A limiting decoded fork reflects to a limiting source fork using `isLimitOfIsLimitForkMap`.
5. Assuming equalizers exist on the target side, `Adjunction.hasLimitsOfShape_of_equivalence` transfers existence to the source.

The conditional equivalence parameter is the precise missing producer contract, not an assumption that the equalizer conclusion already holds. The experiment tests the proposed consumer interface against existing Mathlib operations. It does not test the producer, a concrete sheaf equalizer, or cartesian restriction. Its initial namespace error was repaired by opening `CategoryTheory.Functor`; that was an encoding mistake, not mathematical evidence.

An initial project-specific probe in `use/Probe.lean` stopped at import because the current checkout lacks `Examples/CoherentSheafFibration.olean`. No build was started. The passing consumer uses only Mathlib; source inspection supplies the connection to the current sheaf API. No integrated build or proof audit was run, and no tracked files changed.

Caller setup remains construction of a system functor, its projection equation, vertical transformations, and cartesian-transition proofs when using cartesian sections. The new equivalence removes repeated restriction/recovery bookkeeping and lets each universal-property application use existing category-theory APIs. Shared preparation includes the fiber adapter, proof-transport simp lemmas and cartesian predicate laws. Maintenance should remain bounded by reusing `Fiber`, `congrRight` and full-subcategory restriction rather than maintaining parallel categories. This evidence supports mathematical reuse; it does not measure a general author-productivity improvement.

Retain the existing diagram lemmas and Boolean noninvertibility/composite-context example. Add the conditional universal-property consumer through the implemented public equivalence, plus a noninvertible vertical-map case and universe checks, as implementation acceptance. A separate construction of sheaf-system equalizers can follow if needed; it should not block this bounded equivalence.
