# Finite higher completion

The first construction under [#721](https://github.com/VladimirMarko/conaled/issues/721)
completes normalized weak bicategorical diagrams on the opens of the discrete
two-point space. It retains objects, arrows and two-cells, and proves a mapping
biequivalence for the actual completion unit. The broader issue remains open.

## Contract and public entry points

`HigherCategory.FullDiagram` in
[`FiniteHigherDiagram`](../../SquareKit/FiniteHigherDiagram.lean) stores four
bicategories, five restriction pseudofunctors, and two comparison adjoint
equivalences. The nonidentity chains are top–left–empty and top–right–empty.
Identity restrictions are normalized. No triple of nonidentity restrictions
exists on this poset. This is an explicit finite presentation; comparison with
an arbitrary unital tricategorical diagram is a remaining representation task.

The generic records permit separate object, arrow and cell universes. The
completion and mapping theorem currently use `FullDiagram.{0,0,0}`. Their
bundled diagram type lives in the next universe. These bounds are an
implementation restriction, not a claim of arbitrary resizing or a mathematical
obstruction to other universes.

`FiniteHigherMap.Map` retains four weak pseudofunctors, five restriction
comparison equivalences and two invertible chain modifications. Its bicategory
has strong transformations with five comparison squares and both chain
equations, then modifications satisfying all five compatibility equations.
The proofs of composition and the bicategory laws retain those equations.
The generic mapping theory permits arbitrary bicategories; its higher-groupoid
applications use the corresponding invertible fibers.

The main operations and theorems are:

| Declaration | Contract |
| --- | --- |
| `TwoPointOpenSite.topology` | Mathlib Grothendieck topology on `Finset Bool`, with union covers. |
| `TwoPointOpenSite.covering_sieve_exists_kind` | Every covering sieve is one of six finite cases. |
| `FiniteHigherDescent.IsStackOnAllCoveringSieves` | Descent through the chosen normalized cone bicategories for every actual covering sieve. |
| `FiniteHigherDescent.stack_criterion` | Equivalent finite criterion: empty value is terminal up to biequivalence, and the pair of atomic restrictions is a biequivalence. |
| `FiniteHigherCompletion.completion`, `unit` | Replace top by the product of atomic values and empty by terminal, with the actual restriction pair as the top unit. |
| `FiniteHigherCompletionDescent.completion_allCoveringSieves` | The constructed completion satisfies the all-sieve descent predicate. |
| `FiniteHigherUniversal.precomposeStackUnit` | Actual-unit precomposition on full mapping bicategories, using empty descent to normalize comparisons. |
| `FiniteHigherUniversal.precomposeStackUnit_biequivalence` | Mapping universal property for every target satisfying the independent all-sieve predicate. |
| `FiniteHigherRecovery.unitLeftRecovery`, `unitRightRecovery` | Both literal composites of the actual unit and constructed inverse recover the identity maps on complete inputs. |

The completion does not require the input already to satisfy arrow or two-cell
descent. The target's inverse pseudofunctor is constructed from essential
surjectivity on objects and equivalences on hom categories. The mapping theorem
does not take extension, recovery or its own mapping equivalence as premises.
Its lower-level helpers expose chosen inverses for reuse; the public theorem
derives those choices from descent.

## Descent presentation

The six covering sieves are the empty and maximal sieves at the empty open,
the maximal sieve at each atom, the proper binary cover of the top, and the
maximal top sieve. The finite encoding is faithful to Mathlib sieves, every
listed cover is realized, and its union-cover test agrees with `topology`.

A binary cone contains a left value, a right value, a separate empty value,
and both equivalences to that empty value. Its arrows carry three components
and two squares; its cells satisfy both square equations. It is implemented as
a nested iso-comma bicategory. The actual restriction uses the original `cL`
and `cR`; component equalities verify that equality transport preserves their
forward arrows.

A maximal top cone is an iso-comma object over the binary restriction. Its
forward overlap arrow contains the three top comparisons and the two chain
cells. It also stores a chosen adjoint inverse. Atom cones are analogous graph
constructions. The empty sieve has terminal cone and the maximal empty sieve
has the original empty fiber. These definitions precede the completion and
its universal property. The graph and iso-comma projection theorems derive the
maximal-cover comparisons, while empty descent derives the binary criterion.

A general comparison to an unnormalized tricategorical cone interface remains
separate. The current theorem is about this explicit normalized presentation,
including the stored adjoint equivalences. It does not assert a formalized
strictification theorem for arbitrary coherent site diagrams.

## Higher information and controls

[`Examples.FiniteHigherCompletion`](../../Examples/FiniteHigherCompletion.lean)
uses the disjoint union of two copies of the existing double delooping of
`C₂`. All nonempty input fibers have that value, with identity restrictions;
the empty fiber is terminal. The actual unit is diagonal on the top fiber.

The mixed pair of object labels gives a binary descent cone with no global
representative. `input_not_stack` rejects the independent all-sieve predicate;
`output_stack` proves that predicate for its completion. At a diagonal object,
the mixed two-cell `(0,1)` has no input preimage, while the nonzero diagonal
two-cell `(1,1)` remains nonidentity under the actual unit. Thus the example
both adds effective data and preserves a second-level observation.
`input_bigroupoid` and `output_bigroupoid` prove both levels of invertibility
for the concrete top fibers, retaining the specified forward arrows.

The double delooping is Mathlib bicategorical data, not a postulated homotopy
group. Its endomorphism cells are actual elements of the abelian group.
`no_faithful_ordinary_encoding` proves that the actual output cells cannot
embed faithfully into the parallel cells of any locally discrete ordinary
category. This connects the existing `Examples.SecondIdentity` obstruction to
the completion output. A nerve-level computation of a homotopy group remains
a separate comparison.

The already-complete control uses the independently proved output as a new
input. `completeInverseUnit`, `completeUnitLeftRecovery` and
`completeUnitRightRecovery` construct its actual inverse and both literal
composite recoveries. `maps_into_output` exercises the public mapping theorem
for an arbitrary source and this concrete higher target.

The mapping controls also exercise the full site interface. Two weak maps
`BC₂ → B²C₂` have identical object and arrow actions but different compositor
cocycles. After packaging them as completed site maps, no full transformation
exists in either direction; their identity transformations remain valid. A
nonidentity full modification survives actual-unit precomposition and is
recovered through its hom equivalence. A separate empty-fiber example changes
only `chi_L`: the specified identity component/square candidate violates the
actual chain equation, while each map has its own valid identity. The negative
claim concerns that candidate, not every possible transformation.

## Representation choices and existing facilities

The implementation reuses Mathlib's bicategories, weak pseudofunctors, strong
transformations, modifications, adjoint equivalences, products and hom-category
equivalences. `PseudofunctorMapping`, `PseudofunctorInverse`,
`ContractibleBicategory` and `BicategoryIsoComma` expose the shared constructions.
Their uses in both descent and mapping proofs avoid duplicating the same
comparison calculus inside the example.

The existing internal strict two-family and cubical interfaces retain their
contracts. They do not supply the weak external mapping theory by coercion.
The new construction is external Lean mathematics; its sound internal model
interpretation remains under [#36](https://github.com/VladimirMarko/conaled/issues/36).

A chain-complex or Picard presentation would expose additive calculations, but
would restrict the arbitrary admitted fibers and weak maps. Mathlib's Dold–Kan
equivalence is useful for that additive direction; it is not an arbitrary
higher-stackification theorem. A simplicial-set route can express untruncated
mapping spaces, at the cost of the relevant localization and descent theory.
The bounded bicategorical route establishes the weak mapping interface first.

The delivered groupoid completion in
[`general-groupoid-completion.md`](general-groupoid-completion.md) has a
different site: sheaf parameters with singleton locally surjective covers.
Recovering it requires both a locally discrete embedding comparison at all
mapping levels and a proved change-of-site comparison preserving units.
[#732](https://github.com/VladimirMarko/conaled/issues/732) owns the existing
original-site groupoid bridge. Evaluation on represented sections alone is
insufficient. No commutation of truncation with completion is assumed.

## Remaining existence and comparison contracts

For a general small site, the finite-level target contract is a completion
`η : F → aF` with ordinary descent and a biequivalence
`Map(aF,T) → Map(F,T)` for every complete target, on weak maps,
transformations and modifications. Extending the present theorem needs genuine
overlap cocycles, common-refinement invariance, and compatible correction at
all admitted input dimensions. The contract must specify the diagram and
cover-index universes and any enlargement.

At the untruncated level, the desired ordinary sheafification has equivalences
of spaces `Map(aF,T) ≃ Map(F,T)` for ordinary sheaves. Hypercompletion has the
separate contract `Map(h(aF),H) ≃ Map(F,H)` for hypercomplete targets.
Dugger–Hollander–Isaksen, *Hypercovers and simplicial presheaves*, Theorem 6.2
and Appendix A, distinguish hypercover localization from Čech localization;
their small-site construction supplies the required dense set of hypercovers.
[Primary source](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/DHI.pdf).
A finite ordinary-descent test does not establish either general localization.

The remaining checklist under #721 is:

- Extend the normalized representation to general coherent diagrams, with a
  comparison preserving units and all mapping levels.
- Handle nontrivial overlaps, refinements and higher cocycles, then arbitrary
  small sites and the promised input/universe bounds.
- Prove the locally discrete groupoid specialization and the original-site
  comparison, including actual units and mapping categories.
- Construct and compare truncation operations where claimed.
- Establish untruncated ordinary sheafification with derived mapping spaces.
- Establish hypercompletion and hyperdescent separately, including their
  relation to finite truncation.
- Supply the internal source/model interpretation through #36.

These are remaining theorem contracts. The finite completion does not close
#721 or discharge the properness/Myers comparison under #724.
