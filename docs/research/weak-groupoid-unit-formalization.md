# Constructed weak groupoid-unit eliminators

Implementation of [#448](https://github.com/VladimirMarko/conaled/issues/448),
following the [accepted paper derivation](local-universes-weak-groupoid-unit.md).
Both routes are constructed in
[WeakUnit.lean](../../Applications/LocalUniverses/WeakUnit.lean), and their exact
agreement is proved. [WeakGroupoidUnit.lean](../../Examples/WeakGroupoidUnit.lean)
checks the arrow-level counterexamples and consumes the universal laws.

The independent [contract](weak-groupoid-unit-contract.md) was committed before
proof development. The implementation incorporates accepted #466/#469 through
`d2dfd41d6fc9b08ea8565a804fa58ca8cc3491ca`; the frozen contract retains its
original preparation base. No existing comparison interface changes.

## Inputs and result

For arbitrary groupoids E, V and Γ, the input is a functor p:E→V, actual
normalized lifts, a motive c:Γ×I→V, a branch d:Γ→E and the equality
`d ⋙ p = constructor Γ ⋙ c`. I is Mathlib's codiscrete Bool groupoid.
Lift targets and isomorphisms are data. Their projection equations and
identity normalization are checked fields. There is no composition law for
lifts, and no extraction of such data from mere isofibration existence.

The direct functor uses the chosen lift at true and the identity at false.
Writing the false case explicitly retains the branch object exactly, including
when the supplied branch equation requires equality transport. This avoids a
choice for the constructor; it does not add a splitness assumption. The arrow
formula conjugates d's arrow by the endpoint lifts. Cancellation proves its
functor laws, projection, beta and substitution by arbitrary functors, including
composite substitution. All conclusions compare whole functors.

The parameter object stores `(a:I⥤V,e:E,p(e)=a(false))`. Its arrows are pairs
of a natural transformation and an E-arrow with the transported equality over
false. The inverse-arrow proof constructs a groupoid on this strict object.
An arbitrary comparison isomorphism is never substituted for object equality.
`functorGroupoid` supplies the componentwise groupoid structure on `[I,V]`.

Mathlib currying and the branch projection provide `representation`, an
actual equivalence between native motive/branch data and functors Γ→Parameter.
Both inverses and naming naturality are proved. `generic` applies the direct
construction to evaluation and the generic branch. `parameterEliminator`
instantiates that constructed filler; its own beta, projection and substitution
proofs use generic equations and naming naturality. `instantiated_agreement`
identifies it with the direct formula for the same lifts.

## Statement review

| Claims | Intended content and checks |
|---|---|
| `constructor`, `conjugate`, `Lift`, `NormalizedLifts` | Actual functors and selected targets, with map laws and image equations. No stability field or split-composition field. |
| `branchEq`, `branch_map`, `outgoing`, `selected`, `directObj`, `directIso`, zero lemmas | Exact branch equality supplies transports. False uses identity; true uses the supplied lift. Both object and arrow branch equations are retained. |
| `directOver`, `leg_natural`, `directIso_image`, `direct_projection`, `direct_beta` | Projection transport cancels along every arrow, rather than checking only objects. Beta is equality of functors. |
| `constructor_natural`, `reindexBranch`, outgoing/selected substitution, `direct_substitution`, `direct_composite_substitution` | Arbitrary functors between arbitrary groupoids; fixed p and lifts. Reindexing carries the native branch equation. Whole arrow maps participate in extensionality. |
| `functorGroupoid`, `Parameter.Hom`, category/groupoid instances and projection lemmas | Invertible natural-transformation components; strict object equality; commuting arrow pair. Composition and inverses preserve the equation. |
| `evaluation`, `genericBranch`, `functor_ext`, `name`, naming equations, `curry_substitution`, `name_substitution` | Currying on whole functors with the E component preserved. Parameter extensionality requires both projections. |
| `Family`, `represent`, `realize`, both inverse theorems, `representation` | Native input family includes its actual equation. Both representation inverses are equalities, not object bijections alone. |
| `generic`, its projection/beta, `instantiated_agreement` | Generic filler is constructed from the same supplied lifts. Agreement does not quantify over unrelated generic choices. |
| `parameterEliminator`, parameter beta/projection/single/composite substitution | Independent parameter-route laws use naming naturality and the fixed generic construction. No final eliminator is reselected during substitution. |
| C₂ `filler`, `same_objects`, `distinct_forward`, `distinct_fillers`, `filler_over`, `same_branch` | Two genuine section functors have the same branch and objects but unequal arrow maps. |
| `swapFillers`, `fixes_whole_branch`, `swaps`, `involution`, `swap_over` | Actual involutive motive automorphism over I, fixing the whole zero fiber and swapping the fillers. |
| `nonsplit`, label equations, `fails_composition` | Actual normalized lifting data, not just a label table. Composing its forward/backward lifts disagrees with its identity lift. |
| `repaired`, native branch, repaired beta/projection/roundtrip, labels and retained branch arrow | Universal construction repairs both nonidentity labels to true, composes correctly, and retains the nontrivial C₂ branch arrow. |
| `erase`, `repeated_substitution`, `native_generic_agreement` | A non-faithful substitution discards the branch loop; two substitutions consume the universal theorem. The native data also consume exact generic/direct agreement. |

The counterexamples reject uniqueness, invariance of the displayed choices
under the swapping automorphism, and treating normalized choices as a functor.
No exhaustive classification of all section functors is claimed. They do not refute the constructed
stable choices. The finite cases do not serve as proofs of the arbitrary
groupoid theorems; those are in the library module.

## Source and reuse boundary

The local source archive for Lumsdaine–Warren
[arXiv:1411.1736v2](https://arxiv.org/abs/1411.1736v2) was rechecked against the
accepted SHA-256
`545175cf105359f0fc24201570fa892de7894ab16ecd7a6b520b98e94d03f9a0`.
Its TeX unit definition (§3.4.4) requests elimination and beta, with no
uniqueness; strict stability concerns the selected operations. Definition
3.1.3 and Example 4.2.5(1) retain the LF/exponentiability hypotheses of the
ambient theorem. The new Lean code proves the explicit construction on supplied
lifting data. It does not formalize that ambient model theorem, all LF,
Grothendieck-universe closure, isofibration choice, or a full comprehension
category.

The implementation reuses Mathlib's codiscrete category, groupoids, product
categories, natural isomorphisms, functor extensionality and currying. Existing
SquareKit.LocalUniverses remains the Type-family baseline; it cannot supply
the nontrivial groupoid arrows. Existing comparison/descent modules handle
different boundaries and are not duplicated or replaced here.

For this constructor, the direct route needs endpoint lifts and conjugation.
The generic route additionally needs the strict parameter groupoid, evaluation,
representation and naturality. Both share the fixed-presentation convention
that substitution precomposes names. This comparison supports using the direct
formula here while retaining the generic route as a checked alternative.
It makes no author-productivity inference from line counts and no project-wide
foundation or framework decision.

## Validation

Focused builds cover both new modules with `autoImplicit false` and
`warningAsError true`. `SquareApplications.lean` imports the example module,
which imports the theory. The enclosing orchestration performs the final
full candidate build/proof audit and independent Standards and Spec reviews;
those receipts are separate from this author statement review. There are no
new axioms, admitted proofs, dependency changes or tooling changes in this
implementation.
