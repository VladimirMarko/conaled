# Full-source preservation (#19)

`STLCNaturality.naturality` interprets every constructor of the existing source
language in arbitrary object/hom universes. It proves that mapping compilation
agrees with compilation in the image model, modulo the target's chosen hom
equivalence. It needs category preservation, target congruence, and local
operation preservation. It neither assumes source category laws nor concludes
raw equality from semantic preservation.

## Optional comparisons

`OptionalMap` separates `CoproductMapLaws`, `DistributionMapLaws`, and
`ClosedMapLaws`. Category/cartesian clients do not acquire these requirements.
Comparisons are pairs of arrows; `ComparisonLaws` separately supplies their
inverse equations. The compiler theorem only needs operation coherence, while
calling a comparison an isomorphism also requires those inverse equations.

| Operation | Required comparison/coherence |
|---|---|
| Injection | Target injection followed by inverse sum comparison |
| Copair | Sum comparison followed by target copair |
| Curry | Inverse product comparison before the mapped body, target curry, inverse exponential comparison |
| Evaluation | Product comparison, exponential comparison on its first coordinate, target evaluation |
| Captured case distribution | Product comparison, sum comparison inside the environment product, target distribution, inverse comparisons on both resulting products and the outer sum |

`imageDistribution` displays the complete captured-environment conversion.
`STLCNaturality.image` retains carriers `F.obj (objects … a)`; it does not
identify these with target products, sums, or function objects definitionally.
`image_preserves` discharges the compiler's local preservation package from
these chosen comparison obligations and primitive compatibility.
`structured_naturality` applies the generic compiler theorem to that image.

`preserves_comp` composes local preservation using `RawMap.comp` and congruence
of the second interpretation. `naturality_comp` combines it with
`RawMap.comp_laws`. Neither proof performs another syntax induction. The
composite model can retain the two stages' explicit comparison operations;
there is no requirement to normalize them into a globally chosen closed
comparison or infer any closed laws from preservation alone.

## Compatibility and consumers

| Existing interface/result | Adapter or shared result |
|---|---|
| `CategoricalCompiler.Target` | `STLCCategory.ops`, `terminal`, `products`, `coproducts`, `distribution`, `closed`; `STLCNaturality.ofTarget` |
| Existing compilation | `compileVar_ofTarget`, `compile_ofTarget` |
| `CategoricalCompiler.Sound` | `soundMap`, `soundMap_laws`, `sound_preserves` |
| `CategoricalCompiler.compile_sound` statement | `STLCNaturality.compile_sound`, derived from `naturality` and `semantics_compile` |
| Existing exact source carriers | `STLCExact.inclusion`, `model`, `preserves`, `compile_comparison` |
| Exact specification and runtime correctness | `STLCExact.compile_spec`, `compile_commutes`, `compile_apply_commutes` |

`STLCExact.model` consumes the shared exact comma products, coproducts,
distribution, curry, and evaluation. Its terminal uses the existing compiler's
`Unit` carrier explicitly; the general exact terminal uses `PUnit`. This keeps
the existing source encoding and every foundation theorem statement intact.
`compile_comparison` is equality of complete comma arrows, preserving both
implementation and specification. Function values remain the existing
`FunctionRep`, with both functions stored as data.

`Examples.FullSourceNaturality.Lift` maps every function object to `ULift`.
A lifted product, sum, or function object is not definitionally the corresponding
construction on lifted objects. The example proves all four comparison inverse
laws, all operation coherence, and primitive increment compatibility. Its
all-term `naturality` theorem checks that these obligations suffice for the full
source language. The captured application uses a different argument from its
captured environment, and both captured sum tags are evaluated. The same model
is then interpreted into Mathlib's bundled function arrows; `composed_naturality`
uses the composition theorem and checks the resulting execution.

`Examples.FullSourceNaturality.Exact` checks captured lambdas and application
in the existing tagged-natural representation. `captured_lambda` quantifies
independently over the captured natural, argument natural, and both Boolean
tags. `left_branch` and `right_branch` quantify over distinct sum payload and
outer value. These proofs consume the generalized full-source theorem through
`STLCExact`, including its primitive contract and both square arrows.

## Local obligations and derived work

The generic model still needs chosen operations, and each representation still
supplies its primitive semantics. A non-strict interpretation supplies product,
sum, exponential and terminal comparisons, their inverse proofs when needed,
and the displayed local coherence equations. No claim is made that a category
functor preserves sums or exponentials automatically.

Derived work is the entire full-source preservation induction, preservation of
variables and captured environments, composition of local preservation, and
recovery of the legacy soundness theorem. `compile_ofTarget` and
`semantics_compile` establish the compatibility boundaries once; subsequent
interpretation composition uses `naturality_comp` rather than repeating those
inductions. Existing category/product/closed laws and all foundation and
relational statements remain unchanged. Higher-order relational client migration
is assigned to #21.

The Felix reference is `6f36d28097db7ea5f5df3263db3e8be08f74e490`.
`Raw.agda`, `Equiv.agda`, `Laws.agda`, and `Homomorphism.agda` were inspected.
The latter still marks `CartesianClosedH` as TODO. This implementation proves
scoped preservation for explicitly chosen curry/evaluation operations; it does
not complete generic closed-law transport, assert arbitrary comma closure, or
justify erasing represented specification functions. Those broader questions
remain outside this ticket.
