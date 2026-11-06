# Category maps and law transport

Ticket #10, under milestone #15, adds `SquareKit.CategoryMap` and
`SquareKit.CartesianMap`. These modules have no source syntax or primitive
parameter. Object and hom universes are independent for each model.

`RawMap` contains an object map and a hom map. `MapLaws` separately states
congruence and identity/composition preservation. `RawMap.comp_laws` composes
those proofs. `RawMap.quotientFunctor` descends a map to the hom quotients from
#9; `toFunctor` and `ofFunctor` connect equality-lawful models to Mathlib.
`FunctionCategory.toTypes` connects ordinary functions to Mathlib's bundled
Type arrows, and its category laws are transported from that lawful instance.

The law-transport theorems require target congruence and laws. They conclude
laws under the source's chosen relation only when the semantic map reflects
that relation. `RawMap.induced` and `induced_reflects` provide the standard
case: source arrows are equivalent exactly when their images are equivalent.
`inducedLaws` then needs only local identity/composition preservation.
None of these theorems turns semantic equality into equality of syntax trees.
`CodeCategory.association_not_equal` remains a checked counterexample to that
stronger conclusion.

`CartesianMapQuotient` descends comparisons and their preservation equations to
hom classes. `Comparison.toIso` and `HomQuotient.comparisonIso` expose genuine
Mathlib isomorphisms. `binaryFanIsLimit` and `terminalIsTerminal` turn the chosen
raw universal properties into Mathlib limits. `HomQuotient.preservesBinaryProduct`
and `preservesTerminal` prove actual `PreservesLimit` instances for the quotient
functor, including non-strict product objects. The Code evaluation specializations
in `Examples.CategoryMaps` exercise both adapters. Terminal preservation needs
the terminal comparison isomorphism; product preservation also uses projection
compatibility. No unproved limit-preservation assumption is introduced.

## Non-strict products

A `Comparison` stores arrows in both directions. `ComparisonLaws` states the
inverse equations modulo the target equivalence. A product comparison goes
from the image of a source product to the product of the two images; a terminal
comparison goes from the image of the source terminal object to the target
terminal object. No equality between those objects is required.

`ProductMapLaws` says that mapped projections are target projections after the
forward comparison, and that a mapped pair is a target pair followed by the
inverse comparison. `TerminalMapLaws` gives the analogous equation for terminal
arrows. Identity/composition of these maps reuse the category map's preservation
proofs. `Comparison.map_laws` and `comp_laws` prove the inverse equations for
composed comparisons.

`ProductMap.transportLaws` derives beta and eta using both inverse equations.
`transportCongr` needs no inverse equations. Terminal uniqueness needs only the
relevant inverse equation, target category/terminal laws, and reflection;
it does not need source category laws. Operations, equivalence, congruence,
and laws remain separately selectable.

## Checked uses and caller work

`Examples.CategoryMaps` checks the induced relation, composition of Code
evaluation with the Mathlib Type adapter, and evaluation on hom classes for
arbitrary arrows. `CodeCategory` uses identity comparisons for products;
terminal comparison changes the foundation's `Unit` to universe-polymorphic
`PUnit`.

| Existing declaration | Shared result now used | Local obligation retained |
|---|---|---|
| `CodeCategory.congruence` | `RawMap.transportCongr` | Evaluation congruence and operation preservation |
| `CodeCategory.laws` | `RawMap.transportLaws` | Evaluation reflects `Equivalent` |
| `CodeCategory.terminalLaws` | `TerminalMap.transportLaws` | Terminal comparison and preservation |
| `CodeCategory.productCongr` | `ProductMap.transportCongr` | Pair preservation |
| `CodeCategory.productLaws` | `ProductMap.transportLaws` | Projection/pair preservation and comparison inverses |

The five declarations retain their public statements. The added local adapters
are `evaluation`, `evaluationLaws`, `evaluationReflects`, `terminalComparison`,
`terminalComparisonLaws`, `evaluationTerminal`, `productComparison`,
`productComparisonLaws`, and `evaluationProducts`. Their proofs concern the
chosen evaluation and comparisons; category and cartesian algebra is supplied
once in the shared modules. The dependency-free root `Compiler.lean` stays
unchanged, including its public `category_assoc`, `product_beta`, and
`product_eta` statements.

`Applications/Linear/Maps.lean` (`MatrixCompiler.Maps`) uses actual matrix multiplication and `mulVec` over a commutative
semiring. Its intermediate coordinate functions expose the non-strict
comparison between functions on sum-indexed coordinates and pairs of coordinate
functions. A second interpretation uses the existing `MatrixCompiler.encode`
and `decode` inverse laws to reach nested values. Composition reuses shared map
and product-preservation proofs; it does not repeat syntax induction or assume
that matrices support exponentials.

## Felix correspondence and scope

The inspected Felix revision is `6f36d28097db7ea5f5df3263db3e8be08f74e490`.
`Homomorphism.agda` supplies `CategoryH`, `ProductsH`, `StrongProductsH`, and
`CartesianH`. They correspond here to `MapLaws`, comparison data, inverse
comparison equations, and terminal/product preservation. Its derived
`F-exl′`/`F-exr′` equations are the chosen projection-preservation form here.
`MakeLawful.agda`'s `LawfulCategoryᶠ` requires a category homomorphism and lawful
target; `LawfulCartesianᶠ` additionally requires strong product comparisons and
cartesian preservation. The Lean transport theorems expose those obligations
and also allow an explicitly reflected source relation.

Generic closed-law transport was outside the original #10 scope, matching the
explicit TODO in the pinned `MakeLawful.agda`. The #37 implementation now supplies
`ClosedMap.transportLaws` and checked raw-code and nonidentity-comparison clients;
see the [current parity record](felix-parity-implementation.md#closed-law-transport-37).
The #333 extension adds [coproduct and distribution transport](optional-law-transport.md).
These extensions do not claim that arbitrary comma categories have exponentials
or that many-valued analyses are exact decoders.
