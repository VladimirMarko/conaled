# Raw categories and lawful hom quotients

Ticket [#9](https://github.com/VladimirMarko/conaled/issues/9) supplies the
category and cartesian part of P1. Its implementation base is
`b57f9f383a527bcd40bd201cd8354e1f8315185c`. Between the inspected foundation
`c17daf5a66b9812fdbc0cb37cd4e9c49b1949ce8` and this base, only planning and ticket
records changed; the Lean baseline is unchanged.

`SquareKit.CategoryOps` has independent object and hom universes. It contains
only homs, identity and composition. `HomEquiv` supplies hom setoids;
`CategoryCongr` and `CategoryLaws` supply separate proofs. `TerminalOps` and
`ProductOps` are independently selectable. Their laws and product congruence
are separate arguments. None of these interfaces mentions source types,
primitives, values, or functions as the required hom representation.

`HomQuotient.category` constructs a Mathlib category after receiving congruence
and laws modulo the chosen relation. `HomQuotient.mk_eq_iff` proves that class
equality is exactly that relation. The `mk_ident`, `mk_comp`, `mk_terminal`,
`mk_fst`, `mk_snd` and `mk_pair` lemmas give descent of all supplied operations.
`terminalLaws` and `productLaws` prove the quotient laws, including product eta.
The quotient leaves the raw representatives available and adds no runtime
normalization algorithm.

For equality-lawful inputs, `ofCategory` and `ofCategoryLaws` consume Mathlib's
`Category`. `LawfulQuotient.homEquiv` compares the raw hom-setoid quotient with
Mathlib's `CategoryTheory.Quotient` under an arbitrary Mathlib congruence. Its
inverse equations are checked, and `LawfulQuotient.comparison` proves identity
and composition preservation as a Mathlib functor. Mathlib's quotient requires
an input `Category`; it does not establish raw syntax's laws. Both constructions
identify precisely the supplied congruence in this comparison.

## Checked instances

`CodeCategory` adapts the existing `CategoricalCompiler.Code` and
`CategoricalCompiler.Equivalent`. Its laws use the existing evaluation proofs.
`association_not_equal` shows that two association trees are unequal as syntax;
`association_classes` proves equality of their classes for arbitrary composable
programs. `product_classes` exercises product eta under the same equivalence.

`MatrixCategory` uses actual matrices over an arbitrary commutative semiring,
with finite coordinate types carrying executable enumeration and decidable
equality. Object coordinates and scalars have independent universes. The
Mathlib category laws hold by matrix equality. Products use disjoint coordinate
sums and the terminal object has no coordinates. `association` and
`pair_recover` specialize the shared public law interfaces to these matrices.
No closure claim is made.

`FirstOrderCategory` adapts the existing first-order target operations without
adding requirements. `Examples.CategoryInstances.matrix_comp`,
`matrix_first_pair` and `matrix_second_pair` connect the existing additive
matrix target to the shared matrix operations and laws. `matrix_add_after_pair`
checks the composed matrix on arbitrary inputs: doubling each coordinate and
then adding yields `2 * x + 2 * y`. The existing `no_exponential` theorem and
all foundation declarations retain their original statements.

## Felix correspondence and scope

The inspected Felix revision is `6f36d28097db7ea5f5df3263db3e8be08f74e490`:

| Felix source | Lean counterpart |
|---|---|
| [Raw.Category](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda) | `CategoryOps`, with the same right-to-left composition order. |
| [Equiv.Equivalent](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda) | `HomEquiv`, using Lean `Setoid` and proposition-valued equivalence. |
| [Laws.Category](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda) | `CategoryCongr` and `CategoryLaws` separate congruence from identity/associativity. |
| `Raw.Cartesian`, `Laws.Cartesian` in those files | Independently selected terminal/products, pair congruence, terminal uniqueness and product beta/eta. |

Felix combines terminal and binary-product operations in `Cartesian`; this
interface permits either capability separately. Lean's beta/eta fields express
the chosen product universal property together with the category/congruence
laws. Optional sums/distribution and closed operations belong to #18 and #19.
Structure-preserving maps and transported laws belong to #10. Mathlib chosen
limit adapters, general comma structure and its product comparisons are not
claimed by this ticket. Full Felix ports and unfinished upstream work remain
tracked in #8. The dependency-free root modules are untouched.

## Statement review

Each category law quantifies over arbitrary composable homs. The law relation
is the explicitly supplied hom setoid; raw equality is asserted only for
Mathlib categories and matrices. Quotient composition consumes congruence,
while its category laws additionally consume `CategoryLaws`. The class-equality
biconditional uses the setoid's equivalence, so no larger generated relation is
silently substituted. The lawful-input comparison assumes Mathlib's congruence
and category laws explicitly.

Terminal uniqueness includes every hom into the selected terminal object.
Products quantify over arbitrary inputs and require both beta equations and
eta. Neither capability assumes the other or an exponential. Empty matrix
coordinates are permitted and supply a concrete terminal instance. The syntax
instance retains arbitrary primitive interpretations; it asserts equality
of evaluated outputs, not equality of primitive syntax. The matrix instance
uses equality of entries, including for the existing additive frontend.
These satisfiable instances exercise the shared obligations; no desired
conclusion is assumed as a primitive interpretation hypothesis.

Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679` with Lean 4.35.0.
Its `Mat` category uses `Matrix X Y R` for a hom from `X` to `Y` and shares the
index/scalar universe. This adapter follows the existing frontend's
`Matrix Y X R` column-vector convention, retains explicit decidable coordinates,
and separates the universes. It installs the standard Mathlib `Category`
interface and uses Mathlib's matrix identity/associativity theorems; it does not
introduce another hierarchy of equality-lawful categories.
