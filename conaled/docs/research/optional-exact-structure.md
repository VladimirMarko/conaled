# Optional structure and exact recovery (#18)

`SquareKit.Optional` adds binary coproducts, left distribution, and closed
operations to the object-polymorphic category interface. Each package is
selected separately. Object and hom universes remain independent; neither
source types nor a particular semantic carrier occurs in these interfaces.

| Capability | Assumptions and scope | Public construction |
|---|---|---|
| General comma identity/composition | Common-target category laws and congruence, interpretation preservation; raw sources need no category laws | `Comma.ops` |
| General comma terminal/products | Common-target cartesian laws and strong terminal/product comparisons for both interpretations; raw construction still does not need source laws | `Comma.terminalOps`, `Comma.productOps` |
| Lawful comma category/products | Mathlib category instances and its own comma-limit preservation hypotheses | `CommaLawful`, `CommaLimits` |
| Binary coproduct interface | Chosen objects, injections and copair; congruence and beta/eta supplied separately | `CoproductOps`, `CoproductCongr`, `CoproductLaws` |
| Left distribution | Products and binary coproducts plus an inverse to the canonical `collect` map | `DistributionOps`, `DistributionLaws` |
| Closed interface | Products and chosen exponential/evaluation/curry; curry congruence and beta/eta/naturality supplied separately | `ClosedOps`, `ClosedCongr`, `ClosedLaws` |
| Exact Type coproducts/distribution | Identity/identity comma over types, arbitrary decoding functions | `Comma.Exact.coproducts`, `distribution` |
| Exact Type closed structure | The same Type specialization; represented functions retain implementation, specification, and compatibility | `Comma.Exact.closed`, `exponential_carrier` |
| General comma coproducts/closure | Not constructed here. Additional preservation/exponentiability hypotheses would be required; category and product hypotheses alone give no such claim | No generic closed instance |

Distribution is a family of arrows indexed only by objects, so it has no
arrow-argument congruence obligation. Its derived `collect` map uses product,
coproduct, and composition congruence already supplied by those packages.
There is no redundant congruence record for a nullary operation.

## Quotients and Mathlib

`HomQuotient.coproducts`, `distribution`, and `closed` descend the operations
under the corresponding congruence hypotheses. `coproductLaws`,
`distributionLaws`, and `closedLaws` prove their equality laws for arbitrary
quotient arrows. The `mk_inl`, `mk_inr`, `mk_copair`, `mk_distribute`,
`mk_evaluation`, `mk_curry`, and `mk_uncurry` theorems identify the quotient
operations on representatives. Existing `HomQuotient.mk_eq_iff` still states
that class equality is exactly the declared hom equivalence. Raw operations
remain available without forming a quotient.

`OptionalMathlib.coproducts` uses Mathlib's chosen binary coproducts, injections,
and universal property. `OptionalMathlib.products` chooses `b ⊗ a` for the
product of `a` and `b`. This reversed coordinate choice aligns our
rightmost-argument curry convention with Mathlib's tensor-left adjunction.
`OptionalMathlib.closed` consumes `CartesianMonoidalCategory` and
`MonoidalClosed`; its `uncurry_eq` identifies derived evaluation with the
adjunction inverse. Beta, eta, and naturality use Mathlib's corresponding
proofs. The adapter does not introduce a competing lawful closed-category
class. `OptionalMathlib.distribution` independently accepts Mathlib `IsIso`
for the canonical collect arrows and takes their inverse; it does not require
closed structure.

## Recovery and checked consumers

`CommaOptionalExact` supplies object comparisons for sums and exponentials
and arrow comparisons for both injections, copair, distribution, evaluation,
curry, and uncurry. These are equalities of complete squares, so both the
implementation and specification are preserved. The recovery theorems
`copair_left`, `copair_right`, `copair_eta`, `uncurry_curry`, and
`curry_uncurry` obtain the existing statements from the new law packages.
The dependency-free `Squares.lean` definitions and public theorem statements
are unchanged. Their existing proofs discharge the Type-specific law
obligations of the adapter.

`Examples.OptionalSquares` consumes the shared operations to curry addition
with an environment of 3 and evaluate at 4, obtaining 7. It checks that the
stored specification also yields 7, checks beta for the complete arrow, and
checks eta with a decoder that forgets a Boolean. Its sum example selects
false on the left and true on the right regardless of the forgotten input;
both tags are exercised. Distribution is checked on both tags and against its
canonical inverse. A Mathlib example uses `environment + 2 * argument` at
(3, 4), obtaining 11 through the shared beta law; swapping arguments would
instead give 10.

## Felix correspondence and boundaries

The reference is Felix `6f36d28097db7ea5f5df3263db3e8be08f74e490`, inspected
in `Raw.agda`, `Equiv.agda`, and `Laws.agda`. The split follows its raw
operations, chosen hom equivalence, and laws. `CoproductOps` covers the binary
part of `Raw.Cocartesian`; initial objects are outside this ticket's exact
operations. `DistributionOps` covers the existing left distribution; Felix
also exposes right distribution. The inverse equations match the left half
of `Laws.Distributive`. `ClosedOps` matches `Raw.CartesianClosed` and defines
uncurrying through evaluation and products. The beta/eta and congruence fields
express the exponential universal property, with the existing local
naturality obligation retained explicitly.

No specification-function erasure is claimed. No closed structure is imposed
on matrices, circuits, or general comma categories. Non-strict preservation of
these optional operations and full-source compiler naturality belong to #19;
this ticket makes no generic closed-law transport claim or claim to complete
Felix's unfinished `CartesianClosedH` transport.
