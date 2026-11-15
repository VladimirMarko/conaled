# Coproduct and distribution law transport

Issue [#333](https://github.com/VladimirMarko/conaled/issues/333) extends the
existing category/product/closed transport interface to sums and distribution.
Operations, semantic equivalence, preservation, and laws remain separate.

## What the transport proves

[`CoproductMap`](../../SquareKit/CoproductMap.lean) derives congruence and the
left, right, and eta laws from preservation of the chosen injections and
copairing. The target supplies category and coproduct laws. The comparison's
`hom_inv` equation is used for the beta laws; `inv_hom` is used for eta.
Source reflection is explicit. No product or closed structure is required by
these theorems.

[`DistributionMap`](../../SquareKit/DistributionMap.lean) assembles its domain
comparison from a product comparison and a sum comparison under the second
factor. Its codomain comparison is a sum of product comparisons. The helper
[`OptionalComparison`](../../SquareKit/OptionalComparison.lean) proves that
these induced comparisons have inverses using target category, product, and
coproduct laws.

`collect_preserved` derives preservation of the canonical `collect` arrow from
`MapLaws`, `ProductMapLaws`, and `CoproductMapLaws`. It requires neither
comparison inverse equations nor distribution laws. In particular, callers do
not supply preservation of `collect` as an additional field.
`transportLaws` then reflects the inverse equations between `collect` and the
chosen distribution arrow. It requires comparison inverses, target distribution
laws, and the existing `DistributionMapLaws` field, but no source distribution
law. `RawMap.transportComparisonLaws` contains the shared inverse-law argument.

The source relation can be induced by interpretation, with no injectivity
requirement, or chosen independently with a reflection proof. The checked raw
code example supplies both forms. Evaluation does not reflect raw constructor
equality: `.comp .ident .ident` and `.ident` have equal evaluations and distinct
constructors. The negative control checks this failure directly.

## Composition and lawful inverse choices

Coproduct comparisons, their inverse proofs, and preservation contracts compose
through `CoproductMap.comp`, `comp_inverse`, and `comp_laws`. Identity
preservation is `id_laws`. These reuse `RawMap` and `Comparison` composition.

`DistributionMap.id_laws` preserves arbitrary distribution choices without
requiring distribution inverse laws. `DistributionMap.comp_laws` composes two
existing distribution-preservation contracts using the existing product and
coproduct comparison composition. It needs category laws in the final
target, the second interpretation's map and structural preservation
laws, final product/coproduct laws, and only the `hom_inv` equations of the
second comparison families. It requires neither source distribution laws nor
reflection, and it does not require distribution laws in either target.

The proof derives preservation of the product map on the second factor and the
coproduct map from their constituent operation fields. Their naturality gives
the forward domain and inverse codomain comparison equations needed to compose
the two distribution fields. First-stage comparison inverses and first-stage
product/coproduct preservation fields are not extra premises of this theorem;
composing their own contracts remains a separate use of `comp_laws` in those
namespaces.

`DistributionMap.of_laws` supplies a separate route for lawful choices. It
derives preservation from structural preservation and uniqueness of inverses,
using only `distribute ∘ collect = id` in the source and
`collect ∘ distribute = id` in the target. It requires no reflection or
injectivity. This route is useful when the chosen inverse laws are already
available; it is not needed by the sequential preservation example.

The sequential example first composes evaluation and the wrapped interpretation's
preservation contracts. Its forward preservation proof remains valid when the
source relation is raw constructor equality. The same checked example shows
that distribution inverse laws fail for this source relation: a composite code
constructor is not an identity constructor. This rules out relying on source
inverse laws to obtain the forward contract. Backward law transport uses the
separately chosen semantic relation and its reflection proof.

## Checked clients and caller work

[`CodeCategory`](../../SquareKit/CodeCategory.lean) now exposes raw coproduct and
distribution operations and their law packages under its existing pointwise
semantic equivalence. The new adapter supplies one identity-arrow sum comparison
family with both inverse proofs, three local coproduct preservation equations,
and one distribution preservation equation. The existing evaluation map,
reflection, and product adapter are reused. Shared transport supplies
coproduct congruence, three coproduct laws, and both distribution inverse laws.
This extends the available law packages; it does not claim fewer total proof
lines than direct proofs of these function equations.

[`Examples.OptionalTransport`](../../Examples/OptionalTransport.lean) checks:

- Coproduct eta for arbitrary raw code arrows and for arbitrary arrows out of a
  wrapped sum.
- Distribution and recovery of a selected right branch with products represented
  by `Box (a × b)` and sums by `Box (Sum a b)`.
- Raw code evaluation followed by a second interpretation into those wrapped
  operations. Product and coproduct preservation and inverse proofs use shared
  composition; distribution preservation composes the two existing contracts.
- Identity preservation for the wrapped choices, the induced source relation,
  the failure to reflect raw syntax equality, and forward preservation with raw
  equality despite the failure of source distribution inverse laws.

The exact optional client in
[`CommaOptionalExact`](../../SquareKit/CommaOptionalExact.lean) retains its direct
proofs. Its coproduct laws are three single applications of existing square
laws. Its distribution laws are two componentwise function-extensionality
proofs with sum case splits. Replacing them with transport would need a target
record retaining both arrow components, a raw map, reflection for both
components, product and coproduct comparisons, their inverse equations, and
seven local operation preservation equations (three product, three coproduct,
one distribution). A projection to just one component cannot reflect exact
arrow equality. That adapter would add obligations to this client; the five
existing law proofs and their exact recovery lemmas remain in place.

No strict-comparison convenience wrapper was added: the code adapter already
uses literal identity arrows, and no migrated caller repeats a larger setup
that such a wrapper would remove. The general non-strict interface remains the
one exercised by the wrapped example. Root `Compiler.lean` stays dependency
light; no blanket migration of matrix, comma, or compiler proofs is claimed.

## Statement review and scope

The new laws are relative to the declared hom relation, not Lean equality of
raw syntax. All arrow theorems quantify over arbitrary arrows of the stated
hom types. Reflection is an assumption of backward law transport and is not
inferred from preservation. The nonidentity comparisons are actual functions
between different carrier types, with both inverse equations checked.
`comp_laws` consumes both input distribution fields and assumes no source
or intermediate category law, or any distribution law. The raw-equality case establishes that its
forward-preservation conclusion is useful even when source inverse laws are
false. `collect` is the existing canonical copairing of product branches; no new
primitive changes its meaning. `DistributionMap.of_laws` exposes its source
inverse premise and must not be used as evidence for establishing that premise.

At Felix revision `6f36d28097db7ea5f5df3263db3e8be08f74e490`,
[`MakeLawful.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
derives category and Cartesian laws under an interpretation-induced relation.
The local optional-family transport extends that mechanism to operations
already supported here. This is not a claim that the pinned Felix file
implements coproduct or distribution transport. The current closed-family
extension is recorded in the [parity report](felix-parity-implementation.md#closed-law-transport-37).
