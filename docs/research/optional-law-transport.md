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
requiring distribution inverse laws. For composition between lawful choices, `DistributionMap.of_laws`
derives preservation from structural preservation and uniqueness of inverses.
It uses only `distribute ∘ collect = id` in the source and
`collect ∘ distribute = id` in the target. It requires no reflection or
injectivity. Composed product/coproduct contracts can therefore be used directly
without proving a new equation for the composite distribution arrow.

This is a lawful-choice composition route. It is not a theorem composing two
arbitrary distribution preservation fields in the absence of inverse laws.
The law-transport theorem itself has no source inverse-law premise. The
composition example first transports code laws from ordinary functions, then
uses those established laws to obtain preservation into wrapped functions.
Its last transport application checks compatibility with the original source
relation; it is not an independent proof of the source laws.

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
  composition; distribution preservation uses inverse uniqueness.
- Identity preservation for the wrapped choices, the induced source relation,
  and the failure to reflect raw syntax equality.

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
`collect` is the existing canonical copairing of product branches; no new
primitive changes its meaning. `DistributionMap.of_laws` exposes its source
inverse premise and must not be used as evidence for establishing that premise.

At Felix revision `6f36d28097db7ea5f5df3263db3e8be08f74e490`,
[`MakeLawful.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
derives category and Cartesian laws under an interpretation-induced relation.
The local optional-family transport extends that mechanism to operations
already supported here. This is not a claim that the pinned Felix file
implements coproduct or distribution transport. The current closed-family
extension is recorded in the [parity report](felix-parity-implementation.md#closed-law-transport-37).
