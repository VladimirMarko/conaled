# Local exceptional internal Hom

Issue [#695](https://github.com/VladimirMarko/conaled/issues/695) constructs
`[f_! A, B] ≅ f_* [A, f^! B]` for a fixed map. The
[local module](../../SquareKit/ExceptionalInternalHom.lean) takes independent
source and target object/hom universes, closed symmetric monoidal fibers, the
ordinary and exceptional adjunctions, and a selected exceptional projection
formula. It derives the isomorphism; the desired comparison is not an input.

## Construction and selected map

`ProjectionFormula.iso A` has components
`f_! (f* T ⊗ A) ≅ T ⊗ f_! A`. Its natural-isomorphism type supplies naturality
in T; its `naturality` field separately supplies naturality in A. No BC square,
purity assertion, or indexed six-operation package is needed.

Mathlib's `ihom.adjunction A` closes `A ⊗ -`. The local `rightAdj A` transports
that adjunction along `BraidedCategory.tensorLeftIsoTensorRight A`, so the
selected chain uses the test object on the left throughout:

```text
Hom(T, [f_! A,B])
  ≃ Hom(T ⊗ f_! A,B)
  ≃ Hom(f_! (f* T ⊗ A),B)
  ≃ Hom(f* T ⊗ A,f^! B)
  ≃ Hom(f* T,[A,f^! B])
  ≃ Hom(T,f_* [A,f^! B]).
```

The second step precomposes with the specified PF's forward map. `chain`
composes those equivalences. `iso` uses Mathlib's `conjugateIsoEquiv` on the
closed adjunction and `ordinary.comp ((rightAdj A).comp exceptional)`.
`hom_eq_chain` identifies composition with its forward component with the
chain for every test arrow. `inv_eq_chain` identifies its inverse with the
inverse chain. Both inverse laws are the fields of this constructed natural
isomorphism. `chain_naturality_test`, `naturality_coefficient`, and
`naturality_target` retain T naturality, A contravariance, and B covariance.
The A proof uses the additional PF naturality field.

This uses Mathlib's closed, adjunction, and conjugation helpers directly.
`Adjunction.compYonedaIso` requires matching hom universes and is unnecessary:
conjugation retains the independent universes here. Existing
[Kunneth](../../SquareKit/Kunneth.lean) ordinary projection/BC composites and
[adjoint-square transport](../../SquareKit/AdjointSquareTransport.lean) stay
unchanged. An ordinary K projection is not automatically this exceptional PF.

## Checked set-family use

[ExceptionalHomFamilies](../../SquareKit/ExceptionalHomFamilies.lean) uses
Mathlib's pointwise category `Bool → Type u`, with its product tensor and
function internal Hom. `Type u` represents families over Unit. Thus the
constant-family `pull` is reindexing along `Bool → Unit`. The chosen exceptional
adjunction is dependent sum ⊣ pull; the ordinary adjunction is pull ⊣ dependent
product. The PF maps `⟨b,(t,a)⟩` to `(t,⟨b,a⟩)`, retaining the actual index and
fiber value.

The generic map specializes to `h ↦ (fun b a => h ⟨b,a⟩)`.
`hom_apply` derives this computation from `hom_eq_chain`, rather than proving
an unrelated function equivalence. `inv_apply` recovers `k b a` on the pair
`⟨b,a⟩` through the generic inverse law.

The [public application](../../Examples/ExceptionalInternalHom.lean) uses
`A false = Unit` and `A true = Bool`. Its selected function takes values 17,
23, and 31 on the three possible dependent pairs. The generic comparison
recovers all three evaluations, including both Boolean fibers. It also
recovers the whole function by the inverse law. `selected_evaluation` consumes
the existing `IndexedSumFamilies.Selected` contract.

`no_product_exceptional` proves that the ordinary product cannot simply serve
as `f_!` with this pull as `f^!`. Take A false empty, A true singleton, and B
empty. There is a map from the product A to B, but no family map A to pull B.
An alleged product ⊣ pull adjunction would identify those hom sets. This is a
mathematical rejection for the selected functors. Merely omitting an
exceptional adjunction or PF from an ordinary provider is instead missing
interface data; it does not show that an extension cannot exist. The positive
sum example supplies such an extension. No geometric properness or K proper-law
claim follows from it.

## Transport and remaining ownership

[#573](https://github.com/VladimirMarko/conaled/issues/573) retains the transport
and primary-source motivic study. Transporting this H construction needs
compatible squares for both adjunctions, source/target tensor and closed
comparisons compatible with evaluation and currying, and compatibility with
the selected exceptional PF and braidings. These equations must carry every
step of the displayed chain. An invertible closed comparison needs its own
preservation hypothesis or a proof in the selected model; strong monoidality
alone does not supply it. Existing adjoint-square pasting is reusable but does
not discharge these additional equations.

This local theorem completes neither #573 nor an indexed six-operation
framework. An indexed wrapper or generic route builder still needs a consumer.
The ordinary K and native clients acquire no exceptional prerequisites.

## Validation and failed attempts

The generic construction, all three variance equations, both family-map
computations, the selected evaluations and the rejection proof compile at the
default resource settings. They are included in `SquareApplications` for the
integrated build and proof audit.

Early attempts failed on implicit arguments to `homFromEquiv`, the namespace
of closed precomposition, matching composite-functor objects in rewrite rules,
and the distinction between Type-category morphisms and bare functions.
Explicit arguments, existing naturality lemmas, and `.hom` evaluation resolved
these encoding failures. No failed attempt established a mathematical
obstruction or required a larger resource limit. The rejection theorem above
is separate mathematical evidence.
