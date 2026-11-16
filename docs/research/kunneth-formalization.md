# Canonical proper Künneth maps and transport

Implementation of [#570](https://github.com/VladimirMarko/conaled/issues/570),
following the paper contracts (K), (E), (C), and (T) in
[six-functor-reusable-argument.md](six-functor-reusable-argument.md).

The library constructs the projection/base-change composite, proves its counit
characterization, and proves invertibility from the specified canonical
comparison laws. It transports this map and its inverse between two explicit
indexed predicate models. These are ordinary categorical models; the motivic
realizations and higher coherence remain with
[#555](https://github.com/VladimirMarko/conaled/issues/555).

## Public construction

[`Kunneth`](../../SquareKit/Kunneth.lean) uses native Mathlib categories,
monoidal functors, adjunctions and mates. `projection` is the transpose of the
cotensorator followed by a counit tensor identity. `baseChange` is the transpose
of the supplied square followed by the other counit; `baseChange_eq_mate`
identifies it with Mathlib's mate. Neither definition assumes invertibility.

`map` is the three-step PF/BC/PF composite with iterated pushforward as target.
`projectionRight_eq` identifies its last step with the symmetries and usual
projection formula in (K). `counit_characterization` proves (E) for this
independently defined composite, rather than assuming (E) as an extra law.
`iso` requires exactly the two PF components and the BC component to be
invertible. The calculation works with oplax monoidal functors; the symmetric
indexed interface supplies the stronger structure used in the paper.

[`KunnethIndexed`](../../SquareKit/KunnethIndexed.lean) separates the indexed
operations from their proper-map laws. Its `Indexed` provider stores a native
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` pseudofunctor, symmetric monoidal fibers, braided
pullback functors and chosen right adjoints. `Coherent` requires monoidal
identity/composition comparisons. The native pseudofunctor already supplies
associativity and unitor coherence. `Proper` adds admissibility closed under
identity, composition and actual pullback, PF for all coefficients on admissible
maps, and BC when the appropriate leg is admissible.

`square` derives the exchange isomorphism from the specified pullback
compositors and the base square's commutativity. `pushComp` uses uniqueness of
right adjoints; callers cannot replace it with an unrelated isomorphism.
`kunnethIso` uses properness of both original maps and derives properness of the
pulled-back map. `kunneth_counit` retains (E) after conversion to the chosen
pushforward along the composite.

## Transport

[`KunnethTransport`](../../SquareKit/KunnethTransport.lean) proves transport of
a tensor transpose through an adjoint square. Its requirements are the tensor
compatibility of the square and compatibility of the two component evaluation
maps. `tensorCompatible_of_monoidal` derives the former from native monoidality.
`tensorTranspose_transport` invokes the existing
`AdjointSquareTransport.curry`; it does not introduce another mates engine.
`map_eq_tensorTranspose` connects the independently constructed Künneth map to
this shared theorem. `tensorTranspose_transport_conjugate` gives (T) with
specified endpoint isomorphisms, and `inverse_transport` transports the inverse.

This local transport theorem accepts the exact component compatibility equations
consumed by the argument. It does not claim that arbitrary strong monoidal
functors preserve all right adjoints, or provide a general pseudonatural
transformation builder. A model route must establish those equations, including
the square/composite comparison in the second evaluation map. The implemented
route supplies actual natural transformations, their mate identification,
counit compatibility and composition compatibility.

## Models and discriminating observations

[`KunnethPredicates`](../../SquareKit/KunnethPredicates.lean) constructs, for a
color type `I`, the fiber `D(X) = Set (X × I)` as a poset category. Tensor is
intersection, pullback is preimage, and pushforward universally quantifies over
each fiber of a base function. The base category is `Type`; admissible maps are
surjections. Nonempty fibers prove PF, and the actual pullback universal
property proves BC. These laws are constructed, not postulated.

The two examples use `I = Unit` and `I = Bool`. The route duplicates one color
into two by precomposition. It has specified pullback and pushforward natural
isomorphisms; `pushRoute_eq_mate` and `route_counit` verify (C).
`map_transport` applies the shared tensor-transpose theorem.
`output_composition` then converts iterated pushforward endpoints, giving
`indexed_transport` for the chosen indexed Künneth maps.

[`Examples.Kunneth`](../../Examples/Kunneth.lean) checks:

- A noninjective surjection `Bool × Bool → Bool` and its actual pullback.
  The first coefficient family varies within a fiber. Independently calculated
  pushforward values identify the source Künneth output with the true base point.
- A separate target instance with unequal color components. Its output is
  precisely `color = false ∨ base = true`. This coefficient object is outside
  the duplication route's image.
- The specified source isomorphism and its inverse transport to the canonical
  target maps, retaining the external tensor and chosen-adjoint endpoint maps.
- The empty-to-singleton map fails PF: the reverse map would send a true
  proposition into false. Adjunctions and genuine base-change machinery do not
  supply the missing admissibility hypothesis.
- A non-thin Type calculation retains both selected coefficients and a chosen
  true tag. The canonical map sends `(a,b)` to `(a,(b,true))` and misses a false
  tag. This separates actual maps that the thin predicate models cannot test.
- Existing native slice projections and the selected dependent-function
  evaluation survive through the same lower comparison/mates layer without PF
  or exceptional-operation requirements.

The predicate models discriminate dependent objects, admissibility and
invertibility, but their hom sets are subsingletons. Their structural comparison
equalities therefore use thinness. The generic K/E and transport proofs do not
use thinness; the Type and native-slice cases retain non-thin observations.
These examples do not construct derived sheaves or motivic categories.

## Design decision and author obligations

Before implementation, three independent design assessments examined contract
and foundations, implementation and use, and alternatives and generality at
baseline `716b33040e252dff0996db99ecf4e8ac5124cfda`. All recommended a native local
calculation plus an implemented indexed provider. The implementation uses the
existing pseudofunctor instead of duplicating its coherence laws. The assessments
also identified the failure of unrestricted Type-family PF and the limited
ability of thin models to test chosen maps; the retained controls address those
risks. Finite module families are a useful future non-thin indexed realization,
not an implemented model in this task.

Direct clients supply native functors, adjunctions and comparison maps and can
use the local construction without declaring a whole indexed model. An indexed
model builder additionally installs reindexing coherence and proves the
admissibility, PF and BC laws. A routine author then supplies the cartesian
square, two properness witnesses and coefficient objects. A route builder proves
preservation and endpoint compatibility once; a transport user supplies the
selected coefficients. Existing slice clients keep their original native APIs.

The [prepared author-trial protocol](kunneth-author-trial.md) separates model
construction from routine author work. No independent author trial has run,
and no productivity improvement is claimed. #235/#117 own execution and the
resulting author evidence; #555 retains the broader mathematical programme.

## Validation and statement review

The checked specializations exercise public definitions and theorems. Statement
inspection covers the actual K/E map, the variance and coefficient quantifiers
of PF/BC, properness under pullback, chosen-adjoint conversion, structural
transport premises, and inverse direction. The general transport theorem's
comparison equations are assumptions about component evaluation maps, not the
conclusion (T). The route constructs these comparisons independently of either
Künneth map.

Acceptance requires the captured candidate's integrated build, exhaustive proof
audit, and independent Standards and Spec reviews. Their exact receipts and
reviewed commits belong to the implementation review record, rather than a
self-referential source revision here. No compiler, dependency, audit policy or
resource limit is changed.
