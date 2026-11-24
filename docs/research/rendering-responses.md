# Compositional rendering responses

[#689](https://github.com/VladimirMarko/conaled/issues/689) tests the first
[rendering milestone](../rendering-direction.md) with one-way emission and
transmission. The reusable API is
[Response](../../Applications/Rendering/Response.lean); the checked clients are
[RenderingResponse](../../Examples/RenderingResponse.lean). This is a response
algebra and a set of exact observations, not an image-producing renderer.

## Algebra and interpretation

A response stores emission `e : V` and transmission `t : T`. Its meaning is
`L ↦ e + t • L`. Composition `front * back` stores
`(e_front + t_front • e_back, t_front * t_back)`: the back acts first on incoming
light, and the front acts on its result. `eval_mul` proves agreement for every
incoming value. `meaning` packages this as Mathlib's `MonoidHom` into
`Function.End V`, whose multiplication is function composition. The representation
itself is a `Monoid`, so standard identity and associativity laws apply.

Evaluation needs addition and a scalar action. The composition laws need only
`Monoid T`, `AddMonoid V` and `DistribMulAction T V`. They do not require a field,
commutative multiplication, additive inverses, coordinates, a metric, probability,
or differentiability. The three-channel client uses scalar rational transmission
acting on `Fin 3 → ℚ`, in addition to scalar-valued clients. The semantic map is
not claimed injective: a nonfaithful action can hide distinctions in transmission.

The algebra does not enforce optical validity. The scalar examples separately
state `Admissible`: emission is nonnegative and transmission lies in `[0,1]`.
They prove closure under composition and nonnegative output for nonnegative
incoming light. Both spatial layers and Boolean gates satisfy these conditions.
This constraint does not bound emission by one or establish energy conservation
for a full optical system. Its order structure is needed only by these physical
checks, not by the algebraic laws.

`transparent` consumes identity and composition; `opaque_front` proves that zero
transmission discards the entire back response and incoming value. An emitting
layer with transmission one still adds light. The order control gives `7/2` for
front `(2,1/2)` over back `(3,1/3)`, and `11/3` in the reverse order on black
background. Thus the implementation does not silently commute layers.

## Spatial queries and coordinate compatibility

A scene for this experiment is a function from a query space to responses.
`observe` takes that function, a query selected by an observer, and the incoming
light. `observe_mul` connects pointwise scene composition to `eval_mul`. The
common API imposes no Euclidean coordinate system or fixed dimension.

The selected clients use rational points `Fin n → ℚ` and the nonconstant field
`s(p) = ∑ i, p i ^ 2`. The front response is `(s(p),1/2)`, the back is
`(s(p)+1,1/3)`, and incoming light is zero. Applying the shared law gives
`3*s(p)/2 + 1/2`. Checked point observations include:

| Query | Observation |
| --- | --- |
| `(1,2)` | `8` |
| `(2,2)` | `25/2` |
| `(1,2,3)` | `43/2` |
| `(1,2,4)` | `32` |

These are point samples of layered response fields. They use spatial data, but
do not perform ray intersection, path integration, visibility sorting or
perspective projection. The third coordinate changes the observation rather
than being an unused parameter.

`reindex` is a monoid homomorphism for pulling scenes back along any query map.
For an equivalence `e`, `observe_reindex_mul` pulls each layer back along
`e.symm`, sends the observer's query through `e`, and proves equality of the
composed observation. The concrete `shift` adds one to every coordinate. The
moving 3D query `(1,2,t)` at `t=3` still gives `43/2` after transporting scenes
and observer. Moving the query alone gives `44`, a control that detects omission
of the scene pullback.

The general compatibility theorem covers bijective relabelings of the query
space with unchanged emission/transmission carriers. The example is an invertible
affine translation. This theorem does not transform directional data, frames,
measures or metrics, and it does not establish chart overlap laws, isotropy,
groupoid equivalence or Morita independence. Dimension changes and coordinate
changes are separate checked clients; neither supplies general orbifold geometry.

## Statistical dependence

The probability client uses existing `Applications.Probability.Table` operations.
`fair` assigns rational mass `1/2` to each Boolean. `shared` composes that draw
with deterministic copying. `independent` composes it with `appendFair`, which
retains the first bit and samples a fresh second bit from `fair`. Its entry theorem
proves the product of the two fair masses. Both joint tables have the same first
and second marginals, checked through deterministic projections and `Table.comp`.

Each bit selects a nonemitting layer with transmission zero or one. `transmitted`
evaluates the composed response on unit incoming light. Its indicator formula
uses `eval_mul`, and a separate theorem identifies the observation with the
represented product transmission. Its value is proved to lie in `[0,1]`.
`expected` integrates that observation using the existing table-to-kernel
interpretation. `Table.lintegral_kernel` reduces this nonnegative expectation to
the finite weighted sum, yielding `1/2` for the shared draw and `1/4` for fresh
independent draws. `dependence_matters` proves the observations differ despite
the marginal equalities.

This demonstrates why joint realization information must survive until after
composition. It does not establish a coherent random field across arbitrary
views, time or refinement, nor an executable random-bit sampler for this renderer.
No new probability-object interface was needed for these finite laws.

## Interface assessment and image client

Retain this construction as a small reusable layering model. The clients required
separate emission and transmission carriers, explicit layer order, a world/query
boundary, scene pullback together with observer transport, and joint random data
before observation. Standard monoids and homomorphisms supplied the laws; there
was no need for a rendering-specific preservation framework. Nothing here
requires adopting scalar layering as the final renderer's universal scene model.
Scattering back toward earlier layers and interreflection require richer response
information and different composition obligations.

The [orthographic image sequence](orthographic-rendering.md) now implements this
next client: two bounded parallel rectangles at depths z=1 and z=2, rational RGB
emission, black background and three translated cameras. It uses the shared
`eval_prod` folding consequence of `eval_mul`. Checked intersections and fixed
depth order justify its finite pixel computation; a separate clamp/quantization
contract connects the exact samples to deterministic PPM output. Its output
adapter has executable byte-level checks and explicit runtime assumptions.

This image slice has no identified dependency on general probability objects,
smooth associated bundles, Morita comparison, a general FRP runtime, or caching.
It is a Euclidean 3D execution milestone. A subsequent genuinely 3D orbifold
scene still needs a selected quotient/chart class, representative and frame
transport, isotropy-sensitive observations and its motion realization. Those
requirements remain with [#34](https://github.com/VladimirMarko/conaled/issues/34).
Certified reuse must likewise choose an observation error relation and a query
region before supplying cache bounds; no such bound follows from this algebra.
