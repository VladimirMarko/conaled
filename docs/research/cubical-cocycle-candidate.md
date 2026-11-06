# A two-cocycle candidate for the cubical higher witness

This note assesses a construction for the remaining higher-object obligation in
#321. The presheaf now has a constructed lawful uniform filling operation. Its
identification with `K(ℤ,2)` and the required coherent observer remain unproved. The full cubical contextual model and the unchanged
frozen-client interpretation are separate, checked results.

## What the sources establish

Brown and Higgins prove an equivalence between chain complexes and cubical
abelian groups **with connections**, using their earlier crossed-complex and
cubical-groupoid equivalences. Their three-page proof does not construct a
selected filler natural under all substitutions in our De Morgan Lawvere
category. We must supply that additional argument rather than importing an
ordinary Kan claim as our `Filling.Lawful` instance.
[Brown–Higgins, *Cubical abelian groups with connections are equivalent to chain complexes*](https://arxiv.org/pdf/math/0212157), theorem and final paragraph.

Buchholtz and Morehouse distinguish the De Morgan, Kleene, and Boolean cube
categories. Their Corollary 2 establishes that the cartesian De Morgan cube
category is a strict test category. This supports searching for a genuine
higher homotopy object on this site, but does not specify our chosen uniform
composition operations. Their discussion of left Kan extension and its right
adjoint also gives the general presheaf construction from a functor assigning
shapes to cubes.
[Buchholtz–Morehouse, *Varieties of Cubical Sets*](https://arxiv.org/pdf/1701.08189), §1.2, §2.4, Corollary 2.

The distinction between classical test-model fibrations and the operations used
by a cubical type-theory model is substantive. Angiuli, Brunerie, Coquand, Harper,
Hou, and Licata explicitly caution that the two fibration classes need not
coincide; they also explain why diagonal naturality invalidates some earlier
Kan constructions.
[*Syntax and models of Cartesian cubical type theory*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/01B9E98DF997F0861E4BA13A34B72A7D/S0960129521000347a.pdf/syntax_and_models_of_cartesian_cubical_type_theory.pdf), discussion of Cartesian and De Morgan models.

May's simplicial treatment provides canonical simplicial abelian models of
Eilenberg–Mac Lane spaces. This is background for the cocycle proposal, not a
proof that the proposed cubical presheaf has our required selected operations.
[May, *Simplicial Objects in Algebraic Topology*](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/May-simp-ocr.pdf), introduction and Chapter V.

## The proposed object

Let `C` be the actual formal De Morgan cube category. Set

```
X(n) = integer-valued 2-cocycles on the nerve of C/n.
```

A cube substitution acts by postcomposition of slice objects, followed by
pullback of cochains. This retains the formal substitution itself, including
connections, reversal, and repeated variables. It does not replace dimensions
with their Boolean vertex values. We use unnormalized cochains; identifying
the homotopy type requires accounting for this choice.

The following is our proposed construction, not a theorem attributed to the
sources above. A section over a presheaf `Δ` should correspond to a cochain on
its category of generalized elements (with the slice-compatible orientation).
For `Δ × I`, adjoining a fresh coordinate gives a functor `F` and a span of
natural transformations

```
identity → F ← cap-at-zero.
```

The graph of the current interval coordinate supplies the first transformation;
the zero endpoint supplies the second. The ordinary categorical prism then
gives a cochain homotopy `H` with

```
δ H(z) = z − cap*(z)       when δz = 0.
```

Subtracting the pullback of `H(z)` along the cap makes this primitive vanish at
the cap. These operations must preserve the subcategory cut out by a face
sieve independent of the filling coordinate.

Given a closed partial tube `u` and a compatible cap `a`, apply this relative
primitive to `u − a`. Extend the resulting degree-one cochain by zero outside
the face sieve, and define the filled two-cochain as `a + δb`. Closure follows
from `δ² = 0`; restriction to the tube must recover `u`, and restriction to the
cap must recover `a`. Zero-extension is performed on chains whose last object
lies in the sieve. Its naturality is about pullback of that actual sieve.
It is not an assumption that vertex membership detects a face.

## Checks and remaining proof obligations

The following construction steps are now kernel-checked:

- The section/cochain correspondence on the opposite category of elements,
  including reconstruction of the selected section and reindexing.
- The relative fresh-coordinate prism, vanishing at the cap, and its exact
  parameter substitution law.
- Extension by zero on the actual face sieve, including restriction and
  pullback laws.
- `boxFill_fills`, `boxFill_reindex`, and the assembled `lawfulCocycleFamily`.
- A specific boundary cocycle whose restrictions to all four formal square
  faces are zero.

`observeSquare_witness` computes the observation as one.
`observeSquare_stokes` proves the signed six-face identity for every three-cube,
and `SquareHomotopy.observation` applies it to homotopies relative to the four
zero sides. Thus the selected square admits no such homotopy to zero.
The remaining obligations are the connection to the contextual model's actual
normalized identity terms and the coherence needed by the unchanged client's
selected identity witnesses. The nonconstant family
and concrete frozen substitutions must use this same cubical model.

The candidate observer is an oriented sum over the flags
`corner → edge → square`. Its checked invariance evaluates the
cocycle equation on the forty-eight flags of a three-cube. The explicit square
has observer value one. These computations do not identify the entire homotopy
type with an Eilenberg–Mac Lane space.

## Approaches not accepted as substitutes

A cofree presheaf can contain distinct squares while remaining contractible;
that does not supply the requested coherent higher invariant. The face marker
in the constructed inductive identity likewise does not, by itself, prove a
nonzero higher homotopy class. Finite vertex-cocycle and ordinary cubical
abelian-group sketches leave naturality under arbitrary De Morgan
substitutions unresolved. Those gaps remain reasons to avoid using these
sketches as completion evidence, rather than proofs that every such approach
is impossible.

## Checked construction steps

The current candidate has kernel-checked low-degree cochain formulas
`δ₁δ₀ = 0` and `δ₂δ₁ = 0`, the categorical prism boundary identity, and
extension of a degree-one cochain by zero along a sieve with its exact pullback
law. `cocycles` is a presheaf on the existing formal De Morgan category, using
Mathlib's actual `Over.map` functor. `CubeCocycle.closed_eval` and
`pullback_eval` express its closure and restriction on formal flags.

The fresh-coordinate functor on each cube slice and both graph natural
transformations have also been constructed. Their difference gives the checked
identity `capPrimitive_boundary`: the coboundary of the selected primitive is
the original cocycle minus its cap restriction. `ElementPartialPrism` extends
this construction to the actual partial tube. `CocycleBoxFilling` proves both
boundaries, and `CocycleFillingSubstitution` proves strict naturality of the
assembled filler. `CocycleFilling` packages these results as `Filling.Lawful`.
This is a constructed uniform filling operation, without an assumed filler.
The nonzero class and coherent observer remain separate proof obligations.
