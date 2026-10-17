# First-order interpretation and compiler naturality

`SquareKit.FirstOrderNaturality` interprets the existing first-order syntax in
an arbitrary object family, with independent object and hom universes.
`cartesian` recursively interprets base, unit, and products using only
`CategoryOps`, `TerminalOps`, and `ProductOps`. `Model` is the syntax boundary:
its source-type indices do not occur in those shared interfaces. Neither the
compiler nor its preservation theorem requires function semantics, category
laws on the source, or exponentials.

`naturality` states preservation modulo the destination hom equivalence for
every term in every context. `cartesian_naturality` specializes it to a map
with explicit terminal and product comparisons. The image model retains the
carrier `F.obj (objects T P base a)`. Its projections run the forward product
comparison before the destination projection; pairing runs the inverse
comparison after destination pairing. Terminal maps likewise use the inverse
terminal comparison. These are executable arrows, not casts equating objects.

The preservation equation needs the local coherence equations
`TerminalMapLaws` and `ProductMapLaws`. It does not need the inverse equations:
those are additional obligations when claiming a strong cartesian map or
transporting cartesian laws. The matrix example supplies both directions of
the inverse equations through `matrixFunctionProducts_inverse` and
`matrixFunctionTerminal_inverse`. This weaker theorem does not assert that
an arbitrary comparison-aware model itself satisfies cartesian laws.

| Obligation | Provider |
| --- | --- |
| Identity and composition preservation; congruence | Shared `MapLaws` |
| Terminal, projection, and pairing coherence | Shared terminal/product map laws |
| Destination congruence for composition and pairing | Shared category/product congruence |
| Recursive syntax preservation, including variables and let bindings | `naturality` |
| Primitive compatibility | Each language/backend interpretation |
| Coordinate comparison inverses and primitive matrix meaning | Matrix representation |
| Composed interpretation preservation | `RawMap.comp_laws`, `ProductMap.comp_laws`, `TerminalMap.comp_laws`, and `preserves_comp` |

The compatibility adapter `ofTarget` retains every operation of the existing
`FirstOrderCompiler.Target`. `compile_ofTarget` identifies the two compilers.
`soundMap_laws` and `sound_preserves` turn the existing `Sound` fields into a
shared interpretation map and primitive compatibility. The new `compile_sound`
derives the original arbitrary-input conclusion through `naturality` and the
semantic interpretation. The original dependency-free files, their public
statements, and `no_exponential` remain unchanged.

`MatrixCompiler.Naturality.compile_coordinates` applies the generic theorem to
the composed map from actual matrices through their coordinate action into
functions. The product comparison changes a function on a coordinate sum into
a pair of functions. `coordinate_linearCombination` checks the independently
specified result `2*x + 3*y` through this compiler theorem, for all scalars.
`additive_let` checks binder handling and two free variables through the Sound
adapter. `finiteModel` uses actual finite-coordinate objects rather than `Ty`
as objects; both rows of its duplication matrix are checked.

Compared with Felix revision `6f36d28097db7ea5f5df3263db3e8be08f74e490`,
`Homomorphism.agda` supplies the category and cartesian preservation vocabulary
and composition proofs reused here. This module adds the first-order syntax
consumer and explicit non-strict product comparisons. It does not claim a
full STLC preservation theorem; sums and closure are outside this ticket.
The matrix/stack migration can instantiate the same theorem with distinct
matrix interpretations and their product comparisons.
