# Source transport coherence: concrete local construction

Separate addendum; frozen proposal and brief unchanged.
Base `4c81050dd2844c39bcfc551426f1e1cdbe3bcac1`.

The source declaration that supplies the needed square comparison is
`NativeTransportComposition.squareComparison` in
`SquareKit/Internal/Cubical/DependentTransportComposition.lean:385`.
It is not merely a theorem named suggestively: its inputs are a chosen lawful
filler on an actual family B over a square, actual left and right dependent
sections l,r, and an actual bottom dependent path p. Its output is a native
homogeneous path between transport along the upper edge applied to the upper
left value and the upper right value. `squareLift` at line 373 constructs the
required dependent square via the existing path-family filler; `squareTop`
at line 377 extracts its upper dependent path. `squareComparison` uses
`sectionComparison` on that path. Reindexing of the entire lift and upper body
is proved by `squareLift_reindex` at line 407 and `squareTop_body_reindex` at
line 423. These are existing Lean declarations, not new claims of validation.

To derive the Q triangle law, use the actual source code square induced by
coordinatewise conditional(s,canonical(v,a)(t),canonical(v,w)(t)). Pull
`NativeDecode.filling` back along this square to obtain F. Its boundaries are:
left constant v, bottom v→a, right a→w, top v→w. Given an input x at v:

1. l is the constant section x on the left.
2. p is the actual `IntervalTransport.forward` section along the bottom,
   made into a dependent path using its zero and one equations.
3. r is the actual forward section along the right, initialized at p's endpoint.
4. `squareComparison F hF l r p` now compares the actual chosen upper-edge
   transport of x with the actual consecutive bottom/right transport of x.
5. The upper-right vertex decoder is isomorphic to a constant finite family.
   `PathDiscrete.ofIso` and `constant_pathDiscrete` in
   `DiscreteEquivalences.lean` turn this path into equality. Extensionality
   gives equality of the bijections in Q's functor composition law.

The same construction proves independence of dimension path. Use the
conditional between two paths with the same endpoint vertices. Its left and
right edges are constant; choose l as constant x and r as the constant value
of the bottom transport of x. The bottom dependent forward section supplies p.
The resulting squareComparison and target discreteness equate top/bottom
transport. This proves Q naturality when a De Morgan substitution sends the
canonical vertex path to a noncanonical expression with the same endpoints.

Identity can use `NativeTransportComposition.alongIdentityComparison`
(line 233) or `NativeUnivalence.reflexiveTransportComparison` in
`CompositionalUnivalence.lean`; target discreteness again gives an exact identity.

Remaining implementation work is the explicit pullback casts between these
source-family presentations and `pathToMap`, using `pathToMap_along` and the
existing reindex laws. The formulas above specify the square and all three
input sections; they do not assume an unprovided general coherence theorem.
No new Lean proof has been compiled in this investigation.
