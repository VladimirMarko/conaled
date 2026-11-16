# Cartesian filling investigation for #600

Investigation base: `4c81050dd2844c39bcfc551426f1e1cdbe3bcac1`.
Status: mathematical constructions for design challenge, not Lean theorems.
No production files changed and no build run. The final source-to-target
comparison below needs its proof details independently challenged before adoption.

## Primary source and local inputs

The inspected author manuscript is
<https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf>, SHA-256
`ea235cf09eae29d3859f31976bc43a939a6565410ff4117addb99d0602c213a3`.
Definition 1, p. 9, specifies arbitrary source and target interval terms and
agreement also where they coincide. Theorem 2 and section 3.4 are the previously
pinned model existence and same-base comparison results. Neither supplies our
cross-category comparison. All constructions below are direct arguments.

Local source inputs are `CubicalStructuredState.admittedPresentation`,
`CubicalStatePackageFamily.filledPackage_observed`, `CubicalStructuredState`'s
`filling_recovery` use, `DiscreteEquivalences`, `DependentTransportComposition`,
`NativeUnivalenceComparison.uaEquivalenceComparison`,
`CompositionalUnivalence.compositeEquivalence` and
`NaturalUnivalenceLaws.composition`. Freeze the actual
`FiniteUniverseLoops.swapComposition` as in #574.

## Cofibrations and size

Use C from #599. At a representable cube, cofibrations are finite unions of
finite intersections of equations r=s for Cartesian dimension expressions.
Each consistent conjunction is represented by identifying variables and/or
setting them to endpoints; contradictory endpoint equations are empty.
Consequently all faces, diagonals and their intersections are present. Base
change substitutes expressions in the formula. General contexts carry compatible
local such subobjects. The filler formulas below actually work for every
subobject, provided its closed-vertex membership is decidable; in classical Lean
this is available without a new axiom. We do not need or claim a classification
of all decidable subobjects by this formula syntax.

Take small sets in Type u, their isomorphisms in Type u, and the groupoid of all
finite small sets in Type (u+1). The code presheaf is therefore one level above
its decoded fibers. No inaccessible cardinal or resizing is used. General
(nonfinite) discrete sets can be used for proof-bearing state packages without
claiming that the finite-code classifier contains all such packages.

## First construction: all boxes of presented discrete families

Let A over X have an actual natural isomorphism e:A≅ΔS. For arbitrary
p:Y×I→X, r:Y→I, tube t over φ×I, and base b over the graph r, define

    fill(y,z) = e_(p(y,z))^-1 (e_(p(y,r(y))) (b(y))).

A section of a constant presheaf over Y×I is independent of the interval:
evaluate at the generic added cube and restrict to each chosen interval term.
The same argument applies to a tube over φ×I, viewed as a section over the
subcontext φ. It proves agreement with t on φ, since agreement at r was part
of the box. The formula is natural under every substitution; at z=r it is b.
Evaluation at any s gives diagonal-Kan composition, and r=s computes to b.
This is an all-target-box construction, including tubes with no chosen source
lift. Any other lawful filler agrees with it by the same constancy argument.

For A≅ΔS the actual target Sigma/Pi package is naturally isomorphic to
Δ(StatePackage S). For a Pi element at x, any generalized argument a' at
f:y→x has a unique preimage a under the carrier isomorphism and reindexing.
Naturality then determines that function value from its identity evaluation.
This proves the specialized Pi inverse rather than presuming the general Pi
comparison is invertible. The proof-bearing fields use the same dependent
values; proof irrelevance only removes alternative proofs of the same
proposition, not the predicates or their argument dependencies.

Apply this to the exact admittedPresentation for Fin3/Phase. The source filled
package is equal to its pullPackage section (existing filling_recovery), and
restriction gives the same pullPackage. Target recomputation by the formula
above gives that section as well. All five fields agree at all generalized
arguments. Conjugation composition proves the nonidentity substitution and
presentation-composition laws. At constant finite endpoints, generic fibers
of bijections are singleton discrete families, so center, contraction,
selected inverse and both selected homotopies are unique as complete records.
This compares actual source composite/inverse records with recomputation,
not just the underlying functions.

A constant code presheaf cannot finish #600. Every native path into it is
constant. Its decoder cannot turn a constant Boolean loop into negation of true.
This separates decoded-family filling from univalence without claiming that
another classifier is impossible.

## Second construction: a non-discrete bounded code presheaf

For a groupoid G let V_n be the indiscrete groupoid on the set {0,1}^n.
Define N(G)(n)=Fun(V_n,G). Cartesian substitution acts by precomposition on
vertices. A cube consists of objects A_v and arrows a_vw:A_v→A_w with
identity and composition equations. In particular the entire two-cube is
determined by compatible boundary arrows. The nerve has nonconstant paths:
N(G)(1) includes every isomorphism in G, including Boolean negation.

Use G=the groupoid of finite small sets and bijections. The decoder over a
cube A is its compatible tuples (x_v), with a_vw(x_v)=x_w. Restriction
selects the corresponding tuple entries. Because V_n is connected, evaluation
at any vertex is a bijection between that cube's decoder fiber and A_v.
This definition is independent of choosing a preferred vertex, so restriction
can change or repeat coordinates without breaking naturality.

Here is a chosen diagonal-Kan filler for N(G), for every admissible target
box. At n-dimensional data, write v for a base vertex, z for the filling
endpoint, r_v for the source endpoint, B_v for the base object and B_vw for
its arrows. Closed-vertex membership φ(v) is a decidable proposition.

* If φ(v), set F_(v,z)=T_(v,z) and w_v(z)=the tube arrow
  T_(v,r_v)→T_(v,z), identifying T_(v,r_v)=B_v by box agreement.
* Otherwise set F_(v,z)=B_v and w_v(z)=id.
* Define every arrow by

      F_((v,z),(w,z')) = w_w(z') ∘ B_vw ∘ w_v(z)^-1.

The groupoid laws prove this is a functor. At z=r_v every w_v is identity,
so restricting to the source graph gives B, including arrows between vertices
where r takes different values. On the tube, functoriality and its source
agreement prove all objects and arrows match T. Under a dimension substitution,
vertices, φ membership, r, B, T and w are precomposed by the same vertex map;
thus the entire filler commutes with substitution. Evaluating at s proves the
source=target equation on the subobject r=s, not only for syntactically equal
r and s. This argument covers diagonals, repeated variables and endpoints.

For the decoder, an arbitrary box over p:Y×I→N(G) has the unique filler:
transport its base tuple along p's arrows from (v,r_v) to (v,z). The arrows
already supplied by p enforce agreement with the tube and naturality.
Thus no source-admission premise appears in either operation.

Codes classify this explicit vertex-local-system presentation, with a chosen
code map and identification with its decoded tuple family. They do not yet
classify every Cartesian Kan family. Native equivalences of decoded families
are fiberwise bijections: their homogeneous paths are unique when endpoints
agree. A pointwise bijection commuting with the transport arrows extends to
a code path by conjugating the arrows, giving a bounded ua operation. Its
transport is the original bijection; composition and inverse use groupoid
composition and inverse. A loop of a finite set is a permutation, not the
identity merely because its endpoints agree.

## Proposed source comparison on the exact square

A useful source domain is the subpresheaf of source code cubes whose vertex
codes have constant finite decoded families (up to natural isomorphism).
This condition concerns only closed vertex codes, not a false assertion that
all interiors of the source universe square are literally constant families.
It is stable under De Morgan substitutions, since these send vertices to
vertices. Every vertex of the exact swapComposition square is code(Fin3),
and the Bool and Fin3 ua loops also lie in this domain.

For such a source code cube u, construct Q(u) as follows. Its object at vertex
v is the closed-element set of the decoded vertex code. Its arrow v→w is
source transport along u evaluated on the coordinatewise De Morgan path from
v to w: constants at agreeing coordinates, t for 0→1, and ¬t for 1→0.
Native source transport gives an equivalence, hence a bijection between these
constant finite endpoint families (DiscreteEquivalences supplies the extraction).

The needed coherence proof is concrete, but not yet formalized. Two dimension
paths with equal endpoint vertices are homotopic relative to those endpoints,
using coordinatewise

    conditional(s,p,q) = (s ∨ p) ∧ (¬s ∨ q) ∧ (p ∨ q).

It equals p at s=0, q at s=1, and p whenever p=q. The latter avoids the false
De Morgan equation s∨¬s=1. A square with the appropriate repeated corner
compares transport v→w with v→a→w. Source dependent square transport and
composition give a native homotopy, and discreteness of the target vertex
family makes its maps exactly equal. This proves identity/composition for
Q(u). Applying a source substitution to the canonical dimension path gives
a path with the same endpoints as the newly chosen canonical path; the same
relative argument proves Q natural. This is where the source filling laws are
used; the target groupoid construction does not import them.

After this proof, Q applied to a source ua path has exactly the bijection of
the supplied f,E, by uaEquivalenceComparison and endpoint discreteness.
Q applied to concatenation has the composite arrow, and Q applied to the
selected inverse has the inverse arrow. Therefore Q applied to the **actual**
comparisonSquare swapComposition is the complete nerve two-cube with sides
identity, lower edge swap12∘swap01, and upper edge the same composite computed
through the intermediate code. Target recomputation gives that same whole
functor, because all objects and arrows in a nerve two-cube are determined
by these compatible boundary data. The entire cube equality, its four faces,
and substitution/composition follow, rather than just its numeric observation.
The Fin3 arrows still send 0 to 2 versus 1 in opposite orders. Boolean identity
and negation remain different arrows, and there is no two-path between them
with fixed sides in this nerve.

This comparison does **not** recover the original source code-valued square
from its nerve image. It is different from #599's faithful body restriction.
It retains the image of the selected body and proves equality with genuine
target recomputation. If #600 requires a relative three-path in RU between
two code-valued squares, Q alone does not meet that requirement: there is no
map back from this classifier to RU supplied here. That distinction must be
settled against the issue's intended comparison contract during design challenge,
not hidden by calling boundary agreement a source-square recovery theorem.

For the decoded finite endpoint records the comparison is stronger: singleton
fiber data give complete equality. For the finite-dependent package, use the
actual presentation and the first construction, preserving its proof fields;
do not infer package equality merely from the code nerve's truncation.

## Next work and concrete residuals

1. Challenge the all-box formulas, the source Q coherence argument, and the
   meaning of the whole-square comparison independently. In particular inspect
   whether the named source square transport theorem suffices to supply the
   required commuting transport square, or derive the missing law from filling.
2. If this bounded research route is accepted, write the construction and
   proofs with the exact source definitions and selected-body equation.
   Research review must not label these formulas kernel-checked.
3. Formalization can reuse #599's Cartesian category and restriction; the
   target nerve and decoder should not need changes to its source primitives.
4. Any stronger source-square recovery needs a chosen decoder/classifier map
   N(FinSetIso)→RU and a native relative comparison on the exact square. Concrete
   inputs are the nerve decoder, its all-box filler, Q, and the fixed source
   swapComposition. Alternatively classification of arbitrary target fibrant
   families requires leaving the vertex-local-system fragment. Neither follows
   from the external model's existence theorem.
