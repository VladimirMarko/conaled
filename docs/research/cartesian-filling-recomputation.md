# Cartesian filling and selected witness recomputation

Research construction for [#600](https://github.com/VladimirMarko/conaled/issues/600),
using source revision `4c81050dd2844c39bcfc551426f1e1cdbe3bcac1` and the
[accepted #574 clients](second-cubical-witness-preservation.md).

The target has chosen fillers for every box of presented discrete families
and a finite-set groupoid nerve with its tuple decoder. The exact Fin3/Phase
package and complete finite equivalence records agree with target recomputation.
For the public `swapComposition` square, a concrete decoder realization and
boundary alignment produce a recomputed square in the original restricted
universe. A chosen native relative three-path connects it to the retained
source square with every face fixed.

These are mathematical constructions with proofs for research review, not new
Lean declarations or kernel validation. Existing Lean declarations provide the
named source operations. [#599](https://github.com/VladimirMarko/conaled/issues/599)
owns formal restriction; this report uses its mathematical specification and
does not treat concurrent implementation as proof evidence.

The [design challenge](design-challenges/2026-11-16/cartesian-filling/synthesis.md)
retained the all-box construction and rejected equality after a nerve observation
as a substitute for comparison in the restricted source universe. The realization
and relative extension below address that objection. The original independent
reports remain linked there.

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

## All boxes of presented discrete families

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

The two inverse recipes are compared separately. The center-selected inverse
projects the unique generic fiber center, so it is the inverse bijection, with
unique left/right path bodies. The universe-selected `inverseMap` transports
along reversed ua; source reverse-transport and ua comparisons, followed by
endpoint discreteness, identify its map with that same inverse bijection.
Its actual `inverseEquivalence` and `inverseLeft`/`inverseRight` then agree with
target recomputation by full generic-fiber/path uniqueness. This does not
assert the two recipes coincide outside the presented-discrete fragment.

For `CubicalFiniteStateIdentity`, use `f=(codeIso presentation).hom` and its
actual `nativeEquivalence`, `A=admittedLine f E`, and `e=admittedPresentation f E`.
The frozen section is exactly
`filledPackage A e (machine.conjugate (admittedCarrier f E))`. Its target
recomputation retains next-state observation 1, ready-valid and failed-invalid,
and the rejection of `wrongPresentation` despite its preserved initial state.
Initial state, step, invariant, initial-validity and preservation proof fields
are equal as the entire target package; no field is removed to obtain these
readouts. All finite-endpoint source composite records use the actual
`compositeEquivalence`, not an independently convenient source witness.

A constant code presheaf cannot finish #600. Every native path into it is
constant. Its decoder cannot turn a constant Boolean loop into negation of true.
This separates decoded-family filling from univalence without claiming that
another classifier is impossible.

## A non-discrete bounded code presheaf

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

## Source comparison before realization

For completeness, the nerve also receives a comparison Q from source code cubes
whose closed vertex codes decode to constant finite families. At vertex v use
the actual closed-section set of its decoder. Between v and w use source
transport along the coordinatewise De Morgan path: constant on equal coordinates,
t on 0→1 coordinates, and negation of t on 1→0 coordinates. The endpoint
presentations turn the full native equivalence into a bijection.

The coordinate expression

```
conditional(s,p,q) = (s ∨ p) ∧ (¬s ∨ q) ∧ (p ∨ q)
```

has endpoints p,q and equals p whenever p=q; it does not use the invalid
De Morgan law s∨¬s=1. Applying it to canonical(v,a) and canonical(v,w) produces
a square with bottom v→a, right a→w, top v→w and constant left v. The exact
[source square-lifting construction](../../SquareKit/Internal/Cubical/DependentTransportComposition.lean)
`NativeTransportComposition.squareComparison` takes the bottom forward section,
the right forward section initialized at its endpoint, and the constant left
section. It compares top transport with consecutive bottom/right transport.
Discreteness only at the final vertex makes the resulting maps equal. This
proves Q's composition law. The conditional between two paths with the same
endpoints, using constant side sections, proves independence of the chosen
dimension path and hence Q's substitution law. The
[transport derivation](design-challenges/2026-11-16/cartesian-filling/transport-addendum.md)
records the precise existing constructors.

Every vertex of the exact `swapComposition` is `code (Fin 3)`. Write H for
that square and L for the actual closed-section carrier of its decoded vertex
code, which is the object used by Q. Fix the bijection e:L≃Fin3 obtained by
lowering the lifted decoder, applying `(constantLocal terminal (Fin 3)).decodeCodeIso`,
and then `DiscreteEquivalences.closedSections`. Equivalently, its value on a
closed section is its decoded Fin3 value at the zero cube. This identifies
closed sections with their zero-cube elements without identifying L with Fin3
as types.

For a permutation h of Fin3 put h_L=e⁻¹∘h∘e. Independently recompute the
target nerve square T_L on the object L using (swap01)_L followed by
(swap12)_L and the target operations. Then the well-typed equality is
Q(H)=T_L. Its side arrows are identities on L. Its lower arrow is
e⁻¹∘swap12∘swap01∘e, from the exact source composite record, and its upper
arrow is (swap12)_L∘(swap01)_L, from the selected concatenation. Cancellation
of e∘e⁻¹ identifies these arrows. Together with the common object L at all
vertices, these equations determine the entire nerve functor.

The Fin3 square T used below is related to T_L by the natural isomorphism
whose component at every vertex is e. On any arrow h_L its naturality equation
is e∘h_L=h∘e; on each side it is e∘id_L=id_Fin3∘e. Thus the same adapter
identifies all four faces. Pullback along a Cartesian substitution precomposes
the vertex functors and this constant-component natural isomorphism, so both
Q(H)=T_L and its relation to T commute with substitution and successive
substitution. No equality of L and Fin3 is used. These comparisons in the
nerve do not recover the source interior or supply the required relative
comparison in RU; the following construction supplies that additional result.

## Realization with the original small universe

Define the same vertex nerve N_D(G) on De Morgan cubes: a substitution acts on
Boolean vertices by evaluating its De Morgan expressions at endpoints. This
respects identities/composition. Restriction to Cartesian substitutions is
literally the earlier N_C(G). No retraction from R(I_D) to I_C is used.

For every T:V_n→G define a small dependent family A_T over y_D(n). At the
generalized point f:m→n its fiber is

    A_T(f) = { (x_v)_{v∈{0,1}^m} | x_v∈T(f(v)),
                 T(f(v)→f(w))(x_v)=x_w for all v,w }.

Restriction along g:k→m selects the entries at g(v). For f arbitrary, the
fiber is Type u: there are finitely many vertices and each T(f(v)) is Type u.
The family lives over the small representable, although the presheaf N_D(G)
is Type (u+1). This avoids incorrectly classifying a large-base LocalFamily
into U_(u+1) and changing the frozen U_u.

Give A_T the decoder filler constructed above: an arbitrary
base map Y×I→y_D(n) determines a code functor at each cube; transport the base
tuple along its arrows from (v,r_v) to (v,z). This works under De Morgan
substitution as well: Boolean vertex evaluation commutes with all substitutions.
Its source, tube and naturality equations hold on every tuple entry and every
compatibility equation. Specialize r=0, s=1 and the existing source cofibration
class to obtain a lawful `Filling A_T`, then its `toLocal` supplies the data of
`SmallFamilyCode n = LocalFamily (representable n)`.

For h:k→n the strict code equation is

    A_(T precomp vertices(h)) = (A_T).reindex (representableMap h).

At f:m→k both sides have exactly the tuple equations indexed by h(f(v));
restriction selects the same entries, and both fillers use the same composite
code functor and transport arrows. Thus the families and the chosen filling
functions agree; the law fields are proof irrelevant. Where the representation
inserts associativity equalities, transport by those equalities is included in
this equation. This is equality of complete LocalFamily records, not merely
isomorphism of their underlying sets. It derives a natural map

    Real_D:N_D(G) → smallFamilyCodes_u.

Equivalently use `LocalFamily.code` on each represented chart, with
`LocalFamily.code_reindex` for the same equality. The decoder comparison is
`LocalFamily.decodeCodeIso`, and the existing classification filler comparison
at `SmallFamilyClassification.lean:380` shows it preserves the selected filler.
Restriction gives Real_C:N_C(G)→RU. A target nerve square is therefore genuinely
realized as a code-valued square in RU. The target nerve operations were defined
before Real and do not take the original source square as an input.

For a constant nerve code on S, A_T is the family of constant tuples. Evaluation
at a vertex and constant-tuple formation are inverse natural isomorphisms
with ΔS. The result does not depend on which vertex is selected: every tuple
has equal entries. Compose this isomorphism with `decodeCodeIso` and the existing
lowering/raising and constant-code decoder isomorphisms. Denote the resulting
actual decoder isomorphism by

    j_S:El(code S) ≅ El(Real(const S)).

This fixes the endpoint carriers and their universe lifts. The code values
need not be judgmentally equal.

## Independently recomputed square and aligned boundary

Let S=Fin3; put a=code S and a'=Real(const S). In N_C(G) use the actual
bijections swap01 and swap12. Its decoded-fiber inverse/composite records and
its ua paths are obtained from the target tuple filler. The native target
composition square T has vertical arrows identity and horizontal arrow
swap12∘swap01. The nerve laws determine its entire functor. One may choose the
reflexive comparison when the selected target concatenation has been identified
with the target ua of this composite. This choice is made wholly in the target.
It does not mention source `swapComposition`.

The same T is a De Morgan nerve cube, so Real_D(T) is a source square between
paths P0,Q0:a'→a'. Define α=ua(j_S,ofIso(j_S)):a→a'. Its transport is j_S by
the source ua transport comparison and discreteness of the two endpoint
families. Transport along reverse α is j_S^-1 by the source reverse comparison.

Use the natural path operation

    W(z) = α · z · reverse α

with a fixed parenthesization and the existing lawful source universe filler.
The reindex laws for native concatenation make W a family map from paths(a',a')
to paths(a,a). Map Real_D(T) through W to obtain the whole square

    K : Path_(paths(a,a))(P,Q),
    P=W(P0), Q=W(Q0).

Both P and Q have closed permutation swap12∘swap01. For Real paths this follows
from the tuple decoder's actual chosen transport; the endpoint adapters j_S
cancel in W. It is a decoder calculation on the realized square, not inferred
from equality of Q observations of some source body.

Let p be the exact source ua of the actual `compositeEquivalence`, and q the
exact selected source concatenation in `swapComposition`. They have the same
permutation, by `loopPermutation_ua`, the actual composite-map equation, and
`loopPermutation_concat`. Use the existing constructor
`FiniteUniverseLoops.samePermutation_path` to choose

    δp:p→P,   δq:q→Q.

Its implementation uses native univalence and actual transport equivalence
records (`classifyLoop`); it does not replace native path bodies by host equality.
Neither δ depends on the source composition square H. They depend only on its
fixed boundary paths and the newly realized boundary paths. Define

    H_new = δp · K · reverse δq : Path_(paths(a,a))(p,q).

This has exactly the source p,q boundaries, not merely isomorphic endpoints.
The α whiskering gives the exact fixed code a on both lateral faces. The source
chosen contractions inside p and q have never been replaced in those boundaries.

## Chosen relative witness between H and H_new

Set X=paths(a,a), D=equivalences(a,a), and f=pathToEquiv(a,a). The source
`univalence(a,a)` is an actual HomotopyEquivalence f.

First derive a natural isomorphism D≅Δ(S≃S), with the explicit lifting/decoder
isomorphisms above understood. For constant presented carriers, a generalized
Pi element is determined by identity evaluation, with inverse obtained by
using carrier reindexing isomorphisms. A path in a constant carrier is the
unique constant generalized body when its endpoints agree. Hence a generic
fiber of a bijection is pointwise singleton. Its center and its entire
contraction are unique by section/Pi extensionality. Conversely, an equivalence
record supplies a bijection via the selected center and its two inverse
homotopies. These constructions are inverses on the complete records. This
proves the family isomorphism, not merely PathDiscrete or a theorem about
closed observations. It is the derived uniqueness adapter requested by the
reviews.

Let d=f(p). Let Z=Fib_f(d) be the actual homotopy fiber, formed by reindexing
`univalence(a,a).fibers` along the section d of D. It has a chosen contraction
c. It has a chosen lawful filler F_Z from `genericFiberFilling` applied to
`pathsFilling a a` and `EquivalenceFamilies.equivFilling`, then reindexed along
d. No new contractibility or filling field is assumed.

For either H or H_new, its body h(i) is a section of X over the comparison
interval, with h(0)=p and h(1)=q. The section f(h(i)) of D is constant in i by
the actual D≅Δ(S≃S) presentation. Its value is d, including every generalized
argument. Thus it has the unique full constant path to d and gives a section

    h_hat(i)=(h(i), refl_d with the identified endpoint) of Z.

The whole images f(H) and f(H_new), not just their endpoints, are handled here.
Their lifted endpoints agree as elements of Z, because their first components
are the same p,q and their D-path components are unique. Call them p_hat,q_hat.

Over two new intervals i,j prescribe the partial section of Z on
φ=(i=0)∨(i=1)∨(j=0)∨(j=1):

    j=0: H_hat(i)       j=1: H_new_hat(i)
    i=0: p_hat          i=1: q_hat.

At each corner the specified endpoints agree; on opposing disjoint faces
there is no compatibility obligation. The local face-union construction of
partial sections therefore gives an actual partial section b of Z. Apply

    L = (c.reindex π).extend (F_Z.reindex π) b,

where π drops both new coordinates. `HomotopyContractible.extend` is the
explicit constructor in `EquivalenceExtension.lean:50`, and its boundary
law at line 53 fixes the entire prescribed section on all four faces. Project
L to X. Abstract i and then j, retaining the boundary equations, to obtain

    Ω : Path_(Path_X(p,q))(H,H_new).

At the universe-body level Ω is a three-cube. Its two comparison faces are
the exact original H and the realized/recomputed/aligned H_new; its remaining
faces are the fixed p,q and a,a as required. It preserves the original H as
an actual face, rather than declaring H equal to a boundary-determined nerve
image. This is the missing native relative comparison.

## Substitution and composition of the chosen comparison

The constructions are fixed at the closed finite client and then pulled back
along every base substitution σ. Target filling commutes with substitution,
Real is natural, and W commutes with reindexing by the native concatenation
laws. The boundary paths are the exact frozen source p,q and their documented
whole-body reindexings. Choose δp_at and δq_at as reindexings of the fixed
closed δp and δq; do not claim an arbitrary independent invocation of an
unproved naturality law for `samePermutation_path` makes the same choice.
Likewise take c_at and F_Z_at by reindexing their fixed selected data.

This is an explicit chosen comparison operation on the client's entire
substitution closure. Its higher extension is uniform because
`HomotopyContractible.extend_reindex` (`EquivalenceExtension.lean:68`) states

    (c.reindex σ).extend (F.reindex σ) (b.reindex σ)
      = (c.extend F b).reindex σ.

Canonical path and fiber comparisons identify the displayed types. Thus
Ω_at(σ) is the reindexed whole Ω, and Ω_at(σ∘τ) equals reindexing Ω_at(σ)
by τ, including every face. Restrict via #599's κ³ (iterate its generic-cube
path comparison) to obtain the required native Cartesian relative witness
in RU. No naturality of unrecorded fresh choices is claimed, and no pentagon
or arbitrary triple-recomputation comparison follows.

## Scope and residual

The target fills all boxes of its actual tuple decoder and code nerve. The
source realization and Ω close the original selected square obligation with
a specified native relative comparison. The presented-discrete argument still
handles the whole dependent package, and singleton generic fibers compare
both inverse recipes separately before identifying their results in this
fragment. Bool identity/negation and noncommuting Fin3 swaps remain separated;
Ω only compares squares with the same fully specified boundary paths.

The classifier domain is the explicitly presented vertex-local-system families.
No result says every Cartesian diagonal-Kan family has that presentation.
The broader classifier follow-up takes an arbitrary small Cartesian diagonal-Kan
family A, constructs/classifies its code in a target universe, and provides a
decoder/ua comparison beyond local systems. The current Real map, its tuple
filler, the native boundary alignment and Ω are reusable inputs, not a proof
of that broader classification.
