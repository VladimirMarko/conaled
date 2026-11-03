# Finite-quotient infinitesimal tangents

This records the semantic construction for [#99], following the accepted
[torsor checkpoint] under [#100] and [#36]. The construction combines actual
sheaf torsors, first-order infinitesimal arcs and the classical quarter-turn
derivative. It does not yet interpret an internal proof of that consequence.

## Quotient and parameters

`SheafActionQuotient.Object a X` consists of a locally trivial group-sheaf
torsor over the parameter sheaf `X` and an equivariant map from its total
sheaf to the acted-on sheaf `M`. Its arrows are equivariant torsor
isomorphisms preserving that map. Restriction has identity and composition
laws. The regular-torsor construction `chart` includes points of `M` in the
quotient; it does not exhaust the quotient's objects.

The extra equivariant maps descend through the effective torsor descent
construction from #98. `SheafActionQuotient.Descent` constructs the map by
sheaf descent, proves its equivariance, and retains every compatible arrow.
Its comparison, canonical recovery and arrow correspondence supply effective
object and arrow descent. `Examples.QuotientDescent` exercises this on the
nontrivial doubled-origin torsor. The resulting quotient object is not
isomorphic to any regular chart. The base remains the doubled-origin line
sheaf, with no claim of an annulus or manifold presentation.

A strict ordinary action by sheaf maps extends to locally constant labels in
`SmoothConstantAction`. The map from constant labels with parameters to the
sheafified group with parameters is locally bijective. Its proved universal
property constructs the extended action. Group laws follow by separatedness
on the label-cover sieves, including disconnected parameters.

The smooth site and sections remain small (`Type 0`); its sheaf category and
quotient objects live in `Type 1`. No resizing, universe classification or
univalence is used. Generic quotient modules keep the site's and sections'
universes explicit.

## Discrete inclusion and infinitesimal mapping

`DiscreteSheaf.inclusion` is the fully faithful Yoneda embedding of the sheaf
category followed by Mathlib's discrete category functor. At a parameter
sheaf `X`, it has objects the actual sheaf maps `X → F` and discrete arrows.
For the supported mapping construction, `Map(iA,iB)(X)` is the discrete
category of maps `A × X → B`. Currying yields `mappingIso`, an isomorphism
of Cat-valued presheaves identifying this with `i(B^A)`.

`SmoothDiscreteMapping.klMappingIso` composes that comparison with the
existing geometric KL isomorphism. Its formulas identify the comparison and
inverse with the existing affine reconstruction and coefficient extraction.
Evaluation is the actual affine value `a + b*d`; zero selects the first
coefficient. Product compatibility and restriction hold for arbitrary sheaf
parameters. This uses the current constructed exponential and smooth KL
model, without replacing sheaf morphisms by pointwise functions.

For the quotient, the supported mapping groupoid is `Map(iD,Q)(X) = Q(D × X)`.
`SmoothTorsorParameters.parameterTorsorEquivalence` extends the represented
comparison to every sheaf parameter. Its universal infinitesimal path
retains the parameter sheaf and evaluates at the point's actual nilpotent
coordinate. Projection and zero restriction are inverse equivalences on
all torsors and arrows.

`QuotientPointedArcs.Pullback` is the comma groupoid of the quotient chart
and zero restriction. Its boundary is an actual invertible quotient arrow,
and its morphisms satisfy the boundary square. Full faithfulness of torsor
restriction lifts the boundary trivialization uniquely. Evaluating the
quotient map at the lifted section constructs the arc and proves recovery
of the entire pointed datum. `SmoothQuotientArcs.comparison` therefore gives

```
i(M^D)(X) ≌ (iM ×ʰ_Q Map(iD,Q))(X)
```

for every sheaf `X`, with compatibility under every map of parameter sheaves.
The use of a chosen lift in this comparison does not imply that unpointed
quotient objects are globally trivial. The boundary is precisely the extra
data that permits the trivialization to lift.

## Fixed lifts and classical coordinates

The fixed-lift construction retains a boundary isomorphism from the chosen
chart point. Its equivalent discrete arc description imposes the actual
zero value. Forward transport along a quotient arrow changes that boundary
by precomposing with the inverse arrow. The resulting arc comparison keeps
the boundary triangle, identity, composition and parameter restriction.

Arrow labels have an explicit orientation: a chart arrow from `m` to `n`
is labeled by `g` with `m = g·n`. Consequently forward transport uses the
inverse label. The action arrow associated to an ordinary element `g`,
from `m` to `g·m`, uses label `g⁻¹`; its forward tangent action is the
ordinary action of `g`.

`SmoothOpenArcs` identifies the dual extension of an ordinary principal open
sheaf with its base point and finite real-coordinate tangent coefficient.
The open condition constrains the base coefficient; the infinitesimal
coefficient is unrestricted. The isomorphism is natural at every stage and
passes through the actual exponential to arbitrary parameter sheaves.
`SmoothQuarterTurnArcs` applies it to the disk's complex chart through two
real coordinates and compares the coefficient action with
`QuarterTurn.disk_tangent`.

The quotient consumers retain four origin automorphisms, recover trivial
isotropy at nonzero disk points, and keep distinct arrows for an ineffective
C4 action on the scalar line. Their coefficient maps agree with the ordinary
derivative, including the identity derivative for the ineffective action.

## Remaining source-to-model work

This result supplies semantic quotient arrows, their fixed-lift transport
and a classical comparison. It does not supply source derivations or soundness
for the following operations:

- Typed contexts, comprehension, substitutions and conversion with their
  identity/composition laws.
- Arrow-valued `Id`, reflexivity, dependent `J` and its computation rule,
  natural under substitutions and endpoint arrows. Concatenation and
  transport must be derived from `J`, with all-rule soundness.
- The selected `BG` and its action family, dependent sums presenting the
  quotient, and the identity/path-over rules needed for their paths.
- The supported dependent-function/exponential rules for `D`-arcs, their
  evaluation and zero substitution, together with the interpretation of the
  particular KL and infinitesimal torsor-discreteness statements used here.

The [accepted transfer interface] specifies the first Id/J experiment in
ordinary groupoids, tracked separately by #102. A concrete next construction
is its smooth interpretation on these parameter-indexed quotient groupoids
and their fixed-lift tangent families. It must identify interpreted paths
with the actual quotient arrows, interpret derived transport as the forward
transport constructed here, commute with parameter restriction, and descend
families and sections. Applying all-rule soundness to the same transported
concatenation derivation should then recover composition of the classical
tangent action, including ineffective loops.

That would connect the source proof to this semantic theorem. It would not
by itself interpret universe rules, general higher dependent sums, cohesive
modalities or crisp judgments. General Weil KL, microlinearity, transverse
pullback preservation, and the proper étale presentation theorem remain
outside this result. The full #36 bridge remains open.

[#99]: https://github.com/VladimirMarko/conaled/issues/99
[#100]: https://github.com/VladimirMarko/conaled/issues/100
[#36]: https://github.com/VladimirMarko/conaled/issues/36
[torsor checkpoint]: smooth-torsor-invariance.md
[accepted transfer interface]: agda-transfer-interface.md
