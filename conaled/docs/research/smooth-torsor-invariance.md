# Smooth-site torsor invariance

This is the implementation record for [#98], under [#100] and [#36]. It follows
the first checkpoint selected in the [Myers assessment]. The construction uses
the existing smooth open-cover site and its Type-valued sheaves.

## Constructed comparison

For a group `H : Type`, `locallyConstantGroup H` is the sheafification of the
constant **group** presheaf. Thus its sections can have different labels on
different connected components. The quarter-turn application takes
`H = Orbifolds.QuarterTurn.C4`; the proof does not need finiteness.
The smooth-site group and base sheaf sections live in `Type 0`; the torsor
groupoid's objects live in `Type 1`. The generic descent module uses sections
in `Type (max u v)`, matching the existing dependent-product interface for a
site with object universe `u` and hom universe `v`.

`SheafTorsor.Torsor G X` consists of a split sheaf family over `X`, a natural
`G`-action, unique transport between any two sections of one fiber, and local
existence of sections. The split sheaf interface already represents arbitrary
sheaf displays over `X`. This definition permits fibers without global
sections. `Arrow` retains equivariant natural isomorphisms, and
`EquivariantMap.toArrow` proves that every equivariant map of torsors is
invertible. No passage to isomorphism classes is used.

The theorem `SmoothOpenSite.infinitesimalTorsorEquivalence (H := H) A` constructs

```
Torsor (locallyConstantGroup H) (y A)
  ≌ Torsor (locallyConstantGroup H) (D × y A).
```

Its functor is restriction along the product projection. Its inverse is
restriction along the zero section. The corresponding equality theorems
identify those functors, and `torsorProductZero_apply` checks the zero section
on generalized points. The equivalence contains natural unit and counit and
the triangle law. `torsorProjection_baseChange` and `torsorZero_baseChange`
prove the represented versions commute with every presentation map, including
maps involving nilpotent stages. `infinitesimalTorsor_baseChange` and
`infinitesimalTorsorZero_baseChange` state both squares directly for the
product presentation.

The proof uses two existing constructions. `dualRepresentable` identifies
`D × y A` with the represented dual extension. The sheaf exponential by `D`
provides a sheaf structure for `F(dual A)`, with its natural comparison proved
in `SmoothDualSheaf`. Neither construction by itself supplies torsor
invariance. The additional ingredients are:

- `dualParameterSieve_cover`, proved for every covering sieve of the generated
  topology, transports local witnesses through the dual extension. Its proof
  checks principal covers and then the topology's closure operations.
- `constantGroupDualEquiv` proves infinitesimal invariance of the group sheaf's
  sections from local constant-label witnesses and sheaf separatedness.
- `dualTorsor` applies the cover result to the local-existence sieve of an
  arbitrary torsor. Its zero map is equivariant and hence invertible.
  `torsor_zero_bijective` applies at generalized points of an arbitrary base
  sheaf, including bases that are not represented.
- The universal infinitesimal path of a point of `y(dual A)` evaluates at that
  point's actual nilpotent coordinate. This gives the counit comparison with
  the original torsor without choosing a global trivialization.

Real points are used to define the site's principal covers and to analyze
ordinary connected examples. They do not replace the presheaf's arrows or
sections. All cover refinements and torsor comparisons retain arbitrary
infinitesimal target stages.

## Effective descent and the nontrivial example

`SheafTorsor.Descent.Datum` specifies equivariant transport between local
lifts, with naturality, identity, and cocycle equations. It contains no
effectiveness assumption. The descended family is the subsheaf of compatible
sections of the existing dependent-product sheaf. Compatibility is required
at every restriction stage. Evaluation on the cover has a constructed
natural equivariant inverse, and `evaluation_transport` recovers the supplied
cocycle. The cover need only be locally surjective. `mapEquiv` proves that
compatible local equivariant maps correspond to all equivariant maps of the
descended torsors. `canonicalRecovery` identifies the descent of an original
torsor's canonical data with that torsor globally.
`canonicalEmbedding_evaluation` verifies its comparison on the cover, and
`canonicalArrowEquiv` gives arrow descent for arbitrary original torsors.
`Map.arrow_ident` and `Map.arrow_comp` check preservation of identity and
composition.

This uses the existing split sheaf/Pi interfaces and Mathlib's subfunctor
locality. It proves effective Cech descent directly, rather than declaring a
`Pseudofunctor.IsStack` instance without its proof. The restriction functors
have proved identity and composition coherence. A later general stack
interface can package these constructions; that packaging is not an extra
assumption in the torsor theorem.

The nontrivial example uses the doubled-origin line sheaf. Two represented
real lines are glued along their punctured lines. The total sheaf glues two
regular group torsors with transition label `1` on the negative component
and a chosen nonidentity element on the positive component. Sheaf pushouts
and Mathlib's adhesive-category result establish the actual local product
charts. `SheafPushoutLocal` proves that sections of these pushouts locally
come from a chart.

A hypothetical global section would yield group-sheaf labels on both real
lines. `SmoothConstantOrdinary` proves that their point-label functions are
locally constant by refining covering sieves to ordinary neighborhoods.
Connectedness of the real line makes each function constant. Evaluating
the transition equation at `-1` and `1` contradicts the chosen label being
nonidentity. This is a sheaf-base example; no cyclic cover of an annulus is
claimed. `SmoothClutching.torsor` packages this display as a torsor: unique
acting labels are computed in its product charts and glued over the proved
covering sieve. Its `no_global_section` and `not_trivializable` theorems apply
to the C4 quarter-turn. The checked `recoveredNontrivial` example recovers
this nontrivial torsor by generic effective descent from its total-space
cover, on which `nontrivialCoverTrivialization` gives an explicit
trivialization.

## Interface and boundaries

The generic torsor, restriction, and local-axiom constructions live in
`SheafTorsor` and `SheafTorsorLocal`; they are independent of the smooth site.
The smooth comparison is the public theorem in `SmoothTorsorEquivalence`.
`Examples.SmoothTorsors` specializes it to C4, retains its nonidentity
regular-torsor automorphisms, and checks disconnected labels and a stage map
that kills a nonzero infinitesimal coordinate. `empty_stage_unique` proves
that sheaf sections at a stage with empty real locus form a singleton, as
required by the empty cover. The examples check this at the actual stage
obtained by localizing at zero. The equivalence has no inhabited-stage
hypothesis.

This is a directly constructed semantic theorem. It does not provide an
internal derivation, a higher identity eliminator, a quotient stack's tangent
comparison, a general Weil result, or a cohesive model. It uses the existing
KL/evaluation model's represented infinitesimal and exponential structure;
it does not assume a new KL or torsor-invariance axiom.

The [source/model handoff] remains the interface plan for interpreting higher
source rules. To reach #36, an interpretation must still identify source paths
with actual torsor isomorphisms, construct the selected quotient and its
pointed homotopy-pullback comparison, and connect the result with the existing
classical quarter-turn tangent calculation. #99 must consume the constructed
torsor/descent interfaces and prove these further comparisons. Ordinary
manifold full faithfulness alone does not discharge them.

The [#99 construction record](finite-quotient-tangents.md) describes the
subsequent quotient, pointed infinitesimal comparison and classical tangent
consumers, together with the remaining source interpretation.

[#98]: https://github.com/VladimirMarko/conaled/issues/98
[#100]: https://github.com/VladimirMarko/conaled/issues/100
[#36]: https://github.com/VladimirMarko/conaled/issues/36
[Myers assessment]: myers-tangent-integration.md
[source/model handoff]: agda-transfer-interface.md
