# Smooth source interpretation: checked construction checkpoint

This is a partial implementation record for [#433], based on accepted integration
`3bbf8083f94629fdedc1a438112f78d6d97a3196`. The original first-path
transport-composition proof is interpreted on every smooth quotient groupoid,
with a constructed family of torsor deformations. That family has parameter
restriction, a comparison with the actual boundary fiber, and effective descent
over each fixed quotient object. Its chart specialization gives the existing
fixed-lift transport and classical quarter-turn composition.

The remaining requirement is restriction and descent of the generated source
contexts and sections. The declarations below do not yet constitute the complete
parameter-indexed source model requested by #433. In particular, a model at every
parameter plus descent of its primitive family is not a proof of that closure.

## The retained source proof

No source rule or proof was changed. The source-consuming route is:

1. `SmoothQuotientDeformations.source_composition` invokes the public
   `GroupoidTransport.transport_concat` wrapper.
2. That abbreviation names `GroupoidModel.UniversalTransfer.transport_concat_universes`.
   It uses the existing universe-lift model and calls `transport_concat`.
3. The latter calls `TransferConsumer.consume` with
   `Typed.Authoring.UniversalTransfer.proof` and its actual generated inputs.
4. `consume` interprets that generated term, extracts equality in the discrete
   fiber, and identifies source transport and concatenation by the existing
   `SourceSemantics` and `ConcatSemantics` results.

This is the unchanged #104/#105 first-path proof selected in #102. The
`transport_comp` lemma needed to construct the semantic family is recorded as
model setup. It is not the body of the source-consuming theorem. The classical
consumer applies the interpreted source result before using the previously
proved coefficient/derivative comparisons.

The exact source requirements are already available: empty and extended typed
contexts, simultaneous substitution and comprehension pairing, the externally
assigned base and its fiber family, identities and reflexivity, conversion, and
J with the dependent `z,q,b` tail. The quotient is supplied as the external base;
its tangent family is supplied as the external fiber. This construction does not
require a source term presenting `BG`, general dependent sums, universes,
univalence, cohesion, or crisp judgments. No #107 operation or favorable #108
result is used as a prerequisite.

## Family on arbitrary quotient torsors

For a sheaf parameter `X`, let `P : SheafActionQuotient.Object a X`. A
`SmoothQuotientDeformations.Deformation P` is an equivariant sheaf morphism

    D × Total(P) → M

whose value at zero is `P.totalMap`. The total sheaf is the actual torsor total
space. The definition requires no global section or trivialization of `P`.
Naturality in the presentation stages belongs to the sheaf morphism; it is not
an additional pointwise continuity assertion.

A quotient arrow acts by precomposition with its inverse torsor map. This gives
the set-valued functor `family a X` on the entire quotient groupoid. The constant
deformation witnesses nonemptiness even for a nontrivial torsor. Quotient objects
live in `Type 1`, while their arrows and deformation sets use the existing small
sheaf-section universe. The source wrapper's explicit universe lifts accommodate
these sizes without resizing.

Restriction along every map `Y → X` pulls back the entire deformation map.
`restrict_id`, `restrict_comp`, and `transport_restrict` prove its laws. These
particular equalities reduce to the chosen split pullback implementation. They
do not identify distinct quotient arrows, including arrows acting ineffectively.

## Boundary and chart comparisons

In the `SmoothQuotientDeformationFiber` module,
`SmoothQuotientDeformations.Fiber P`: the structured-arrow category of quotient
arcs with an actual boundary arrow from `P` to their zero restriction.

A deformation produces such a quotient arc on the pullback of `P`'s torsor.
Conversely, fullness of torsor restriction along zero lifts the given boundary
torsor arrow. This constructs `fromFiber`; `recovery` retains the coherent
boundary isomorphism. Faithfulness of zero restriction proves full faithfulness
of the comparison. `equivalence` therefore applies to every quotient object,
including objects that admit no global chart lift.

`transportComparison` compares deformation transport with forward boundary
transport. It is an isomorphism with a boundary triangle, not an equality of
quotient objects. `fiberRestriction` and `comparison_restrict` retain the boundary
under every sheaf-parameter map.

On a chart lift, `chartEquiv` evaluates at the identity of the regular torsor;
its inverse extends an arc equivariantly. `toArc_transport` identifies the result
with `SmoothQuotientTransport.forwardArcTransport`. The quotient convention is
still `m = g·n`, so forward transport uses the inverse label. The action arrow for
an ordinary element `g` has label `g⁻¹`, hence acts forward by `g`.

`source_arc_composition` transports the result of the unchanged source proof
through this equivalence. `SmoothQuotientSource.origin_classical_composition`
then uses `origin_forward_classical` to obtain the composition of the actual
classical manifold derivatives. The comparison with those derivatives uses the
existing coordinate and fixed-lift theorems; it is not definitional equality.

## Family descent and its current boundary

For any locally surjective sheaf map `f : Y → X` and fixed arbitrary quotient
object `P`, `DescentDatum P f` contains a deformation on `P|Y` and the matching
condition on the induced cover of `D × Total(P)`. It assumes no global deformation
or effectiveness witness.

`DescentDatum.descend` uses effective descent of sheaf maps to construct the
global map. Its zero equation follows by cancellation of the total-space cover.
Its equivariance follows by cancellation after adjoining the group parameter.
`descend_restrict` and `descend_unique` establish effectiveness and uniqueness.
This is descent over a fixed quotient object; combining it with quotient-object
cocycle descent and proving closure for generated contexts remains work.

The next interface must supply parameter maps between interpretations of
*generated* contexts and their dependent families, preserving variables,
substitution, identity, and the contextual-J construction used by the source.
The existing `Typed.StructuralMap` maps all semantic contexts strictly between
two models. A restriction of the external quotient/fiber signature does not
immediately give such a map on every arbitrary groupoid context. A suitable
construction needs context-indexed functors or relations, built from base/fiber
restriction through identity formation and context extension, together with
descent closure. This is a semantic construction requirement, not evidence that
a new source rule is necessary.

Proving only naturality of the two evaluated transport endpoints, or uniqueness
of the final discrete equality witness, would not by itself discharge those
context and section obligations. The full issue remains open pending that work,
public coverage/audit integration, fresh validation, and independent review.

## Checked cases and statement review

`Examples.SmoothSourceTransport` retains an ordinary caller with arbitrary
quotient objects, arrows, and deformation. It also checks:

- the doubled-origin quotient torsor with no global chart lift, a source consumer
  over that torsor, and recovery of an arbitrary boundary datum over it;
- the four origin automorphisms and trivial isotropy at nonzero disk points;
- distinct ineffective loops and source-derived identity transport for their
  composition;
- effective deformation descent over arbitrary locally surjective parameters.

Statement review checked quantifier order, zero boundaries, inverse-arrow
orientation, and the distinction between equality of deformation maps and
isomorphism of boundary objects. The nontrivial-torsor case rules out an implicit
global-trivialization premise. The ineffective case checks that transport on a
set-valued tangent fiber does not erase base isotropy. These are known theorem
consumers, not an independent author-productivity trial.

Model-specific work consists of the deformation family, boundary equivalence,
chart comparison, parameter maps, and descent. Reused proof work is the existing
source term, interpreter, and transport/concatenation evaluations. The original
Typed first proof, old Contextual proof and existing ordinary clients remain
unchanged. No #108 preparation or broader modal/properness comparison is included.

Focused development checks and named-root axiom results are recorded in the
external #433 handoff. They are not a fresh full-library build or exhaustive
audit, and no completion of #433 is claimed here.

[#433]: https://github.com/VladimirMarko/conaled/issues/433
