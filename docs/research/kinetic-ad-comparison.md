# Local AD for the disk midpoint action

Issue [#541](https://github.com/VladimirMarko/conaled/issues/541) connects the
existing analytic AD operations to the independently proved disk midpoint
derivatives and local Legendre inverses. The checked consumers are in
[Examples/KineticAD.lean](../../Examples/KineticAD.lean).

## Admission at an observed point

The midpoint action is `2 * normSq(y-x) / (h * gap(midpoint x y)^2)`.
Its denominator vanishes outside the admitted domain. Lean's total division
does not make it globally smooth. The existing `DMap.ofSmooth` and
`AD.SecondOrder` interfaces retain their global assumptions unchanged.

[AD.SecondOrderAt](../../Applications/AD/SecondOrderAt.lean) uses the same
semantic tangent operation and iterates it. First-order composition requires
differentiability at the observed point; second-order composition requires
local smoothness there. The proof uses nearby first-order chain rules and
equality of derivatives of functions that agree on a neighborhood. It does
not require a globally smooth extension. `lift_global` and `twice_global`
recover the existing operations exactly under their original assumptions.

This uses Mathlib's native local calculus. An alternative `ContDiffOn` route
would need an open-domain premise to recover ambient derivatives and domain
mapping obligations at composition. That would suit uniform domain claims.
The selected observations here are at admitted points, so the interface retains
pointwise premises and discharges them from the disk domain where needed.
No new smooth-map record or change to the compiler's global contract is needed.

## The actual action and derivative observations

`actionParts` constructs the globally smooth numerator and denominator pair;
`quotient` divides them. `action_compositional` and
`action_twice_compositional` identify first and iterated tangent evaluation of
the actual midpoint action with composition through those operations. Their
premises retain both nonzero timestep and nonzero midpoint gap.

`firstMomentum` and `secondMomentum` reconstruct complex vectors from the AD
outputs in directions 1 and I. Their equality to the independent `d1` and `d2`
uses uniqueness of the derivatives already proved in `Kinetic.Midpoint`.
`directional_first` connects the joint action's tangent to the first endpoint
covector. The equality holds on the admitted neighborhood before it is
differentiated again.

`action_mixed_second` and `action_twice_mixed` recover the mixed observation
of the actual twice-lift: `-diagonalScale h x * covector u v`. The first seed
varies the first endpoint; the transverse seed varies the second endpoint;
the mixed seed is zero. Thus the observed component contains no additional
first-derivative contribution. The independent origin calculation gives -4
for timestep 1 and unit directions.

The recovered Legendre maps have the existing invertible diagonal derivative
blocks. Their selected branches are the original `minusBranch` and
`plusBranch`, retaining positive timestep, endpoint-domain membership,
inverse and uniqueness laws, and smooth inverse observations. A concrete
origin case proves branch membership and uses the AD-derived observation in
its inverse law. These results supply no numerical radius or executable
inverse solver.

## Quartic separating case

`quartic_twice_compositional` uses the existing global `SecondOrder.twice_comp`
on subtraction followed by fourth power. `quartic_twice_mixed` identifies its
mixed output with the independent coefficient `-12*(y-x)^2`; the off-diagonal
case at `(0,1)` gives -12. At the diagonal the output is zero, and
`quartic_diagonal_control` retains the independently proved failure of an
invertible mixed derivative. `quartic_recurrence_control` retains uniqueness
of the discrete recurrence separately. Uniqueness does not discharge the
regularity obligation.

## Caller obligations and recommendation

Retain this bounded local extension. It shares tangent iteration, the local
composition proof and recovery of second derivatives from neighborhood
observations, while agreeing with the global API on its existing inputs.
The midpoint action needs the local admission law; the quartic action continues
to use the simpler global route. Both exercise the same derivative semantics.

A caller still supplies the action factorization, local denominator admission
and independent mathematical observations. The local laws require smoothness,
although the first-order comparison itself only requires differentiability.
Complex covector reconstruction and selected branch domains remain specific
to this application. The direct proofs remain useful independent references;
this experiment adds comparison and reuse, not a shorter replacement for every
existing proof.

The benefit demonstrated here is reusable mathematical composition at admitted
points. This is not an author-usability trial, a runtime comparison, an
executable AD compiler for reciprocal operations, or evidence for replacing
all global interfaces with local ones. The broader architectural assessment
remains owned by [#235](https://github.com/VladimirMarko/conaled/issues/235).

## Statement review and validation scope

The changed claims retain the actual functions and selected branches.
Neighborhood equalities justify differentiating recovered observations; no
pointwise equality is silently promoted to derivative equality. The origin,
off-diagonal quartic and degenerate diagonal cases exercise the public results
with independent expected values. No existing kinetic theorem is weakened.

These modules are imported by `SquareApplications` and are subject to the
repository's full candidate build, exhaustive axiom audit and independent
Standards and Spec review. Acceptance receipts identify the exact reviewed
commit; a focused development build alone is not acceptance evidence.
