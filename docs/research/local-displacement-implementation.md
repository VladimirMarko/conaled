# Local displacement with domains, bracketings and alignment

[#413](https://github.com/VladimirMarko/conaled/issues/413) constructs a local
nonassociative disk client from the existing `Orbifold.gyroAdd`. It retains
intermediate domain evidence and selected alignment labels, and compares actual
endpoints and derivatives. The useful shared component is preservation of an
admitted binary expression from a local operation equation. No associativity
law or full timed-path state is required.

## Concrete operation and local branches

[`LocalDisplacement.lean`](../../Applications/Orbifold/LocalDisplacement.lean)
uses `U = {z : ℂ | normSq z < 1/4}`, the open disk of radius one half.
`strict_subdomain` proves it is strictly smaller than the native unit disk.
The native operation is

```text
mu(a,b) = (a+b)/(1+conj(a)*b).
Admissible(a,b) = a in U, b in U, and mu(a,b) in U.
```

`disk_denominator` discharges division safety on admitted operands.
`gyroAdd_contDiffAt` proves joint real smoothness there; complex holomorphic
smoothness in both operands is not asserted because the first is conjugated.
`admissible_open` and `admissible_near_origin` prove a nonempty open set of
admitted pairs, rather than assuming a global closure law. The zero unit laws
and unit-admission laws are checked.

[`Division.lean`](../../Applications/Orbifold/LocalDisplacement/Division.lean)
constructs both division formulas. Left division is `mu(-a,z)`. For right
division, solve `x - (z*b)*conj(x) = z-b`:

```text
rightDivide(b,z) = ((z-b)+(z*b)*conj(z-b))/(1-(z*b)*conj(z*b)).
```

The denominator is nonzero when `b,z` lie in the unit disk. The left/right
branch domains require the input, target and computed solution in `U`.
`left_solve`, `right_solve`, `left_unique` and `right_unique` prove the equations
and uniqueness on their stated domains. Both branch domains are open
neighborhoods of `(0,0)`; explicit nonzero consumers recover the operands of
`mu(1/10,i/10)`. Callers supply membership and alignment evidence. These formulas
and neighborhood proofs are exact mathematics, not a decidable test for real
membership, a certified floating-point inverse, or a terminating root finder.

This operation is named Möbius displacement arithmetic. No new comparison with
a connection exponential or logarithm is claimed. Existing `PoseConnection` and
`TimedMotion` supply stronger path/geodesic contracts; equality of an endpoint
alone does not recover those contracts.

## Parenthesized composition and rejecting controls

[`PartialEvaluation.lean`](../../Applications/Bracketing/PartialEvaluation.lean)
reuses the existing `Bracketing.Tree`. `Tree.Valid` checks every leaf and every
intermediate output. `Tree.eval` retains the tree shape; its raw function is
also defined on invalid trees, but the admitted consumer uses the validity
proof. `Tree.preservation` requires only domain preservation and the local
operation equation on admitted pairs. It derives both the output equation and
validity of the mapped tree. There is no reassociation hypothesis or quotient.
The shared theorem uses predicates and adds no Mathlib dependency to this
previously lightweight tree module.

The [checked controls](../../Examples/LocalDisplacement/Controls.lean) use
`a = 1/10`, `b = i/10`, and the third leaf `a`. Their determinant is nonzero.
Both `(a mu b) mu a` and `a mu (b mu a)` are admitted, but their real components
are respectively `101040101/510301025` and `20/101`. `nonassociative` proves the
outputs unequal from the actual rational complex calculations. These are
constructed controls, not fields of a proposed model record.

For the separate domain control, both leaves `2/5` lie in `U`, but their product
is `20/29`, outside `U`. Thus leaf validity does not suffice. The counterexample
still lies in the full native disk, so it specifically checks the chosen local
domain rather than a singular denominator.

`tree_rotation` instantiates preservation using the proved diagonal C4 equation.
`rotated_left` uses the noncollinear tree, and `rotated_twice` applies the same
theorem to two changes successively. The scalar operation law is proved once;
callers do not repeat it at every internal node.

## Selected alignment, differential and descent

[`Alignment.lean`](../../Applications/Orbifold/LocalDisplacement/Alignment.lean)
defines the endpoint `mu(a, phase(g)*b)` with the relative label `g : C4`.
Its derivative in `b` is obtained from the existing `Pose.hasDerivAt_mobius`
for the actual pose `(a,phase(g))`. It acts on a tangent `v` by

```text
(1-normSq(a))*phase(g)/(1+conj(a)*phase(g)*b)^2 * v.
```

Under independent representative changes `a -> phase(h)*a` and
`b -> phase(k)*b`, the selected alignment changes to `h*g*k^-1`.
`endpoint_relabel`, `aligned_relabel` and `differential_relabel` prove the exact
endpoint/domain/tangent comparison. The derivative equation transforms the
input tangent by `k` and the result by `h`. `alignmentArrow` is an actual action
groupoid arrow with its selected label exposed by `alignmentArrow_label`.

The [ordinary clients](../../Examples/LocalDisplacement.lean) use these functions
directly. At `a=b=1/5`, identity alignment gives endpoint `5/13` and derivative
`150/169`; half-turn alignment gives endpoint zero and derivative `-25/24`.
Both choices are locally admitted. A three-leaf noncollinear client composes
the derivative theorem through its intermediate domain proof.

[`Descent.lean`](../../Applications/Orbifold/LocalDisplacement/Descent.lean)
provides an optional wrapper for fixed selected alignment: `Input g` retains
both representatives and admission, `endpointFunctor` preserves change-of-chart
labels, and `endpointSquare` reuses the existing orbit-square construction.
Descent is under simultaneous relabeling of the admitted pair. It is not an
operation on two independent position quotients. The existing
`QuarterTurn.quotient_addition_values`, `second_inputs_same_orbit` and
`addition_outputs_different_orbits` are retained as checked regression clients.

The existing `AtlasIsotropy` C4×C2 labels provide the ineffective control.
`ineffective_labels_distinct` retains distinct selected labels; their endpoints
and differentials agree because the second factor acts trivially. The old
path-tangent observation is also recovered. Numerical tangent data does not
reconstruct that label. `SmoothOrdinaryIsotropy` supplies the broader ordinary
open-arrow comparison; this endpoint experiment does not duplicate it or claim
its sheaf-level generality.

## Integration decision and remaining scope

Adopt the small tree preservation theorem for parenthesized local clients and
retain direct endpoint/differential use. A direct two-input caller supplies
membership proofs and a selected alignment. A larger admitted tree additionally
supplies intermediate membership; the shared theorem then transports every
such obligation. The optional groupoid wrapper is useful when a caller needs
an orbit map and retained change labels. It is unnecessary for a direct scalar
calculation. These comparisons establish proof reuse, not measured author or
runtime improvement.

The generic interface stores no desired nonassociativity or final preservation
claim: the disk model and controls prove them. It does not expose a universal
loopoid record. No native pose, path, clock, transport, or simulator API changes.
A path-producing command would need its own comparison with the native path
contract. No numerical error bound or new physical dynamics is established.

The model is homogeneous hyperbolic arithmetic. The radial variable-curvature
construction from [#312's report](local-displacement-loopoids.md) is separately
owned by [#415](https://github.com/VladimirMarko/conaled/issues/415), coordinated
with #32/#34. Its actual flow dependence, exponential/log branches and
nonassociativity are not supplied by this result. Full smooth loopoids,
variable-curvature geometry and executable branch acquisition remain outside
this bounded adoption decision; their mere existence does not require another
wrapper or successor ticket.

The implementation and its public examples are included in `SquareApplications`
for integrated compilation and exhaustive proof auditing. All new operations
here are exact, noncomputable real/complex mathematics; no runtime performance
or numerical execution claim is made.
