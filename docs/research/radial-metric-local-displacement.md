# Local displacement for the radial metric

[#415](https://github.com/VladimirMarko/conaled/issues/415) constructs the local
operation for `g = exp(2|z|²)(dx² + dy²)` proposed in the
[loopoid comparison](local-displacement-loopoids.md). The Lean construction has
an actual selected flow, local inverse branches, local divisions, and a positive
nonassociative client. Its exponential, logarithm, displacement and associator
have proved fifth-order remainder bounds. Independent acceptance of the final
candidate is recorded outside this report.

## Fixed connection and time-one flow

[RadialMetric](../../Applications/Geometry/RadialMetric.lean) represents the real
Euclidean plane by `ℂ`, with an explicit real-coordinate map `coords`. The
positive frame scale is `exp(|z|²)`; `metric_factor` identifies its square with
the specified metric factor. The coefficient is

```text
Γ_z(u,v) = 2 conj(z) u v.
```

`gamma_coords` identifies this with `ConnectionAssessment.gamma` at gradient
`(2x,2y)`. Symmetry and metric compatibility reuse `gamma_symmetric` and
`gamma_metric`; `scale_directional` proves the actual directional derivative
needed by that compatibility identity. The real-coordinate acceleration is
`−4⟨z,v⟩v + 2⟨v,v⟩z`. The coefficient and metric scale are C4-equivariant.
The earlier conformal example depending only on `x²` is not used as this metric.

[RadialFlow](../../Applications/Geometry/RadialFlow.lean) uses the invertible
velocity rescaling `w = 2v`. The equivalent first-order field is

```text
H(z,w) = (w/2, −conj(z)w²).
```

On the product-norm closed ball of radius `1/4`, its norm is at most `1/8` and
its Lipschitz constant is at most `1/2`. Mathlib's Picard construction gives a
retained selected curve for every initial weighted state of norm at most
`1/16`, on `[-5/4, 5/4]`, staying in that coordinate ball. In original
coordinates this admits `|z| ≤ 1/16`, `|v| ≤ 1/32`. `geodesicFlow_deriv` recovers
the original second-order geodesic field. `boundedFlow_unique` proves uniqueness
on the admitted interval among solutions with the stated bound.

The total function `boundedFlow` uses the Picard curve's clamped extension.
Its ODE theorem is restricted to the admitted time interval. The nonzero
[flow client](../../Examples/RadialFlow.lean) has initial velocity `1/64` and
checks the differential equation and bound at time one.

## Initial-data dependence and inverse branches

The proof of initial-data dependence uses a Banach-space implicit function
theorem for the fixed polynomial integral equation. This replaces the proposed
variational-equation estimate from the implementation preflight; it proves the
needed dependence rather than adding it as a hypothesis.

Let `J` be integration from zero on continuous paths over `[0,1]`. For initial
weighted state `p` and paths `(z,w)`, the residual is

```text
R(p,z,w) = (z − const(p.z) − (1/2)Jw,
            w − const(p.w) + J(conj(z)w²)).
```

[RadialVariation](../../Applications/Geometry/RadialVariation.lean) constructs
`J` as a bounded real-linear map, proves the residual smooth, and proves its
path derivative at zero is the invertible triangular map
`(z,w) ↦ (z − (1/2)Jw,w)`. The implicit function gives `solutionPaths` and its
actual residual equation near zero. [RadialDependence](../../Applications/Geometry/RadialDependence.lean)
derives its time ODE by the fundamental theorem of calculus and identifies it
with the selected bounded Picard solution by uniqueness. Initial-data
smoothness is therefore separate from differentiability in time.

[RadialExponential](../../Applications/Geometry/RadialExponential.lean) obtains
a smooth germ `expMap(x,v)` whose derivative at zero is `(δx,δv) ↦ δx + δv`.
The velocity derivative is identity. `Admitted` retains the weighted initial
bound, path bound and residual equation used to identify it with actual flow.
The total choice-backed definition makes no flow assertion outside that domain.

[RadialBranches](../../Applications/Geometry/RadialBranches.lean) applies the
inverse function theorem to `(x,v) ↦ (x,expMap(x,v))`, whose derivative has
inverse `(δx,δy) ↦ (δx,δy−δx)`. The resulting partial homeomorphism is restricted
to the interior of `Admitted`. Its source and target contain zero, and all
exponential/log inverse laws retain source or target membership. A
[positive-velocity client](../../Examples/RadialExponential.lean) proves that
the branch admits more than the rest state.

## Displacement, division and selected symmetry

[RadialDisplacement](../../Applications/Geometry/RadialDisplacement.lean) defines

```text
originLog(y) = Log_0(y)
radialParallel(x,v) = exp(−|x|²)v
μ(x,y) = expMap(x, radialParallel(x, originLog(y))).
```

`DisplacementDomain` requires the actual origin-log target and the source of
the final exponential branch. It contains a neighborhood of `(0,0)`.
Both units and the derivative `Dμ_(0,0)(δx,δy) = δx + δy` are checked.

[RadialAngular](../../Applications/Geometry/RadialAngular.lean) proves that
`Im(conj(z)w)` vanishes along the selected origin geodesic, by a scalar ODE
uniqueness argument. It then verifies `exp(−|z(t)|²)v` as the parallel field
along that same geodesic, with its initial value, uniqueness and endpoint
`radialParallel(y,v)`. A straight radial parameter is not identified with
affine geodesic time. The [displacement client](../../Examples/RadialDisplacement.lean)
retains the selected log and flow witnesses in this comparison.

[RadialDivision](../../Applications/Geometry/RadialDivision.lean) constructs
separate local inverse branches of `(x,y) ↦ (x,μ(x,y))` and
`(x,y) ↦ (y,μ(x,y))`. Each supplies a solution and uniqueness on its own source,
restricted to `DisplacementDomain`. These neighborhoods are not asserted closed
under arbitrary repeated multiplication.

[RadialSymmetry](../../Applications/Geometry/RadialSymmetry.lean) derives flow
covariance from field covariance and uniqueness. Exponential covariance then
passes through inverse-branch uniqueness to displacement. `RotationDomain`
retains membership of the rotated logarithm in the same branch. The finite
intersection `C4Domain` contains a neighborhood of zero and permits each chosen
C4 alignment. The group element remains an argument of `displacement_c4`.
This does not supply multiplication of independently represented coarse points.

## Actual nonassociativity

[RadialRemainder](../../Applications/Geometry/RadialRemainder.lean) derives an
exact fixed-point equation from the residual. Smooth dependence first gives a
linear norm bound for the selected paths. Cubic multiplication gives a cubic
deviation from the linear path; substituting that deviation back into the
cubic term gives a fifth-order remainder. [RadialTaylor](../../Applications/Geometry/RadialTaylor.lean)
evaluates the actual Volterra integrals and restores the original velocity:

```text
Exp_x(v) = x + v − conj(x)v² − (1/3)conj(v)v² + O(‖(x,v)‖⁵).
```

[RadialLogRemainder](../../Applications/Geometry/RadialLogRemainder.lean) uses
the actual inverse law to prove the origin-log remainder.
[RadialDisplacementRemainder](../../Applications/Geometry/RadialDisplacementRemainder.lean)
also uses Mathlib's exponential-series remainder for the parallel factor, giving

```text
μ(x,y) = x + y − conj(x)y² − |x|²y + O(‖(x,y)‖⁵).
```

[RadialNonassociative](../../Applications/Geometry/RadialNonassociative.lean)
uses `x=t`, `y=z=tI`. Its actual associator satisfies

```text
μ(μ(t,tI),tI) − μ(t,μ(tI,tI)) = −2t³ + O(|t|⁵).
```

`associator_nonzero_near` proves nonvanishing for sufficiently small positive
`t`. `positive_nonassociative_client` provides such a positive `t`, both unequal
values, and all four intermediate `DisplacementDomain` witnesses. Thus the
coefficient calculation is connected to the constructed operation through
proved error bounds and nonempty domains. No curvature-to-loop theorem is
assumed.

## Endpoint, path and label observations

[RadialTransport](../../Applications/Geometry/RadialTransport.lean) solves the
circle equation for `z(t)=r exp(tI)`:

```text
V(t) = exp(−2r²tI)V(0).
```

The [transport client](../../Examples/RadialTransport.lean) chooses `r=1/4`,
duration `2π`, and identity closing label. The circle and hold have the same
endpoint and closing label, but their transport maps differ on vector `1`.
The differential equation is verified for every initial vector. At the origin,
a quarter-turn closing symmetry fixes position and rotates the tangent. The
existing `SmoothQuarterTurnArcs.ineffective_distinct_labels` theorem is reused
as a separate-family control: labels can remain distinct even when that family's
action is identical. The radial tangent action is not declared ineffective.

## Reuse, validation and limits

The construction uses the pinned Mathlib Picard/ODE uniqueness, implicit and
inverse function, continuous-linear-map, interval-integral and asymptotics APIs.
Its local proofs reside in the modules linked above. All examples enter through
`SquareApplications`; the README candidate command checks public coverage,
compilation and the exhaustive project axiom audit. Statement-review and exact
candidate validation receipts accompany the candidate outside the repository.
No Lean admission, extra axiom or audit exception is introduced.

The analytic branches and positive witnesses are noncomputable choices.
Existence of a neighborhood is not an algorithm for acquiring its radius or
executing its inverse. This work proves no global smooth loopoid, gyrogroup,
numerical exponential solver, variable-curvature simulator backend, or
independent coarse-representative arithmetic. The fixed metric provides an
additional local geometry; it does not replace the hyperbolic transport or
[atlas-descent construction](disk-atlas-transport-descent.md).
