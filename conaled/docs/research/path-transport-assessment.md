# Constructed path transport

[#44](https://github.com/VladimirMarko/conaled/issues/44) now has an experimental
coordinate construction on the disk, with real-linear transport, connection
comparison, and pose/matrix observations. The original prerequisite assessment
is retained below as the record of the route selection.

## Implemented contract

[`ParallelTransport`](../../Applications/Geometry/ParallelTransport.lean)
constructs the scalar fundamental solution `P(a,b)v=q(b)/q(a)*v` and proves its
parallel equation and uniqueness on a closed interval. Only the differential
equation for a nonvanishing `q` is a caller obligation. Identity, composition,
reversal and uniqueness are proved results, not fields in a transport record.
Its coordinate comparison is stated for arbitrary real normed vector spaces,
with actual first/second derivatives and the Christoffel transformation
formula. It requires constructed source and target solution families and
uniqueness on the admitted domain. A coordinate map must preserve that domain;
no theorem claims existence along arbitrary smooth image paths.

[`DiskConnection`](../../Applications/Orbifold/DiskConnection.lean) uses
`g_z(v,w)=4 Re(conj(v)w)/(1-normSq(z))²` and
`Gamma_z(u,v)=2 conj(z) u v/(1-normSq(z))` in the existing global real disk
chart. [`DiskCurvature`](../../Applications/Orbifold/DiskCurvature.lean) proves
the scale derivative, metric compatibility, torsion-freeness characterization,
uniqueness of the compatible symmetric coefficient, and curvature `-1`.
Curvature is computed from derivatives and quadratic terms of the Christoffel
coefficient through `ConformalConnection.curvatureVector`, with convention
`R(X,Y)Z=nabla_X nabla_Y Z-nabla_Y nabla_X Z` on constant coordinate fields.
Positive definiteness is checked on the open disk. These are coordinate
results, not a newly installed Mathlib Riemannian bundle instance or a new
manifold hierarchy.

[`DiskTransport`](../../Applications/Orbifold/DiskTransport.lean) admits finite
endpoint-indexed words of segments. Each segment has a nonnegative real
duration `T`, a curve and velocity on `[0,T]`, disk-domain evidence, actual
derivatives including smooth endpoint extensions, and a nonvanishing scalar
solution of the connection equation. This certificate admits explicitly
solvable paths without claiming a solver for every smooth curve. Constructors
in [`TransportSegments`](../../Applications/Orbifold/TransportSegments.lean)
supply holds, affine real-diameter segments, and circular arcs of radius
`sqrt(1/5)`. C4 rotations and reversal supply further constructors. Compared
with the assessment's proposed grammar, the implemented circular constructor
uses this fixed radius so that a full turn has exactly `-id` transport. Other
radii or radial phases can be admitted by supplying the same analytic
certificate; they are not supplied constructors here.

Concatenation appends words and adds durations. Reversal reverses segment
order and substitutes `T-t`, with its derivative proved. There is no rescaling
to Mathlib's unit-interval `Path.trans`. Segment clocks are local, and
`Path.ParallelField` requires the field values to match at every joint.
`transport_parallel` constructs such fields and `transport_unique` proves
uniqueness of their terminal value. Norm preservation follows by
differentiating the metric; polarization proves preservation of its bilinear
pairing. Zero-velocity segments have identity transport regardless of their
solution certificate. A positive-duration hold retains its duration.

[`TransportComparison`](../../Applications/Orbifold/TransportComparison.lean)
proves C4 connection preservation and the transport square using #41's actual
`mfderiv`. For the ellipse, both Christoffel coefficients and parallel fields
are expressed directly in ellipse coordinates and compared to the disk using
the derivative of the existing `diskEllipse` diffeomorphism. The endpoint
comparison consumes the reusable comparison theorem and proved uniqueness.
The `Squares.Square` adapter, real-linear ellipse transport, composition, and
preservation of the pushed metric expose the result to callers. The metric
and connection on the ellipse are the coordinate transforms of the disk
ones, not the Euclidean ellipse metric.

[`TransportFrames`](../../Applications/Orbifold/TransportFrames.lean) constructs
a terminal pose from a transported metric-unit frame and proves agreement for
every frame vector with the existing pose and certified-matrix observations.
It does not identify arbitrary motion increments with parallel transport.
`ClosedLift` retains the path and an action-groupoid arrow **from endpoint to
source**. Its observation is `D(closing) ∘ P`; the closing symmetry label is
retained separately and survives the existing disk/ellipse functor.

[`VariableCurvature`](../../Applications/Geometry/VariableCurvature.lean) is a
second consumer of the scalar construction, for `exp(2x²)(dx²+dy²)` on the real
plane. Its coefficient `2x u v` is symmetric and metric-compatible. Vertical
segments use the actual solution `exp(-2 i b t)` at fixed `x=b`, with uniqueness
and metric preservation. The curvature is computed from the coefficient as
`-2/exp(x²)²`, and its values at `0` and `1` are proved unequal. The example
does not assume constant curvature or use disk-specific transport laws.

## Checked applications and limits

[`Examples/PathTransport.lean`](../../Examples/PathTransport.lean) retains the
full `coordinate_transport` specialization to the ellipse with actual first
and second derivatives, the nonconstant radial scale `3/4`, an out-and-back path with duration `1`, a
positive-duration hold, a full curved loop with transport `-id`, quarter-turn
derivatives at the apex and a regular point, the ellipse calculation,
variable-curvature transport, and matrix/frame agreement. A regular quarter
circle has distinct lifted endpoints and closes with the inverse quarter-turn
arrow. An apex hold separately demonstrates identity path transport with a
nonidentity closing symmetry.

All modules are in the public import closure and use the existing foundational
axiom whitelist. The construction is exact and noncomputable. It provides no
numerical integrator, floating-point bounds, general atlas descent, arbitrary
smooth-path existence, or global Mathlib bundle installation. Generalizing
existence beyond supplied scalar solutions still requires the analytic work
identified by the assessment; it is not needed for these admitted paths.

## Historical prerequisite assessment

Section A of [#44](https://github.com/VladimirMarko/conaled/issues/44), assessed
against conaled `871c732bc5774e40ee6bf898fb99259cd8242d43`, Lean 4.35.0 and
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. This checkpoint selects an
explicit segment construction. It does not complete #44 or introduce its
transport interface. The [gyrovector plan](gyrovector-generalizations.md) and
[ordinary manifold comparison](conventional-orbifolds.md) remain the context.

## Metric and connection

Use real coordinates on the open complex unit disk. Write `s=1-x²-y²>0`,
`lambda=2/s`, and `g_z(v,w)=lambda² <v,w>`, with the Euclidean real pairing.
For a general positive conformal scale `lambda=exp(f)`, set `a=grad f` and

```text
Gamma_z(u,v) = <a,u>v + <a,v>u - <u,v>a
nabla_u V = D V[u] + Gamma_z(u,V).
```

This choice follows from metric compatibility and zero torsion. Indeed,
`D g[u](v,w)=2 lambda² <a,u><v,w>`, and expansion gives
`g(Gamma(u,v),w)+g(v,Gamma(u,w))` equal to that derivative.
The coefficient is symmetric in `u,v`. Conversely, subtract two symmetric
compatible coefficients and put `C(u,v,w)=g(B(u,v),w)`. Symmetry in the first
two slots and antisymmetry in the last two imply
`C(u,v,w)=-C(v,w,u)=-C(w,v,u)=C(w,u,v)=C(u,w,v)=-C(u,v,w)`.
Thus `C=0`; nondegeneracy gives `B=0`. This is the coordinate Levi-Civita
characterization, rather than a name assigned to an arbitrary coefficient.
The smooth field product rule extends the constant-field compatibility
identity to arbitrary differentiable fields.

On the disk, differentiating `log(2/s)` gives `a=(2x/s,2y/s)`.
The conformal Gaussian curvature formula is `K=-lambda⁻² Delta f`:
`f_xx=2/s+4x²/s²`, `f_yy=2/s+4y²/s²`, so `Delta f=4/s²` and `K=-1`.
These differential and curvature calculations, and the uniqueness argument
above, are mathematical derivations for the selected route; they are not yet
Lean theorems about a manifold connection. The checked coefficient identities
below are their algebraic prerequisites. Formal differentiation of the scale,
positive definiteness, the uniqueness argument, and the curvature formula
remain proof obligations in #44.

[`ConnectionAssessment.lean`](../../Applications/Orbifold/ConnectionAssessment.lean)
checks `gamma_symmetric` and `gamma_metric` for every real gradient and vectors.
It also proves `pose_frame_norm` using the existing `Pose.frame` and `Pose.unit`:
`g_a(frame(w),frame(w))=normSq(w)`. Thus the factor `1/2` in #39 agrees with
this curvature convention. `Pose.frame_comp` concerns derivatives of motions;
it supplies no parallel-transport theorem along a path.

## Admitted paths and explicit solutions

Select finite words of timed segments, with matching endpoints. Each segment
has a finite real duration `T>0` and parameter `t in [0,T]`. Admit:

- Holds at any disk point.
- Radial segments `c(t)=rho(t) exp(i theta)`, where `theta` is fixed,
  `rho(t)=r0+(r1-r0)t/T`, and `r0,r1 in (-1,1)`.
- Origin-centered circular arcs `c(t)=r exp(i(theta0+omega t))`, with
  `0<r<1` and arbitrary finite real `theta0,omega`.

Segments extend smoothly to a neighborhood of their closed interval inside
the disk. Endpoint bounds give this for radial segments by compactness and
convexity of `(-1,1)`; the circle has constant radius. The whole path is
continuous and piecewise smooth; its derivative can jump at joints. The
parallel equation is imposed on each segment with one-sided endpoint values,
and fields match at joints. The empty word has zero duration. Holds retain
positive elapsed time even though their transport is identity.

Concatenation appends words and adds durations, translating each segment's
local clock. Reversal reverses the word and replaces each segment by
`c(T-t)`: radial endpoints swap, and arcs use `theta0+omega T,-omega`.
No rescaling to a unit interval is needed. A later adapter to `Path.trans`
must prove reparameterization invariance; its half-interval convention cannot
be silently substituted for elapsed time.

The explicit candidates, acting on real tangent coordinates, are:

```text
hold:    P(t)v = v
radial:  P(t)v = (1-rho(t)^2)/(1-r0^2) v
circle:  P(t)v = exp(-i k omega t) v,  k=2r²/(1-r²).
```

The radial coefficient is positive. Circle transport is a rotation, so these
are invertible and preserve the endpoint conformal metrics. For uniqueness,
multiply any parallel field by the inverse scalar/rotation fundamental
solution; the product derivative vanishes. Apply the interval zero-derivative
lemma, then induct over the word. This avoids needing a general ODE existence
theorem. Proving these derivative calculations, uniqueness, the word laws,
and real linear equivalence packaging belongs to section B.

The checked `radial_parallel` and `radial_field_derivative` verify the equation
for `c(t)=(t,0)`, `V(t)=(1-t²)v`. Restricting to `[0,1/2]` gives a nonconstant
admissible path; the endpoint scaling is `3/4`. `circle_coefficient` verifies
that at radius `1/2`, `Gamma(c,c',v)=(2/3) Jv` per radian, where `Jv=(-v_y,v_x)`.
A full turn therefore has candidate transport `exp(-4 pi i/3)`, which is
nonidentity, unlike a hold at the same base point. The full-turn solution,
endpoint equality, and nonidentity proof are still required; the coefficient
check alone is not a holonomy theorem.

## Comparison examples and remaining scope

Quarter turns preserve this segment class, including radial crossings of the
apex. Under the existing real-linear `QuarterTurn.stretch`, admit images of
these segments in the ellipse, with unchanged clocks. For `A=stretch`, use
`g^E_q(v,w)=g_(A⁻¹q)(A⁻¹v,A⁻¹w)` and independently express the coefficient
as `Gamma^E_q(u,v)=A Gamma_(A⁻¹q)(A⁻¹u,A⁻¹v)`. The second derivative of `A`
is zero. For a general coordinate diffeomorphism the concrete preservation
condition is

```text
D phi Gamma(u,v) = D² phi(u,v) + Gamma'(D phi u,D phi v).
```

Together with the chain rule and uniqueness, this yields the desired transport
square. A general comparison must require that the image path is admitted (or
has a constructed solution); this small segment class is not closed under
arbitrary diffeomorphisms. It is closed under C4 and the specified ellipse
comparison. Retain action-groupoid arrows through `coordinateChange` rather
than dropping labels. For a closing arrow `g : c(T) -> c(0)`, the endomorphism
is `Dg_(c(T)) ∘ P_c`; the symmetry and `P_c` are separate data.

For variable curvature, use the same conformal coefficient with `f=x²`,
`lambda=exp(x²)` on the real plane. Then `K=-2 exp(-2x²)`; values at `x=0`
and `x=1` differ since `exp(-2)<1`. Vertical affine segments at fixed `x=b`
have explicit transport `exp(-2 i b (y(t)-y(0)))`. Holds, concatenation and
reversal give a scoped second consumer of the same solution/comparison
contract. `variable_vertical` checks its coefficient through `gamma`.
The exponential solution and a formal curvature calculation proving the
nonconstant assertion remain required by section D.

No substantial new existence theory is needed for this selected route.
Within #44, prove the scale derivatives and Levi-Civita characterization,
segment solutions and uniqueness, duration-preserving word operations,
coordinate squares, frame observations, and the two curvature examples.
Use Mathlib real continuous linear maps/equivalences and the existing semantic
squares; the coordinate pair in the feasibility checks is the ordinary product
vector space, not a new tangent hierarchy. Convert it to the existing complex
real tangent coordinates when packaging transport. No generic connection
record that assumes the requested transport laws is proposed.

If arbitrary smooth paths become required, separate prerequisites would be
(1) a coordinate connection adapter to Mathlib's covariant derivative API,
and (2) continuous-coefficient linear ODE transport on compact intervals,
including parameter dependence and bundle trivialization. Those are proposed
follow-up scopes, not blockers for the segment construction or newly filed
issues. Internal models #36/#38 and general atlases are not prerequisites.

## Checked evidence and statement review

The module is experimental assessment evidence and is in the public import
closure. The algebraic results quantify over all coordinate vectors, rather
than assuming the desired parallel equation. The radial denominator premise
holds throughout the chosen interval and excludes the disk boundary. The
circular premise is inhabited, for example at `(1/2,0)`. Metric compatibility
is explicitly conditional on the derivative of the conformal scale; it does
not claim that an arbitrary gradient defines a compatible metric. The frame
check consumes #39's public frame and its actual unit-phase constraint.
No theorem in this module constructs path transport, curvature, or a manifold
connection. Those distinctions delimit the checkpoint's checked claims.

## Pinned API inventory

Sources in this table are relative to the pinned Mathlib `Mathlib/` directory.
[Browse that revision](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib).
Declaration names and hypotheses were inspected in local source.

| Capability | Exact source and declarations | Hypotheses and consequence |
|---|---|---|
| Connection on a vector bundle | `Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean`: `IsCovariantDerivativeOn` (92), `CovariantDerivative` (366), `ContMDiffCovariantDerivative` (412) | Over a nontrivially normed field, normed model and fiber, charted base, fiber bundle with topological module fibers. The operator takes global sections and returns `Π x, TangentSpace I x →L[𝕜] V x`. Additivity and Leibniz hold on sections differentiable at the point. Regularity is a separate class; the bundled connection alone gives no smoothness. Argument order `cov σ x v` is section, point, tangent vector. |
| Metric compatibility | `Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean`: `CovariantDerivative.derivMetricTensor`, `IsMetricCompatible`, `IsMetricCompatible.mvfderiv_inner_eq`, `isMetricCompatible_iff` | Real inner-product fibers, vector bundle, C1 Riemannian bundle, C1 vector bundle, finite-dimensional model fiber. Compatibility is vanishing of the derivative metric tensor. The inner-product derivative rule requires both sections differentiable at the point; the iff additionally uses a C1 manifold. It is not a theorem about transport. |
| Levi-Civita connection | `Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`: `CovariantDerivative.IsLeviCivitaConnection`, `.uniqueness`, `leviCivitaConnection`, `isMetricCompatible_leviCivitaConnection`, `isLeviCivitaConnection_leviCivitaConnection` | C2 real manifold, finite-dimensional model, Riemannian tangent bundle with C1 metric. A connection is constructed and proved metric-compatible and torsion-free. Uniqueness is pointwise on differentiable vector fields, not equality on arbitrary sections. This file does not provide a transport construction or a regularity instance for its connection. |
| Tangent bundle and chart changes | `Geometry/Manifold/VectorBundle/Tangent.lean`: `tangentBundleCore`, `tangentCoordChange`, `tangentCoordChange_comp`, `TangentBundle.contMDiffVectorBundle`; `Geometry/Manifold/MFDeriv/Tangent.lean` | Tangent coordinate changes have their cocycle law; an `(n+1)`-smooth manifold supplies an `n`-smooth tangent vector bundle. This supports bundle plumbing, not a pathwise connection solver. |
| Local ODE existence | `Analysis/ODE/PicardLindelof.lean`: `IsPicardLindelof` (80). `Analysis/ODE/ExistUnique.lean`: `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` (57) and suffixed `₀` (71) | Real Banach target for existence. `IsPicardLindelof f t₀ x₀ a r L K` requires uniform `K`-Lipschitz dependence on state in `closedBall x₀ a`, continuity in time, uniform norm bound `L`, and `L * max (tmax-t₀) (t₀-tmin) ≤ a-r`. Initial point lies in `closedBall x₀ r`; initial time belongs to the interval. Produces a curve solving the ODE with within-derivatives on that interval. Does not itself prove existence across an arbitrary prescribed path or global time interval. |
| ODE uniqueness | `Analysis/ODE/ExistUnique.lean`: `ODE_solution_unique_of_mem_Icc_right` (194), `_left` (209), `ODE_solution_unique_of_mem_Icc` (252) | Normed real target, no completeness requirement. Uniform state Lipschitz bound on time-dependent domain; both curves remain in domain and are continuous on closed interval; derivative equations and equal initial value. The interior-time version assumes initial time in `Ioo a b` and ordinary derivatives on the interior. Endpoint version instead uses one-sided within derivatives. |
| Integration and FTC | `MeasureTheory/Integral/IntervalIntegral/Basic.lean`: `intervalIntegral.integral_symm` (684), `integral_add_adjacent_intervals` (1095). `.../FundThmCalculus.lean`: `integral_hasDerivAt_right` (725), `integral_eq_sub_of_hasDerivAt` (1148), `integral_eq_sub_of_hasDerivAt_of_le` (1140). `Analysis/ODE/PicardLindelof.lean`: `ODE.picard` (106), `hasDerivWithinAt_picard_Icc` (485) | Bochner integration in normed real spaces, with Banach hypotheses where FTC requires them. Adjacent integral composition requires interval integrability on both pieces. FTC2 requires derivative equation and interval-integrability of derivative; the `_of_le` variant needs continuity on closed interval and derivatives only in interior. These are suitable for the integral form of the fiber ODE after trivializing. |
| Paths | `Topology/Path.lean`: `Path` (60), `Path.refl`, `.symm`, `.trans`, `.trans_symm`, `.reparam` | `Path x y` is a continuous map from unit interval with endpoints. Concatenation rescales time by 2 on each half. It does not carry C1 or piecewise-C1 data. Reversal/concatenation can be reused as underlying continuous paths, but regularity and derivative transformation must be proved separately. |

The bounded negative search was case-insensitive `parallel.?transport|ParallelTransport|Christoffel|covariant.*along|connection.*along` over `Mathlib/Geometry` and `Mathlib/Analysis/ODE`. Its only matches were the TODO in `CovariantDerivative/Metric.lean:34-36`, explicitly requesting a future parallel-transport notion and its isometry characterization. Thus no reusable pathwise transport/Christoffel API was found in the inspected relevant directories. This does not assert absence under every possible spelling elsewhere in Mathlib.

## Local interfaces

`Applications/AD/Core.lean` supplies `DMap`, `tangent`, `tangent_correct`, `tangent_comp`: genuine Fréchet derivatives and tangent mapping under composition, useful for coordinate derivatives but not a connection or time evolution.

`Applications/Orbifolds/Equivariant.lean` supplies `CoordinateChange`, `CoordinateChange.groupoidEquivalence`, `stabilizerEquiv`, `quotientEquiv`, and equivariant orbit maps. `Applications/Orbifolds/SmoothComparison.lean` supplies `manifoldCoordinateChange`, `manifoldQuotient`, and `tangent_intertwining`. These cover equivariance and tangent compatibility of coordinate changes, not connection descent or path lifting at isotropy.

`Applications/Orbifold/Pose.lean` supplies exact disk Möbius pose algebra, and `Applications/Orbifold/MatrixDisk.lean` supplies `hasDerivAt_mobius`, `frame_agreement`, and `product_derivative`. Those are derivatives of spatial transformations and frame actions. They do not identify a frame update with the solution of a Levi-Civita parallel equation. `Applications/Orbifold/ProjectiveMotion.lean` supplies Hermitian-similitude actions and preservation of `ratio`; that invariant is not a defined positive Riemannian bundle metric.


The ODE route offers a larger eventual path class, but needs state bounds,
finite-interval continuation, and differentiation along paths. The explicit
route proves existence by formulas and uniqueness by an integrating factor;
it trades that analytic infrastructure for a restricted segment grammar.
Mathlib already constructs Levi-Civita connections. Reuse its characterization
and uniqueness when installing the disk Riemannian metric; do not create a
second manifold connection hierarchy. Its current construction alone does
not discharge the pathwise or regularity obligations above.

## Timed command construction checkpoint for #47

Assessed against conaled `bf9b9e596df756faec5fecabfc592edb85d606c0`,
Lean 4.35.0 and the Mathlib revision pinned above. The assessment inspects
`Pose`, `DiskTransport`, `TransportSegments`, `TransportComparison`, and
`TransportFrames`, together with Mathlib's `DerivHyp`, `ContDiff/RCLike`,
and `ODE/ExistUnique` APIs. This is a construction checkpoint, not completion
of [#47](https://github.com/VladimirMarko/conaled/issues/47).

For a unit complex direction `d` and real signed speed `s`, set
`r(t) = tanh(s*t/2)`. The base pose has position `d*r(t)` and phase `1`.
Its frame sends `w` to `(1-r(t)^2)*w/2`, so its body velocity is `d*s`.
The derivative `r' = s*(1-r^2)/2` gives the velocity equation and the
parallel-frame equation for the existing curvature -1 connection. Mathlib's
`Real.tanh_sq_lt_one` gives disk validity for every real time; therefore
any finite nonnegative duration is admissible. The factor `1/2` follows
from `Pose.frame`. The affine radial constructor from #44 cannot supply
this constant metric speed without a proved change of clock.

For an initial pose `p`, compose `p` on the left of this base pose. Its
position is `p.mobius` applied to the base position. `Pose.gyro_gap` and
`Pose.act_denominator` establish disk validity and exclude poles. The new
analytic obligation is the derivative of `Pose.derivative` and the identity
`D²phi(v,w) + Gamma(phi)(Dphi(v),Dphi(w)) = Dphi(Gamma(v,w))`.
`Pose.frame_comp` alone does not discharge it. A scratch construction checked
the hyperbolic derivative, diameter velocity and frame equations, and this
Möbius identity before choosing a command interface.

Turning at fixed position uses phase `p.u * exp(i*omega*t)`. A hold uses the
constant pose. Both exist for all real times. A turn has identity path
transport, while its frame obeys the prescribed angular equation. Finite
words must retain these local clocks and their developed paths, including
positive-duration holds. Representative changes multiply both position and
phase by the same C4 scalar; body controls stay fixed.

Existence can therefore use explicit formulas. Uniqueness needs a separate
argument for the coupled position/frame equation. `Segment.field_unique`
only covers a fixed supplied path. In coordinates `(z,h)` with `h=u(1)`, the
coupled vector field is `(h*v, -coefficient(z,h*v)*h + h*i*omega)`. It is
smooth on the open disk times the frame-coordinate plane. The pinned
`ContDiffOn.exists_lipschitzOnWith` and
`ODE_solution_unique_of_mem_Icc_right` provide a route on compact convex
subdomains away from the disk boundary. Continuity on a finite closed
interval must justify containment for any solutions compared. No global
ODE existence assumption or new bundle hierarchy is needed for this route.

## Timed command interface and proof scope

The experimental [timed commands](../../Applications/Orbifold/TimedCommands.lean)
construct `Control.move v`, `Control.turn omega`, and `Control.hold` from any
existing `Pose`. A `Command` adds a real duration and its nonnegativity proof.
Callers supply no differential-equation certificate. Complex numbers represent
real tangent coordinates; multiplication by `i*omega` is the positive planar
skew operator. Public move controls accept every complex vector, including
zero. Internally the velocity is split into its Euclidean norm and unit
direction, with direction `1` chosen for the zero vector. Pose composition
places the initial pose on the left of the time-dependent base solution.

`Control.position_equation` and `Control.frame_equation` state the two governing
equations using actual real-time derivatives. Pose fields prove disk validity
and unit phase at every real time. `frame_metric` and `frame_pair` give the
metric-unit frame and its real inner-product law. `control_move_geodesic` and
`control_move_speed` prove zero covariant acceleration and constant squared
metric speed `normSq v`. `command_move_transport` connects that frame to the
constructed #44 segment on the actual clock. A turn's position path is a hold;
`spin_half_turn` proves its rotating frame can differ from identity path
transport.

[`Control.unique`](../../Applications/Orbifold/MotionUniqueness.lean) compares
any pose-valued solution on `[0,T]` with the constructed trajectory. Competing
solutions must have the stated actual position and frame derivatives on the
closed interval, interpreted through extensions at endpoints, and the same
initial pose. This implies the continuity needed by the uniqueness theorem.
The implementation derives compact bounds away from the boundary for both
solutions; callers need not choose bounds or prove Lipschitz continuity.
This theorem includes `T=0`. It does not assert uniqueness for discontinuous
paths or equations imposed only almost everywhere.

`execute` folds commands in list order, starting each at the preceding framed
endpoint. `develop` retains the certified position path, while `trace` retains
the duration and entire framed trajectory of each local clock, including
turns. Observe each local trajectory on `[0, command.duration]`. The append
laws prove state composition, trace concatenation, transport composition, and
addition of elapsed time. Zero-duration commands have identity endpoint and
transport observations; the recorded zero-duration segment need not equal an
empty trace. Positive-duration holds retain their elapsed time.

[`CommandComparison`](../../Applications/Orbifold/CommandComparison.lean) uses
the existing C4 pose action to transform position and frame together. The
same body controls commute with representative changes at every local time,
through the whole trace, and through developed transport. `executionFunctor`
retains the action-groupoid label and source/target evidence. This symmetry
arrow is separate from the physical command list. Matrix observations agree
with frames both for the canonical pose matrix and for every certified matrix
decoding to the same motion. These results use analytic connection
preservation for moves; they do not identify arbitrary pose increments with
parallel transport.

[Checked examples](../../Examples/TimedMotion.lean) include a nonconstant move
reaching the apex at an interior local time, a regular-point representative
change, a move–turn–move sequence, a positive-duration hold, uniqueness, and
pose/matrix agreement. The position-only representative-change example checks
that the point is correct but the initial velocity is wrong when the attached
frame is left unchanged.

The construction is exact and noncomputable. The
[rational Euler realization](numerical-motion.md) now implements a bounded
class of these commands with proved position/frame error, domain checks,
finite-command composition, and C4 compatibility. Discretization error and
exact rational arithmetic have separate contracts. Simultaneous translation
and turning, time-dependent controls, force laws, and atlas descent remain
outside this interface.
