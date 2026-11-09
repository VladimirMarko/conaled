# Exact Lorentz realization of framed disk motion

Implemented for [#411](https://github.com/VladimirMarko/conaled/issues/411),
following the [#313 representation comparison](lorentz-clifford-realizations.md).
This is an exact alternative representation and composition consumer. It does
not replace the numerical simulator backend.

## Carrier and input obligations

[Applications.Orbifold.Lorentz](../../Applications/Orbifold/Lorentz.lean)
constructs real 3×3 matrices with time coordinate first and metric
`J=diag(−1,1,1)`. `encode p` is the explicit `B(p.a) R(p.u)` from the
research report. The boost and rotation entries are defined directly;
identity, determinant 1, form preservation, and the positive first time
coordinate are proved.

The named carrier **`Realized` is restricted to the image of this encoding**.
It is not defined as every matrix satisfying the three Lorentz conditions.
No theorem here classifies all of `SO⁺(2,1)` or proves that those conditions
alone supply image membership. On this named carrier both decoding round
trips are proved. This restriction was permitted by #411 and must remain
visible when the carrier is reused.

A native certified `Pose` supplies an initializer through
`Realized.ofPose`. A caller starting with an arbitrary real matrix supplies
an image witness, for example by proving its equality with an independently
computed `B(a)R(u)`. The literal matrix clients below do that. Image membership
is a proposition, not a numerical validator, and the formulas over Lean's
reals and complexes are noncomputable. There is no floating-point acquisition,
precision, runtime, or approximate-validity claim.

The carrier's evidence contains no assumed operation-comparison theorem.
Decoding uses the matrix's entries rather than selecting its image witness.
The witness discharges the coordinate domain and normalization obligations;
ordinary clients do not repeat those proofs.

## Independently calculated operations and comparison

`point A` projects the first column by stereographic projection:
`(A₁₀+i A₂₀)/(A₀₀+1)`. `frame A w` applies its differential to the
linear combination of spatial columns specified by arbitrary complex `w`.
It therefore observes the entire oriented frame, not only a chosen tangent.
`turn A` recovers the unit phase from that frame's scale. The checked laws
`point_encode` and `frame_encode` recover native `p.a` and `p.frame w`, and
`Realized.decode_ofPose`, `encode_decode`, and `ofPose_decode` supply the
round trips.

Composition is ordinary real matrix multiplication. Its closure and
`decode_comp` follow from the proved `encode_comp`. The latter is not a
transported definition of multiplication: it uses the independently
calculated intertwining of real boosts/rotations with Hermitian 2×2
coordinates, then reuses `Pose.matrix_comp` and `Pose.gyro_gap` to prove the
normalization law. `encode_preserves` is proved from the real entries, not
assumed from native motion correctness.

Inverse is the real matrix expression `J Aᵀ J`. `inverse_encode`,
`inverse_mul`, `mul_inverse` and `Realized.decode_inv` prove its closure,
two inverse laws and native comparison. The scalar inverse pose is
constructed as `(-conjugate(u)a, conjugate(u))`; its unit and disk evidence
are proved.

For arbitrary valid disk `z`, `pointAction A z` observes the first column of
`A * B(z)`. `frameAction A z v` transports an arbitrary tangent `v` through
the rotation-free input frame, applies the same real product, and observes
the result with the stereographic differential. The input scale is
`2/(1−|z|²)`. The proved comparisons are:

```
pointAction (encode p) z = p.act z
frameAction (encode p) z v = p.derivative z * v.
```

`pointAction_inside` and `Realized.act` return a certified disk point without
caller denominator proofs. `Realized.future_column` and
`pointAction_future` show that the relevant columns lie on the actual future
unit hyperboloid, `−X₀²+X₁²+X₂²=−1`, `X₀>0`.
`Realized.act_comp`, `frameAction_comp`, and their identity/inverse laws
establish composition of these actions. The frame action is a motion
derivative; it is not parallel transport along an independently supplied
trajectory.

Finite lists use a fold of the actual real products. The empty list uses the
real identity matrix. `composeList_matrix`, `decode_composeList`,
`finite_point` and `finite_frame` compare every admitted list with the native
pose fold. `finite_pointAction` and `finite_frameAction` extend the comparison to
arbitrary initial disk points and tangents. `composed_frame` reuses
`Pose.frame_comp`, retaining all complex frame directions.

## Consumers and controls

[Examples.LorentzMotion](../../Examples/LorentzMotion.lean) constructs literal
real matrices independently of the encoder and proves their admission once.
The examples then consume the public operations and comparison theorems:

- The noncommuting poses `(1/3,i)` and `(i/4,(3+4i)/5)` give product point
  `1/11` and full frame `((-48+36i)/121)w`. The first matrix is
  `[[5/4,0,−3/4],[3/4,0,−5/4],[0,1,0]]`, whose frame is `4iw/9`.
- Both inverse products are identity. Arbitrary finite products and the empty
  list exercise the same public consumer.
- An apex quarter-turn has frame `iw/2`. A quarter-turn representative change
  changes the nonzero point and frame; right body increments remain
  equivariant by the existing native law.
- The selected closing label is kept alongside the matrix. Existing
  `AtlasIsotropy` labels differing in their ineffective factor have equal
  geometric matrices but unequal retained labeled results. The existing
  `QuarterTurn.increment_label` remains the arrow-label law.
- `−I` preserves the form but is rejected by its time coordinate. The
  reflection `diag(1,1,−1)` also preserves the form but is rejected by its
  determinant. These controls test distinct validity conditions.
- The first matrix has Klein coordinate `3/5`, while its Poincaré point is
  `1/3`; the two projections are not interchangeable.

The example's `compositionSquare` decodes into the existing
`Motion diskForm` semantics and synchronizes with the existing
`DiskRealizations.poseCompositionSquare`. Its `finite_motion` reuses
`Pose.motion_composeList`. This keeps the established meaning comparison
available alongside direct point/frame observations. Callers can continue to
use ordinary Lean poses or independently represented valid matrices; neither
interface is made mandatory for the other.

## Remaining boundaries

There is no full Lorentz-group classification, spin cover, executable real
matrix validator, rounding analysis or performance comparison in this change.
The independent Clifford experiment #412 shares the point/frame contract;
it need not import this module unless it chooses to consume these results.
The #313 probe remains bounded empirical evidence rather than certification
of this representation.

A numerical successor requires an actual consumer and matched point/frame
error and failure contracts for acquisition, conversion, composition and
decoding. Exact comparison alone does not authorize backend adoption or a
new generalization ticket. Variable-curvature transport, atlas coherence and
selected symmetry labels retain their existing owners and interfaces.
