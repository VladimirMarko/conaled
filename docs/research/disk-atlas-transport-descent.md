# Disk transport across a nonconstant frame atlas

[#408](https://github.com/VladimirMarko/conaled/issues/408) constructs transport
by executing local frame-coordinate solutions and overlap transitions on a
witnessed finite subdivision. The resulting full real linear map agrees with
the existing disk path transport. Applying the retained closing arrow then
agrees with `ClosedLift.endomorphism`.

The scope is bounded atlas transport descent for the fixed hyperbolic disk
connection. Independent acceptance belongs to the enclosing implementation
review. This supplies part of the connection-cocycle comparison proposed by
[#310](orbifold-transport-three-presentations.md); it does not establish a full
stack/transport equivalence or arbitrary Morita invariance.

## Independent inputs and local equations

The metric and connection remain those in
[DiskConnection](../../Applications/Orbifold/DiskConnection.lean):

```text
g_z(v,w) = 4 Re(conj(v) w) / (1 - |z|²)²
k(z,u)   = 2 conj(z) u / (1 - |z|²).
```

A native `Segment` supplies the physical curve, velocity, duration, endpoint
proofs, disk membership, and a nonzero scalar solution of its parallel equation.
The existing circle, radial and hold constructors establish those hypotheses.
There is no new arbitrary-curve solver. A `Path` retains its segment list, and
a `ClosedLift` additionally retains its chosen endpoint-to-source action arrow.
These inputs precede the atlas construction; final transport agreement is not
an input field.

[FrameGauge](../../Applications/Orbifold/FrameGauge.lean) uses a smooth complex
frame multiplier `e`, nonzero on the disk, with its actual derivative along
curves. Coordinates point from local coefficients to physical vectors:
`V = e a`. Differentiating gives

```text
a' = -(k + e'/e) a,
a_j = (e_i/e_j) a_i.
```

`decode_parallel` and `encode_parallel` prove these product/quotient-rule
statements. The local factor is the supplied physical factor divided by `e`.
`local_unique` and `local_field_unique` prove uniqueness at the endpoint and
throughout the interval. This recovers an independently specified local ODE,
rather than requiring an equality of final maps as data.

The actual charts are `Re z < 1/2` and `Re z > -1/2`, restricted to the disk.
`disk_chart_open`, `disk_chart_cover` and `disk_chart_proper` prove that both
are proper opens and cover it. The chosen frames are

```text
e_0(z) = (1 - |z|²)/2,
e_1(z) = e_0(z) exp(i Re z).
```

Both are smooth and normalized for the fixed metric (`standard_metric`,
`varying_metric`). Their overlap is `exp(-i Re z)`.
`transition_nonconstant` proves it cannot be constant even on the overlap,
using its derivative at zero. `varying_connection` derives the extra term
`i Re u`; `unchanged_connection_rejected` tests it at `z=0,u=1`.
The frames extend globally, which is an explicit restriction of this first
instance. Both charts and their changing coordinates are still used in the
construction.

## Executed descent and preservation maps

[GaugeConnectionMaps](../../Applications/Orbifold/GaugeConnectionMaps.lean)
specifies a map `J(t)` by its derivative and connection-preservation equation.
It proves that `J` takes parallel fields to parallel fields, then derives the
endpoint square by local uniqueness. The actual overlap is an instance proved
by the quotient rule. Identity and successive maps retain their selected
values; the composition theorem applies the second map after the first.
This interface concerns scalar maps along a fixed segment. It does not claim
a new general nonlinear coordinate-change theorem; the existing
`ParallelTransport.coordinate_transport` owns that separate derivative law.

[ChartedTransport](../../Applications/Orbifold/ChartedTransport.lean) constructs
`Charting s a b` from ordered subintervals and a chart-containment proof for each
piece. Each step executes an initial overlap, the chosen local solution, and
the remaining charted path. The nil case executes the terminal overlap.
Zero-length pieces are admitted. `parallel` constructs local fields meeting
the overlap boundary conditions; `unique` proves the assembled endpoint is
unique. Local field uniqueness also rules out different solutions inside each
piece.

`decode` proves the physical interpretation of this recursive construction.
`independent` compares any two witnessed chartings with the same segment and
times, so it covers subdivision refinement, chart changes, insertion and
removal of zero-length pieces. `overlap_comp`, `overlap_identity` and
`overlap_inverse` handle insertion/removal of transitions at a point. Their
composition order is obtained from `equiv_cocycle`, quantified over typed
linear equivalences between arbitrary real modules, without a commutativity
hypothesis.

An `AtlasPath` supplies such a full charting for each original segment.
`agreement` proves equality with `Path.transport` as real linear equivalences,
and `closed_agreement` proves equality after the original closing arrow.
The type still indexes the original physical path; chart independence does
not identify different curves. `clock_agreement` and `clock_independent`
retain its original duration. The closing label is read from the original
`ClosedLift`, never reconstructed from the endomorphism.

## Checked cases and observations

[AtlasTransport](../../Examples/AtlasTransport.lean) constructs a single-chart
and a genuinely mixed-chart subdivision of the radius-squared `1/5` loop.
Its full-turn transport is `-v`, while a hold at the same point has identity
transport. The examples exercise the universal chart comparison, the
uniqueness-derived overlap square, local-field existence/uniqueness, and
successive connection maps. Holds of durations one and three have equal
transport and different durations. An origin hold closed by `i` observes `i`.

[AtlasIsotropy](../../Examples/AtlasIsotropy.lean) retains the four-element
origin stabilizer and the trivial stabilizer of a nonzero point. It also
constructs actual closing arrows for `C4 × C2`, acting through the first
factor. Here `C2` is the two-element permutation group. Distinct kernel labels
remain distinct arrows while their actual manifold derivatives and charted
frame observations agree. The wrong closing-direction control reverses the
quarter turn and rejects the resulting observation. The construction never
replaces this ineffective action by a free coarse frame space.

`AtlasPath.terminal_frame` connects the full comparison to the existing exact
`Pose.frame` observation for every initial pose with the required base point.
The public example specializes it to the closed origin hold. No numerical
integrator, error theorem or approximation relation changes. No new error-bound
transfer, rounded-machine guarantee, physical runtime or storage claim follows
from this equality alone.

## Relation to existing descent and bundle interfaces

The inspected Mathlib `VectorBundle.LocalFrame` interface describes smooth
section bases and coefficient recovery on open sets. This construction uses
explicit complex coordinates for the trivial real tangent bundle: `frameMap`
is the real linear coefficient-decoding equivalence, and its inverse recovers
coefficients. The metric theorems identify the two selected oriented normalized
frames. No `IsLocalFrameOn` or general principal-bundle instance is claimed.
Mathlib's `CovariantDerivative/Metric.lean` still lists the parallel-transport
characterization as a TODO at the pinned dependency revision. Completing that
general API is not a prerequisite for this scalar comparison.

[SheafTorsorDescent](../../SquareKit/SheafTorsorDescent.lean) has stronger
stagewise data: `Datum` includes identity/cocycle, naturality under all
restrictions and group equivariance. Its compatible family and
`evaluationEquiv` construct and recover the glued torsor fibers.
The local `overlap` laws here are the fiberwise linear counterpart of its
identity/cocycle equations. `Charting.Parallel` adds an ODE along time intervals
and boundary matching; torsor descent alone contains neither obligation.
No sheaf-valued family or naturality adapter from this atlas is constructed,
so its stagewise effective-descent theorem is not silently invoked.

This packaging retains a concrete comparison target for a later smooth
bundle/stack adapter without requiring a new joint model. There is no identified
contradiction with those interfaces. Remaining work is an actual adapter and
its hypotheses, not a claim that the current theorem already supplies it.

## Source correspondence and remaining boundary

The source locators and immutable PDF receipts remain in the
[#310 report](orbifold-transport-three-presentations.md#source-receipts-and-validation).
Schreiber–Waldorf's Definitions 3.1/3.6 and Theorem 5.4 require their smooth local
trivialization/descent conditions. Collier–Lerman–Wolbert use their own smooth
transport condition, with the stack and cocycle results in Theorems 6.4/6.7;
their Remark 3.6 does not prove equivalence of the two smoothness definitions.
This implementation proves neither source theorem. It supplies explicit
ordinary finite-path equations in the same geometric comparison.

Callers still supply admitted native segments and finite cover/subdivision
witnesses. General compactness subdivision, thin-homotopy/sitting-instant
comparison, general presentation descent and arbitrary smooth-curve existence
remain outside the theorem. The clock must remain beside any future thin path
quotient. Higher synthetic source interpretation and external Agda artifacts
retain their separate model and checking boundaries. No external artifact was
replayed for this implementation.

The variable-curvature controls from #310 also remain separate: `f=x²` fails
C4 invariance, whereas radial `f=r²` is invariant. The current construction
uses the fixed hyperbolic coefficient and its native factors. It does not
supply variable-curvature integration or transfer the old error estimates.
