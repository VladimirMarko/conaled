# Checked disk kinetic action and local Legendre laws

Issue #414 implements the bounded analytic client proposed in
[the variational-motion report](variational-orbifold-motion.md). The continuous
kinetic equation agrees with native disk movement. The coordinate-midpoint
action has smooth local Legendre inverses around every diagonal disk pair for
positive time. Its DEL equation is not the exact native recurrence: the samples
`0, 1/2, 4/5` satisfy the exact action's DEL equation but have midpoint residual
`301663232/1540798875` at time step one.

## Derivatives and regularity

The source modules are under
[`Applications/Orbifold/Kinetic`](../../Applications/Orbifold/Kinetic/Differential.lean).
They use the existing complex disk chart as a two-dimensional **real** vector
space. `covector v` is the Euclidean real covector represented by `v`; the
cotangent rotation law checks this identification against rotated tangent
vectors. This is not a complex-holomorphic derivative of the metric.

`Differential` proves real Fréchet derivatives of the actual function
`L(z,v)=2 normSq(v)/gap(z)^2`, where `gap(z)=1−normSq(z)`. The velocity partial
is represented by `4v/gap²` and the position partial by
`8 normSq(v) z/gap³`. `EulerLagrange` differentiates the momentum along a
curve with the specified velocity and acceleration. Its equation is equivalent
to `a = −christoffel z v v` when the gap is nonzero. Applying the existing
`move_velocity` and `move_geodesic` results gives `native_eulerLagrange`.
The existing `move_speed` result supplies the kinetic energy `s²/2`.

`Midpoint` proves the disk membership of midpoint positions and both actual
partial derivatives of
`Ld(h,x,y)=2 normSq(y−x)/(h gap((x+y)/2)^2)`.
`Regularity.mixed_hessian` differentiates that first partial with respect to the
second endpoint at the diagonal, obtaining `−4 I/(h gap(x)^2)`. The full
joint momentum derivatives are also proved, not supplied as record fields.

For `c=4/(h gap(x)^2)`, the Legendre derivatives and their actual inverses are:

| Map | Derivative on `(u,v)` | Inverse on `(a,b)` |
|---|---|---|
| `Fminus(x,y)=(x,−D1 Ld)` | `(u,c(v−u))` | `(a,a+b/c)` |
| `Fplus(x,y)=(y,D2 Ld)` | `(v,c(v−u))` | `(a−b/c,a)` |

`Legendre` packages these as continuous linear equivalences, proves smoothness,
and invokes Mathlib's inverse function theorem. Both resulting open partial
homeomorphisms are restricted to actual disk endpoint pairs. They contain the
diagonal point, have inverse laws and local uniqueness, and their inverse is
smooth at the corresponding phase point. The public
[`KineticLegendre` examples](../../Examples/KineticLegendre.lean) acquire an open
admitted neighborhood and use its inverse to solve the actual phase equation.
No target regularity or existence assumption is smuggled into that client.

## Symmetry and retained observations

`Equivariance` proves kinetic and midpoint-action invariance under unit complex
rotation, equivariance of both momenta and Legendre maps, and preservation of
covector evaluation. C4 specializes these laws through the existing phase
representation. `PhaseRelated` is an ordinary Lean relation between phase
pairs, witnessed by admitted disk endpoints and positive time. Rotation
transports that witness. Both inverse-branch compatibility theorems require the
original endpoint pair and its rotated copy to lie in the chosen respective
branch domains. They do not assert that arbitrary IFT choices are canonically
equivariant.

`ExactDiameter` proves the derivative of `artanh` on `(-1,1)`, then derives the
momenta of the exact action
`E(h,x,y)=2(artanh(y)−artanh(x))²/h`. For positive time and an interior middle
point, its DEL equation is exactly equality of consecutive `artanh` increments.
`NativeComparison` connects `tanh(s*t/2)` to those increments and proves that
this exact action equals the integral of the native kinetic energy over the
time interval. The result also holds for a pose-transformed diameter; the
scalar coordinates name the diameter before that pose transformation.

The checked reference includes rest, signed passage through zero, nonzero
velocity at the apex, and a C4-rotated chosen direction. The direction `d`,
initial pose `p`, and frame vector `w` remain explicit inputs. The frame law
reuses `move_transport`, which was proved from `move_parallel` and the existing
normalized native frame. Neither coarse apex position nor action value alone
selects this incoming lift or frame. The experiment does not change native
turns, holds, or the numerical simulation driver.

## Rejecting controls and limits

`Controls` checks the rational midpoint residual using the proved momentum
formulas. The exact-action increments of the same three points agree. It also
proves actual quartic derivatives for `Ld(x,y)=(y−x)^4`, the unique recurrence
`z=2y−x`, and the failure of an invertible mixed derivative on the diagonal.
Thus uniqueness of recurrence is not used as a substitute for regularity.

Raw formulas are total Lean functions, including division at zero. All physical
inverse branches require `0<h`; zero time fails that admission condition.
Low-level derivative identities sometimes hold on a larger algebraic domain,
but do not enlarge the physical branch contract. The native rest example does
not justify a zero-duration mechanical inverse step.

These are analytic, noncomputable laws. Neighborhood existence gives no
numerically usable radius or certified root finder. Outside a branch's source
or target, its total function values have no asserted inverse meaning. No
symplecticity, Noether theorem, approximation order, long-time energy behavior,
solver error, or descent of newly generated mechanical paths is claimed. The
adoption decision is to retain this separate mechanical relation and its local
regular example alongside the native controlled-motion interface. Degenerate
mechanics remains free to use relations without selected local maps. A numerical
successor needs a concrete consumer and its own solver, error, and selected
path/frame/clock/label specification; this result does not schedule one by itself.
