# Variational motion on the quarter-turn cone

This report completes the research deliverable for #311. Its recommendation is
**investigate a separate mechanical client**: free inertial motion on the
hyperbolic disk modulo quarter turns, discretized upstairs and descended with
explicit symmetry. The mathematical calculations below are not Lean theorems.
The existing timed-command and numerical implementations remain unchanged.
Independent acceptance of this report is pending.

## Physical question and state

Let D be the unit disk, with metric
`g_z(u,u) = 4 |u|² / (1 − |z|²)²`. The physical question is the motion of a free
unit-mass particle, with kinetic Lagrangian

`L(z,u) = 2 |u|² / (1 − |z|²)²`.

Its Euler–Lagrange equation is
`z̈ + 2 conj(z) ż² / (1 − |z|²) = 0`. There is no applied force, collision
rule at the cone point, or prescribed change of velocity. This choice precedes
the choice of numerical integrator.

Represent an observed state upstairs by `(z,e,v)`, where `e` is an oriented
metric-unit frame, `v : ℂ` is body velocity, and `ż = e v`. Parallel transport
of `e` and constant `v` express this free motion. The frame records an
observation convention; it is not an independent rotor with angular inertia.
For a quarter turn `g`, the transformation is
`(z,e,ż) ↦ (g z,g e,g ż)`, leaving `v` unchanged. The corresponding cotangent
lift acts on momentum. At `(z,p)=(0,0)` the phase point has C4 stabilizer; a
nonzero momentum removes that effective stabilizer. Frame and lift labels can
still distinguish observations of the same quotient trajectory.

On a real diameter put `r = 2 artanh x`. The metric becomes `dr²`, so
`r(t)=ct`, `x(t)=tanh(ct/2)` crosses the cone point at `t=0`. The unit frame
is `e=(1−x²)/2`, and `ẋ=e c`. Given this lifted initial velocity, the crossing
has no choice of reflected or refracted continuation. Forgetting the velocity
and retaining only the coarse point would remove the information that chooses
it. This is a paper derivation of the mechanical example, using the same
hyperbolic metric as the native implementation.

## Which arrows describe motion?

Use the ordinary pair groupoid `D×D ⇒ D`: an arrow `(z₀,z₁)` is a physical
step, and composable pairs share an endpoint. Its Lie algebroid is `TD`.
C4 acts diagonally on these steps. First construct equivariant dynamics in
this ordinary setting; then establish descent of the resulting phase map.

The étale action groupoid `C4 ⋉ D ⇒ D` instead describes changes of quotient
representative. Its source fibers are discrete and its Lie algebroid has rank
zero. A variational equation along those fibers cannot supply the two real
velocity degrees of freedom of the particle. At the origin, its arrows rotate
a representative without providing any radial displacement. Regularity for
this rank-zero problem would not establish regularity of particle mechanics.

The smooth Atiyah-groupoid reduction in Marrero–Martín de Diego–Martínez
requires a principal bundle, hence a free action. The diagonal C4 action on
`D×D` fixes `(0,0)`, so the coarse quotient cannot be passed to that theorem
as a smooth principal gauge groupoid. See their [§2.2 and §5.4][M]. A suitable
orbifold phase space is `[T*D/C4]`, with invariant canonical symplectic form.
Lerman–Malkin's atlas description of forms and symplectic Deligne–Mumford
stacks supports this formulation ([§2.5, Proposition 2.9 and §2.12][O]). It
does not itself prove descent of the discretization proposed here.

Passing to the effective frame bundle makes C4 act freely, but does not fix
this issue for free. Pulling the point-particle Lagrangian back to its tangent
bundle gives no kinetic term in the vertical angular velocity and is
Legendre-degenerate. Adding such a term changes the physical system to one
with a rotor. With an ineffective kernel even the frame action need not be
free. Neither change is an implicit premise of this comparison.

## Source results and their hypotheses

The inspected versions and locators are part of the evidence, including the
actual two-page published correction, not merely a reference to its existence.

| Source | Result used | Hypotheses and boundary |
| --- | --- | --- |
| [Marrero–Martín de Diego–Martínez, math/0506299v2][M] | §4.1 variational principle; §4.6 Legendre maps; Theorem 4.4 preservation; §4.9 Noether theorem | Smooth Lie groupoid, composable steps and admissible variations. The preserved object is a Poincaré–Cartan Lie-algebroid two-section; it is not automatically an ordinary symplectic form on every arrow manifold. |
| [Published corrigendum, Nonlinearity 19, 3003–3004][C] | Corrected Definition 4.12 and Theorem 4.13; corrected Remarks 4.3 and 4.8 | Regularity means the Poincaré–Cartan two-section is symplectic. It is equivalent to either Legendre map being a local diffeomorphism. Local evolution is constructed near a chosen DEL solution. Source and target local bases may require different neighborhoods. These changes are incorporated in v2. |
| [Marrero–Martín de Diego–Martínez, exact discrete Lagrangian, v1][E] | Theorem 5.1 exact action and Hamiltonian flow; Theorem 5.7 approximation order | Theorem 5.1 uses hyperregular continuous L on an integrable Lie algebroid and sufficiently small positive time on local domains near identities. Theorem 5.7 requires regularity and an order-r approximation to the exact discrete Lagrangian. It does not supply implementation-specific constants or roundoff bounds. |
| [Marrero–Martín de Diego–Stern, v2][S] | Theorem 2.16, Lagrangian bisections and local source/target invertibility | A Lagrangian submanifold of a symplectic groupoid is required. The cotangent relation `dL(G) ⊂ T*G` can represent mechanics before choosing an evolution map. An arbitrary relation or Lie-groupoid submanifold does not satisfy the theorem. |
| [Lerman–Malkin, v2][O] | Atlas-compatible tangent/cotangent data and symplectic forms | Deligne–Mumford stack with the stated atlas conditions. This supports retaining finite stabilizers, rather than claiming a smooth coarse quotient at the singularity. It is not a general stack variational-integrator theorem. |

The correction's rejecting example is `L(x,y)=(y−x)^4`. Its DEL equation gives
`z=2y−x`, a unique global diffeomorphic evolution on pairs. Nevertheless its
mixed Hessian is `−12(y−x)²`, which vanishes on the diagonal. Existence of a
unique evolution is therefore insufficient evidence of regularity.

For a regular L the corrected proof constructs
`ξ = (F⁻|V)⁻¹ ∘ (F⁺|U)` near a chosen solution `(g₀,h₀)`. The uniqueness
needed here is uniqueness within that inverse branch, or of its germ at that
solution. The printed uniqueness clause does not explicitly restrict the
competing map's target to the chosen inverse neighborhood; its proof uses
that inverse. This report does not infer a global, branch-independent selector
from a local diffeomorphism.

## Variational step, Legendre maps and rejecting controls

For fixed `h>0`, a discrete Lagrangian on admitted pairs defines action
`Σ Ld_h(z_k,z_(k+1))` with fixed endpoints and interior variations. In the
pair groupoid the DEL equation is

`D₂ Ld_h(z_(k−1),z_k) + D₁ Ld_h(z_k,z_(k+1)) = 0`.

The Legendre maps are
`F⁻(x,y)=(x,−D₁ Ld_h(x,y))` and `F⁺(x,y)=(y,D₂ Ld_h(x,y))`.
Invertibility of the mixed Hessian supplies local regularity; a selected
inverse branch supplies the update. On a local convex normal neighborhood the
exact free-particle action is `Ld^E_h(x,y)=d_g(x,y)²/(2h)`. This formula follows
by integrating the constant kinetic energy along the selected geodesic.
The exact-discrete theorem [E] identifies its phase update with the exact
Hamiltonian flow on the admitted local domain.

On a diameter this becomes
`Ld^E_h(x,y)=2(artanh y−artanh x)²/h`, with momenta

`p₀=4(artanh y−artanh x)/(h(1−x²))`,
`p₁=4(artanh y−artanh x)/(h(1−y²))`.

The DEL recurrence is `r_(k+1)−2r_k+r_(k−1)=0`. It applies across `x=0`
without discarding the incoming lifted direction.

A candidate approximation, chosen only after fixing that law, is coordinate
midpoint quadrature:

`m=(x+y)/2`, `Ld_h(x,y)=2|y−x|² / (h(1−|m|²)²)`.

For disk endpoints the midpoint stays in the disk. At the diagonal its real
mixed Hessian is `−4 I/(h(1−|x|²)²)`, so it is regular on a neighborhood of
each diagonal point. A practical solver still needs an explicit admitted
neighborhood, velocity and radius bounds, and a branch-selection procedure.
Positivity of the kinetic energy is no proof of global invertibility. The
formula is undefined at `h=0`; native zero-duration identities need a separate
case rather than division by zero.

This scheme is C4-equivariant and, for this radial metric, SO(2)-equivariant.
It is not the exact geodesic update. For a reproducible rejecting calculation
set `h=1`, `x₀=0`, `x₁=1/2`, `x₂=4/5`. These have equal increments of
`2 artanh x`, so they are successive exact geodesic samples. For real x,y,
put `d=y−x`, `m=(x+y)/2`, `s=1−m²`. Then

`D₂ Ld=4d/s²+4d²m/s³`, `D₁ Ld=−4d/s²+4d²m/s³`.

The DEL residual at these three samples is exactly
`301663232/1540798875`, which is nonzero. This rational calculation rejects
reusing exact native movement as if it satisfied the midpoint variational
recurrence. It does not reject local consistency of midpoint quadrature.
No order or uniform error theorem for that scheme has been formalized here.

Minimizing over representative rotations is another rejected shortcut:
`min_g Ld^E_h(x,g y)` loses the selected lift and may have tied branches. At
`x=0` all rotations have equal action while specifying different outgoing
lifted directions. Coarse endpoint cost cannot replace the selected history.

A regular local variational map preserves the corresponding symplectic form.
A continuous infinitesimal symmetry satisfying the Noether hypotheses gives a
momentum invariant. C4 itself has zero Lie algebra and supplies no nontrivial
infinitesimal momentum; angular momentum in this example comes from SO(2).
Fixed-step symplecticity does not imply exact energy conservation. Local
existence, preservation, approximation order, accumulated error and roundoff
are separate obligations. Rational evaluation avoids floating-point roundoff
but does not eliminate discretization or nonlinear-solve error.

## Comparison with checked native observations

At baseline `8c2d494`, [TimedCommands.lean][T] proves
`control_move_geodesic`, `control_move_speed`, `command_move_transport`, and
the position/frame equations. A constant `move` has precisely the free
geodesic interpretation chosen above. Its transported frame and physical
elapsed time can therefore be compared with a mechanical trajectory. Changing
move velocities at command boundaries prescribes new motion externally.
A `turn` rotates the observation frame at fixed position; a `hold` consumes
time without movement. Neither is a free-particle continuation with nonzero
momentum. Forces, impulses or constraints could model those operations, but
that would be a different specified mechanical problem.

[Cartan development and atlas transport][A] retain the chosen path, full frame
transport, closing symmetry and clock. A discrete pair sequence alone does
not determine those observations. A mechanical adapter must select an edge
interpolation, transport the frame on it, retain representative changes, and
prove independence of admitted chartings/subdivision. Accepted #408 supplies
such comparisons for its certified native path factors; it does not certify
all edges produced by a new mechanical solver. Even equal endpoints and
elapsed time do not establish equal transport or closing labels.

The current [numerical-motion report][N] describes rational Euler for the
controlled first-order position/frame system. [NumericalExecution.lean][X]
proves `run_correct`, `run_error` and `run_clock` for successful checked runs;
[NumericalSymmetry.lean][Y] proves `checkedStep_equivariant` and execution
symmetry. These are explicit bounds and symmetry laws for that implementation.
The variational papers add no symplecticity or energy theorem to Euler.
A comparison must use the same free-motion initial data and observation map,
then separately compare error, work, failure conditions and retained history.
Operation counts from #193 are distinct from physical time, storage and
numerical error. No author-effort or performance measurements were made here.

## Descent, extension limits and next decision

The proposed phase update must commute with C4, including its chosen local
inverse domains. That can be proved from invariance of Ld and local uniqueness
on compatible branches. It then defines an orbifold phase map with stabilizer
data. A finite invariant intersection can restrict local domains, but it does
not choose among globally different solutions. At the origin all chart-change
labels must remain observable where the client asks for them.

Coordinate midpoint is compatible with these linear rotations. It is not
invariant under arbitrary nonlinear coordinate changes. Recomputing midpoint
independently in a new chart generally defines another discrete Lagrangian.
For general atlases, transport the same generating function across overlaps,
or construct one using invariant geometric data and prove the overlap laws.
Frame gauge compatibility from #408 alone does not prove this displacement
compatibility.

A C4-invariant variable metric can support the same question. For example
`exp(2|z|²)|dz|²` is invariant; `exp(2(Re z)²)|dz|²` is not invariant under a
quarter turn. The first example needs new geodesic, exact-action, regularity
and numerical analyses, even though the descent strategy survives. A
non-global quotient needs compatible local displacement domains and their
compositions, not a fictitious global principal bundle. For an ineffective
extension such as C4×C2 acting through C4, the kernel acts trivially on position,
velocity and frame but remains isotropy data. A coarse state cannot recover it.

The recommendation has four parts:

- **Adopt** the corrected regularity criterion and the separation between
  symmetry arrows, displacement arrows and selected evolution. These prevent
  invalid uses of the existing mechanics theorems.
- **Investigate** a bounded free-particle client on the disk: independently
  specify the ODE and kinetic action, prove the midpoint mixed Hessian and
  C4 laws, supply a local inverse domain, and compare with the exact diameter
  action. This can be ordinary Lean analysis without a new frontend or general
  groupoid-mechanics library. A solver acceptance test must reject the exact
  samples above as a midpoint DEL solution.
- **Defer** a general variational stack library and non-global discretization
  until a client requires their overlap/composition laws. A relation-based
  cotangent formulation [S] remains an architectural alternative for degenerate
  or constrained mechanics; a convenient selected-map API must not rule it out.
- **Reject** treating the étale C4 action groupoid as physical steps, using
  principal reduction at its fixed point, or replacing timed control semantics
  with free mechanical evolution without changing the specification.

A successor must prove the local analytic laws before claiming an executable
selected solver. The solver then needs terminating or explicitly partial
root-finding, residual/error bounds, symmetry-compatible failure, and an
observation bridge preserving path, frame, clock and closing label. Test cases
include rest at the origin, a crossing with nonzero velocity, a rotated copy,
a retained loop label, zero-time handling and an ineffective label. An exact
geodesic reference can test the solver, but cannot stand in for its DEL proof.
The remaining comparison with variable-curvature local displacement structures
belongs with #312; no prerequisite forces it to use this midpoint scheme.

This research leaves #32/#34 geometry and #49 motion ownership intact. It adds
no backend migration or new axioms. Existing [three-presentation research][P]
and [motion reassessment][R] remain relevant to transport and controls; the
new obligation is a physical variational law and its selected numerical
realization. A mechanical solver could replace a future mechanical backend if
it meets that client's observations and error requirements. Current interface
convenience is not evidence against that architecture.

[M]: https://arxiv.org/abs/math/0506299v2
[C]: https://doi.org/10.1088/0951-7715/19/12/C01
[E]: https://arxiv.org/abs/1608.01586v1
[S]: https://arxiv.org/abs/1103.6250v2
[O]: https://arxiv.org/abs/0908.0903v2
[T]: ../../Applications/Orbifold/TimedCommands.lean
[A]: disk-atlas-transport-descent.md
[N]: numerical-motion.md
[X]: ../../Applications/Orbifold/NumericalExecution.lean
[Y]: ../../Applications/Orbifold/NumericalSymmetry.lean
[P]: orbifold-transport-three-presentations.md
[R]: orbifold-motion-reassessment.md
