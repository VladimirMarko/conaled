# Local displacement arithmetic and loopoids

The useful alternative is a connection-dependent local displacement operation,
with its parenthesization and domain evidence retained. It can be a mathematical
interface in its own right; it need not become an associative pose algebra.
It does not, however, define addition of independently represented orbifold
positions. The quarter-turn obstruction survives even in the flat case and
persists for the variable-curvature example below.

This is the research result for [#312](https://github.com/VladimirMarko/conaled/issues/312),
on source baseline `8c2d494a2f80c7962daae22557fd5a1f84d0cc54`.
The derivations below are paper arguments, not new Lean theorems. Existing
checked results are identified separately. No new numerical experiment,
performance comparison, universal loopoid library or backend replacement was
performed. The [motion reassessment](orbifold-motion-reassessment.md) supplies
the original comparison questions.

## What the published contracts require

Grabowski–Ravanpak use target α, source β, units M, and composable pairs
β(g)=α(h). Their smooth quasiloopoid has surjective submersions α,β,
smooth multiplication, units, and injective immersed translations. A loopoid
additionally has unit associativity, equivalently the appropriate endpoint
laws, and diffeomorphic translations between fibers. Associativity is absent.
Division by translations does not supply the stronger inverse property
`g⁻¹(gh)=h`, `(hg)g⁻¹=h`; that property is additional.
Their tangent construction preserves loopoids, while the usual cotangent
multiplication need not exist. Infinitesimal structures are skew/almost Lie
algebroids, without a general Jacobi identity. Their nonassociative mechanics
defines equations through prolongations; the ordinary fixed-product variation
argument does not automatically transfer. Regularity is defined through a
Legendre local diffeomorphism; the inverse-loopoid hypothesis matters in the
comparison of the two Legendre maps. These are published results, not an
orbifold instance. [Definitions 3.2, 3.4, 3.7; §§5–7, especially Theorem 6.3,
Definition 7.3 and Theorem 7.4](https://arxiv.org/html/2101.07258v2).

A point requiring care in adoption is *locality*. The above multiplication is
defined for every source/target-matched pair. A geodesic local loop instead
has an additional open domain around its unit. Merely naming the base point
as both source and target would incorrectly admit all pairs. We must retain
an explicit local-domain relation or prove a separate globalization theorem.
This is a difference in contracts, not a reason to reject the local operation.

Kikkawa's 1964 Theorem 1 constructs local loops on suitable restricted normal
neighborhoods of a smooth affinely connected manifold. Theorem 2 says a
left-di-associative such loop for a torsion-free connection forces curvature
zero at the unit. **Order convention:** that paper transports the first
argument's initial vector to the second point; the 1999 survey's displayed
formula uses the opposite order. Associativity is unaffected by passing to
the opposite product, but one-sided identities are exchanged. We use the
survey order throughout. The original paper's holonomy comparison also has
an extra hypothesis; inner mappings are not automatically the full holonomy
group. [1964 paper, pp. 200–207, inspected mirrored scan](https://scispace.com/pdf/on-local-loops-in-affine-manifolds-4cgcqcg7bm.pdf),
[publication DOI](https://doi.org/10.32917/hmj/1206139396),
[1999 author survey, §1.1](https://ir.lib.shimane-u.ac.jp/3358/files/8459).

## A local contract stated without a group assumption

Fix a smooth affine connection ∇ and base point o. Choose a star-shaped
neighborhood V of zero in TₒM such that Expₒ restricts to a diffeomorphism
onto U; Logₒ means this inverse, not an unspecified logarithm. For x in U,
let cₓ(t)=Expₒ(t Logₒ x), 0≤t≤1, and let Pₓ transport along this particular
radial path. Define, where meaningful,

```text
μₒ(x,y) = Expₓ(Pₓ Logₒ y)
hₒ(u,v) = Logₒ(Exp_(Expₒ u)(P_(Expₒ u) v)).
```

Admissibility includes x,y∈U, existence of the second exponential through time
one in the chart, and its endpoint lying in U if a further Logₒ or nested
operation uses it. Every intermediate node of a parenthesized expression
needs those premises. Shrinking domains can establish local division. It
cannot make an arbitrary bounded neighborhood closed under all additions:
even Euclidean addition exits such a neighborhood.

Here is our direct law check. μₒ(o,y)=y and μₒ(x,o)=x. Consequently both
partial derivatives at (o,o) are identities; the inverse function theorem
supports local left and right division after suitable restriction. With a
compatible inverse branch Logₓ, left division has the explicit formula
`x \ z = Expₒ(Pₓ⁻¹ Logₓ z)`. Right division solves μₒ(z,x)=y on its selected
local branch. Neither formula asserts a global division or the inverse
property of a loopoid. A connection with torsion still supports the
construction; torsion-free and curvature assumptions must be supplied for
any stronger identities. No metric is needed until metric observations or
Levi-Civita transport are requested.

A local affine diffeomorphism φ preserving the connection carries geodesics
and parallel solutions to their counterparts by uniqueness. If it also
carries the chosen domains and inverse branches to the target choices, then

```text
φ(μₒ(x,y)) = μ_(φ(o))(φ(x),φ(y)),
Dφₓ Pₓ = P_(φ(x)) Dφₒ.
```

These are our naturality deductions from the defining ODEs. For a base-fixing
symmetry they give diagonal equivariance. For a chart change moving the base,
the target operation has base φ(o), not o. If choices are only locally
compatible, restrict both sides to their common domain; an arbitrary chosen
log branch need not be equivariant.

## Quarter-turn descent, including its failure

Use the flat disk chart, o=0, and J(x,y)=(-y,x). Restrict the local operation
to pairs whose sum remains in a small chart neighborhood. Then μ₀(x,y)=x+y
and μ₀(Jx,Jy)=Jμ₀(x,y). Nevertheless choose 0<a<1/3 and x=y=(a,0).
Replacing only x by Jx preserves its C4 orbit but changes the outputs to
(2a,0) and (a,a). Their squared Euclidean radii are 4a² and 2a², so they are
not C4-related. All points and outputs can be arbitrarily close to the unit.
Shrinking the domain cannot repair independent-representative descent.
This is our elementary obstruction, distinct from the checked hyperbolic one.

The latter must also remain visible:
[QuarterTurn.quotient_addition_values](../../Applications/Orbifold/QuarterTurn.lean)
proves `gyroAdd(1/5,1/5)=5/13` and `gyroAdd(1/5,-1/5)=0`.
`second_inputs_same_orbit` and `addition_outputs_different_orbits` certify
that the second inputs agree as orbits while the outputs do not. Choosing a
nonassociative local operation does not refute or bypass that theorem.

What *does* descend is the operation on pairs with a common representative
change: the diagonal C4 action on its invariant domain. It gives a map from
the diagonal action groupoid to the position action groupoid, carrying the
same label. Its domain is not the product of two independently quotiented
position sets. To connect independently presented inputs one must retain a
chosen alignment arrow or equivalent frame data; its effect on the result
is observable. This is the precise additional input, not a claim that no
quotient-based interface can work.

At the origin retain all four stabilizer arrows. For an ineffective test,
let C4×C2 act through C4. The origin has eight labeled automorphisms and a
nonzero point has a C2 stabilizer, although that kernel acts trivially on
positions, tangent vectors and the local operation. Diagonal equivariance
still holds, but numerical tangent data cannot recover the hidden label.
Replacing the labeled frame groupoid by a coarse free-frame manifold would
erase it. This paper guard agrees with the existing ineffective-arrow
controls in [SmoothOrdinaryIsotropy](../../Examples/SmoothOrdinaryIsotropy.lean);
it is not a new proof of an ineffective geodesic-loop orbifold model.

## A variable-curvature local calculation

Take a neighborhood of zero in ℝ² with

```text
r² = x²+y²,  g = exp(2r²)(dx²+dy²),
Γ_z(u,v) = 2〈z,u〉v + 2〈z,v〉u − 2〈u,v〉z.
```

This is our worked Levi-Civita calculation. Γ is symmetric in u,v and
satisfies metric compatibility by differentiating exp(2r²). Its Gaussian
curvature is `K(z)=-4 exp(-2r²)`; it is variable and nonzero at zero. In the
convention `R(X,Y)Z=∇_X∇_Y Z−∇_Y∇_X Z−∇_[X,Y]Z`, differentiating Γ at
zero directly gives `R₀(X,Y)Z=4(〈X,Z〉Y−〈Y,Z〉X)`, hence
`R₀(e₁,e₂)e₂=-4e₁`. Both the metric and Γ are C4-equivariant.
The earlier checked `ConnectionAssessment.variable_vertical` concerns
f=x², which is not C4-invariant. It cannot be silently reused as this cone
metric. [Existing coefficient identities](../../Applications/Orbifold/ConnectionAssessment.lean)
provide algebraic precedents, not the new curvature or exponential theorem.

There is an explicit reduction along rays. Set
`F(r)=∫₀ʳ exp(s²) ds`. For a sufficiently small chosen normal neighborhood,

```text
Log₀(x) = (F(|x|)/|x|) x,       ratio at zero = 1,
Pₓ(v) = exp(-|x|²) v,
μ₀(x,y) = Expₓ(exp(-|x|²) (F(|y|)/|y|) y).
```

To verify the transport formula, parametrize the radial path as z(t)=tx.
Then Γ_(tx)(x,V)=2t|x|²V, so V(t)=exp(-t²|x|²)V(0) solves the parallel
ODE. The geodesic image is the same radial ray; the affine parameter is
its g-arclength F. The second exponential solves the explicit ODE
`z''+4〈z,z'〉z'−2|z'|²z=0` with the stated initial vector. We have not
claimed a closed form for its nonradial solutions, nor a computable certified
radius for the common normal neighborhood.

The local product is genuinely nonassociative. If it were associative on a
neighborhood, its opposite product would satisfy the one-sided identity in
Kikkawa's 1964 Theorem 2. The connection is torsion-free, but R₀≠0,
contradicting that theorem. This gives an existence obstruction to
associativity, not a numeric associator value for selected finite inputs.
It does not invoke homogeneity or parallel curvature. Indeed K is not
constant, so ∇R cannot vanish throughout this neighborhood.

Independent quotient descent still fails. Smoothness and the two unit laws
give `Dμ_(0,0)(u,v)=u+v`. For x=y=ae₁ the output has squared radius
`4a²+o(a²)`; for x'=ae₂ and y=ae₁ it has squared radius `2a²+o(a²)`.
For sufficiently small positive a the radii differ. Thus even this invariant,
variable-curvature local operation cannot be applied to independent C4
orbits. This deduction needs only the derivative at the unit, not a truncated
series asserted to equal the exact exponential.

Endpoint data also loses transport. On a small circle z(θ)=r(cosθ,sinθ),
Γ_z(z',V)=2r²JV, so parallel transport is rotation through −2r²θ and a
full circle gives angle −4πr². For small nonzero r this differs from the
identity transport of a constant hold with the same endpoint. Clock, chosen
path and closing isotropy arrow are therefore separate observations. This
paper calculation parallels the already checked hyperbolic
[TransportSegments.path_dependence](../../Applications/Orbifold/TransportSegments.lean),
without asserting that the two metrics share a transport implementation.

A local loop based at o can be viewed as a one-object displacement algebra;
its continuum of elements is not the finite orbifold stabilizer at o. A
family indexed by o would have both base maps equal to o and multiplication
inside each fiber. It still would not compose physical arrows from x to y.
Building that transition object, retaining the local admissibility relation
and the separate symmetry arrows, is an additional construction. Naming it a
loopoid does not supply the missing endpoints or identify those two kinds of
isotropy.

## Comparing the alternatives on their own terms

| Interface | Capability for this workload | Obligation or information it does not supply |
|---|---|---|
| Local μₒ and double exponential hₒ | Compose small based displacements; local division and differential expansions without homogeneous geometry | Base, connection, branches and every intermediate domain; endpoint alone forgets clock, path and closing label |
| Smooth loopoid | Nonassociative source/target composition, division and tangent construction | An actual instance with the required global fiber translations; the geodesic local domain is an additional obligation |
| Gyrogroup | A specified correction to reassociation, with strong reusable laws in supported geometries | Generic local-loop inner maps need not satisfy its automorphism and loop laws |
| Framed paths | Explicit physical trajectory, clock, parallel transport and labeled closing symmetry | Producing the path from a command remains an existence/ODE problem; endpoint arithmetic is not its primitive operation |
| Homogeneous disk poses | Compact exact composition and point/frame observation | The implemented motion derivative is not arbitrary path parallel transport; variable curvature has no supplied homogeneous pose model |
| Connection-dependent development | Controls in a transported frame generate a path and frame together | Existence interval, chart transitions and isotropy descent; no free global finite-dimensional pose algebra |

The pinned AFP `gyrogroup` class requires left identity/inverse,
gyroassociativity, automorphism-valued gyrations and the left loop law.
For a local loop, `L_(μ(x,y))⁻¹ L_x L_y` measures reassociation where defined;
merely naming it a gyration establishes none of those extra laws.
[Primary Isabelle theory, lines 4–20](https://raw.githubusercontent.com/isabelle-prover/mirror-afp-devel/352a4e06c2e2c1dc358200e2a87bd930e458ca90/thys/GyrovectorSpaces/GyroGroup.thy).

Al-Kaabi et al. construct formal double-exponential machinery for general
affine connections using an enlarged free Lie/D-algebra setting. Their
Theorem 6 is a formal-series result; it does not supply a finite-step
convergence or numerical remainder bound. Grong–Munthe-Kaas–Stava's more
specialized construction assumes parallel torsion and curvature; the metric
above fails the latter. These are different routes, so rejecting the
specialized hypothesis is not rejection of the general expansion program.
[Al-Kaabi et al., Proposition 7 and §6, v1](https://arxiv.org/html/2205.04381v1),
[Grong et al., Theorem 1.1, v2](https://arxiv.org/html/2305.02688v2).

The present library already distinguishes some of these observations.
[TransportFrames.terminal_frame](../../Applications/Orbifold/TransportFrames.lean)
relates the terminal pose to the whole transported frame, and
`ClosedLift.endomorphism` applies the labeled closing action after transport.
[QuarterTurn.right_increment_equivariant](../../Applications/Orbifold/QuarterTurn.lean)
justifies fixed body increments on framed-state orbits; it is not independent
orbit multiplication. These results remain useful even if local arithmetic
becomes the preferred command interface. Conversely, an associative path API
is not a prerequisite for proving μ's local unit/division/naturality laws.

## Bounded integration decision

**Investigate a local displacement interface under #34/#32; retain the native
interfaces meanwhile.** Start with ordinary connection mathematics and an
explicit open domain, not a universal displacement algebra or a new frontend.
A bounded next experiment should admit a parenthesized command with two or
three local steps, preserve its endpoint and differential under a
connection-preserving chart change, and retain the selected alignment label.
Its acceptance controls are the flat quarter-turn descent failure, the
ineffective kernel, and the variable-curvature distinction between endpoint
and transport. Prove actual domain/branch hypotheses for its chosen instance;
do not accept those as opaque assumptions and call it an implemented geometry.
A flat instance alone cannot validate nonassociative behavior.

There is a compositional route without imposing associativity: interpret
binary expression trees, carrying domain proofs at each node, and prove local
operation preservation. Induction then gives interpretation preservation for
that tree. Reassociation is a separate rewrite requiring its own law or
explicit correction. The existing square idea is compatible with this
contract; it does not require the primitive binary operation to be associative.
Whether current formal interfaces make the dependent domains convenient is
an authoring question for the bounded experiment, not something settled by
this paper derivation. Ordinary Lean clients should retain direct use of the
operations and their geometric theorems.

The possible benefit is a smaller **mathematical command interface** when the
client wants local endpoint/differential arithmetic. It is not yet a better
numerical representation, a faster integrator or a new mechanical law.
A command producing transport must additionally expose the chosen developed
path or prove the required transport comparison; recording only hₒ is
insufficient. Preserve construction and observation as separate contracts.

**Defer general loopoid mechanics** to #311's comparison until an actual
configuration space, Lagrangian, inverse/regularity hypotheses and local
solution branches are supplied. Do not identify the orbifold's étale symmetry
arrows with physical displacements. Do not transfer groupoid symplectic or
fixed-product variational claims merely because the same equation notation
is used. No global flow, conserved quantity or numerical error estimate was
established here. **Reject independent coarse-position addition** for the
worked operations, rather than rejecting nonassociativity itself.

Stop the proposed experiment if its selected endpoint/differential client
requires the full existing path state with no reduction in author obligations,
or if branch/alignment data cannot be made explicit without changing the
intended observations. That is evidence against this interface for that
client, not proof that loopoids have no applications. A materially different
dynamics model requires owner discussion; ordinary local proof obligations
do not. #313's realization comparison and the existing numerical work remain
independent. No broad migration or new Lean axioms follow from this report.

## Source inventory and evidence limits

| Source inspected | Exact role and limitation |
|---|---|
| Grabowski–Ravanpak, arXiv:2101.07258v2 (2022), §§3, 5–7 | Definitions, tangent and mechanics contracts; no instantiated conaled geometry |
| Kikkawa, *On Local Loops in Affine Manifolds* (1964), Theorems 1–3 | Local existence and curvature obstruction, with opposite-product convention accounted for; publisher retrieval returned a challenge page, so the primary paper was inspected through a mirrored scan |
| Kikkawa, *Geometry of Homogeneous Left Lie Loops and Tangent Lie Triple Algebras* (1999), §§1.1–1.3 | Author's formula and separation of general local loops from stronger homogeneous structures |
| Al-Kaabi et al., arXiv:2205.04381v1 (2022), Proposition 7, §6 | General affine formal double exponential; no analytic convergence or numerical guarantee imported |
| Grong et al., arXiv:2305.02688v2, Theorem 1.1 | Parallel-curvature/torsion route and its failed hypothesis here |
| AFP GyroGroup.thy at `352a4e06c2e2c1dc358200e2a87bd930e458ca90` | Actual gyrogroup axiom boundary; not a Lean import |

Versioned primary links above are durable. External author receipts record
retrieval URLs, hashes for downloaded HTML/PDF/source files and unsuccessful
fetches; a blocked HTML response was explicitly excluded as PDF evidence.
The 1964 scan was inspected through web PDF extraction, not replayed in a
proof assistant. No inaccessible 2004 follow-up is used as evidence.
Documentation validation checks local links and repository cleanliness;
independent Standards and Spec review owns acceptance of this research.
