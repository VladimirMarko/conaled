# Lorentz and Clifford realizations of framed hyperbolic motion

Research for [#313](https://github.com/VladimirMarko/conaled/issues/313),
2026-11-09. Native implementation inspected at
`46ccec3ce63d7adf7cb55c2dae1163011b34af27`.

**Recommendation: investigate exact Lorentz and spin adapters, retain the
existing native interface and certified numerical backend.** The adapters can
represent the same oriented point/frame observations. Neither the sources nor
the bounded probe establish a numerical winner. Near the disk boundary, small
coordinate errors can coexist with large frame errors. A future backend must
prove both its geometric comparison and its numerical contract.

This report separates existing Lean results, mathematical derivations below,
published numerical analysis, and executable observations. It adds no Lean
theorem or certified simulator. The Python artifact is a research experiment.

## Subsequent exact Lorentz implementation

[#411's implementation record](exact-lorentz-motion.md) describes the checked
`B(a)R(u)` image carrier, coordinate round trips, actual real matrix operations,
point/full-frame actions, finite products and independent consumers. It does
not classify every future Lorentz matrix or add a numerical backend. The
research derivations and numerical observations below retain their original
status; the implementation record identifies the results now checked in Lean.

## Common semantics and existing checked boundary

Freeze the curvature −1 Poincaré disk, with a pose `(a,u)` satisfying
`|a|<1`, `|u|=1`. Its point is `a`, its first oriented unit tangent vector is
`h=(1−|a|²)u/2`, and the second is `i h`. Its motion is

```
f(a,u)(z) = (u z + a)/(1 + conjugate(a) u z).
```

Identity is `(0,1)`. Composition applies the right operand first. For
`p=(a,u)`, `q=(b,v)`, put `d=1+conjugate(a)u b`. Then

```
p ⋅ q = ((a+u b)/d, (conjugate(d)/d) u v)
p⁻¹   = (−conjugate(u)a, conjugate(u)).
```

The denominator cannot vanish: `|conjugate(a)u b|<1`. Point action at an
arbitrary `z` is `f(p)(z)`; frame action at `(z,w)` is `f(p)'(z)w`.
These are derivatives of isometries, not parallel transport along a supplied
trajectory. A position alone omits the stabilizer rotation and therefore
cannot replace a framed pose for body-relative increments.

[Pose](../../Applications/Orbifold/Pose.lean) already proves `matrix_comp`,
`motion_comp`, `motion_injective`, associativity, and `frame_comp`.
[MatrixDisk](../../Applications/Orbifold/MatrixDisk.lean) proves the matrix
point and derivative formulas, including nonzero denominators and scalar
representative independence. [DiskRealizations](../../Examples/DiskRealizations.lean)
checks arbitrary finite compositions and frames through the public squares.
The checked projective construction itself does not classify all hyperbolic
isometries. The Lorentz and spin correspondences below are proposed
mathematical constructions, not additional checked results.

The existing complex representative is

```
M(a,u) = [[u, a], [conjugate(a)u, 1]].
```

It preserves the Hermitian form of signature `(1,1)` up to the positive factor
`1−|a|²`. Products equal the representative of the composed pose times the
nonzero scalar `d`. Any nonzero complex scalar gives the same motion and
frame derivative; arbitrary matrices do not. The carrier consists of
certified positive similitudes modulo those central scalars. Inverse can be
computed by the adjugate when only projective meaning is needed.
[ProjectiveMotion](../../Applications/Orbifold/ProjectiveMotion.lean) supplies
this quotient rather than asserting equality of representative matrices.

## Primary sources and their scope

Sokolov's [*Clifford algebra and the projective model of Hyperbolic spaces*,
v1, §2](https://arxiv.org/pdf/1602.08562v1) uses `e₀²=−1`,
`e₁²=e₂²=1`. Lines are vectors; plane points are dual bivectors
`P=w e₁₂+x e₂₀+y e₀₁`. Proper points have `P²<0`; null points form the
absolute, and the other projective points are not reachable interior metric
points. Its coordinates at `w=1` are Klein coordinates. Sandwich actions
implement motions. The paper motivates a hyperbolic Clifford adapter, not a
floating-point certification. We pin the arXiv version, whose submission is
2016; the PDF's rendered date is 2022.

Gunn's [*Geometric algebras for euclidean geometry*, v4, §§3.7–3.8,
7–8](https://arxiv.org/html/1411.6502v4) distinguishes degenerate **dual
Euclidean PGA**, signature `(n,0,1)`, from Euclidean **CGA**, signature
`(n+1,1,0)`. CGA represents Euclidean points on a null quadric and directly
represents spheres. Euclidean PGA serves flat primitives and rigid motions.
Those are different geometric domains and grade conventions. Its Euclidean
kinematics comparisons do not establish the stability or efficiency of a
hyperbolic simulator. For this two-dimensional task, a general CGA would
carry 16 multivector coefficients, versus 8 in `Cl(2,1)` and 4 in its even
part; these storage counts alone say nothing about executed cost.

Mishne, Wan, Wang and Yang's [*The Numerical Stability of Hyperbolic
Representation Learning*, §§2–3](https://proceedings.mlr.press/v202/mishne23a/mishne23a.pdf)
distinguishes two failures. Propositions 3.1–3.2 relate distance to disk
boundary resolution and cancellation in the Lorentz norm. The approximate
binary64 radii 38 and 19 concern those different tests; the latter is a soft
constraint failure, not automatic loss of every useful coordinate.
Proposition 3.3 compares exact Riemannian gradient descent under a coordinate
change. Theorem 3.5 assumes `x=(1−δ,0,…)`, `δ=10⁻ᵏ`, a radial Euclidean
gradient with negative first component, and a matched Lorentz point. Its
expansions compare update magnitudes; the discussion takes step size 1 and
gradient size of order 1. They are not rounding-error bounds for arbitrary
motion sequences or frame transport. We use the paper to choose diagnostics,
not to transfer its optimization ranking to this workload.

## Exact Lorentz comparison, derived for the frozen contract

Use `J=diag(−1,1,1)`, the future sheet
`H={X : Xᵀ J X=−1, X₀>0}`, and `SO⁺(2,1)`: matrices satisfying
`Lᵀ J L=J`, `det L=1`, and preservation of that sheet. Other components of
the Lorentz group include orientation or time reversals and are outside this
contract. An oriented frame is the ordered triple `(X,E₁,E₂)` with Gram
matrix `J`, positive orientation, and future `X`.

Here are explicit candidate conversion formulas. Write `a=(x,y)`,
`g=1−x²−y²>0`, and `u=(c,s)`:

```
B(a) = [[(1+x²+y²)/g, 2x/g,          2y/g],
        [2x/g,         1+2x²/g,     2xy/g],
        [2y/g,         2xy/g,       1+2y²/g]]
R(u) = [[1,0,0], [0,c,−s], [0,s,c]]
L(a,u) = B(a) R(u).
```

Expanding the entries gives `Bᵀ J B=J`, `det B=1`, `B₀₀>0`;
`R` has the same properties when `c²+s²=1`. Thus the columns of `L`
are a valid `(X,E₁,E₂)`. Decode through

```
ψ(X) = (X₁,X₂)/(X₀+1)
Dψ_X(E) = ((X₀+1)(E₁,E₂) − E₀(X₁,X₂))/(X₀+1)².
```

For `L(a,u)`, substitution yields `ψ(X)=a` and
`Dψ_X(E₁)=g u/2`. Conversely, for a valid frame, set `a=ψ(X)` and
`u=2Dψ_X(E₁)/(1−|a|²)`. The frame equations give `|u|=1`;
`X₀≥1` makes decoding defined. The first two columns determine the third
by the orientation condition. Equivalently, `B(a)⁻¹ L` fixes `e₀` and
restricts to a unique planar rotation. This proves the candidate frame
correspondence without assuming arbitrary matrices have meaning.

Identity, multiplication and inverse are closed on `SO⁺(2,1)`;
`L⁻¹=J Lᵀ J`. Acting on every frame column gives point and tangent
action together. Substituting `ψ` into `L(a,u)X` gives the frozen Möbius
formula; differentiating gives the frame formula. Therefore
`L(p⋅q)=L(p)L(q)`: both sides act equally on the base oriented frame,
which determines a Lorentz matrix. Induction yields the same comparison
for every finite list, including the empty list. This argument covers
arbitrary valid operands, not just the probe's generators. Formalizing its
algebra, derivative and surjectivity steps remains work for a successor.

The related projective carrier is a negative real line `[X]`, not an
arbitrary point of real projective space. Selecting its future unit
representative removes both nonzero scale and sheet ambiguity. Klein
coordinates are `k=(X₁,X₂)/X₀=2a/(1+|a|²)`; using `k` as a Poincaré
point would change the specification. A negative line alone still omits
the frame. A projective implementation must retain tangent/frame data with
compatible scaling, or decode the future unit frame before observation.

## Clifford comparison and cover ambiguity

For the probe we use **primal vectors** in `Cl(2,1)`, with the same basis
squares as above. This is not a silent reuse of Sokolov's dual point grade.
With pseudoscalar `I=e₀e₁e₂`, our vector
`X=X₀e₀+X₁e₁+X₂e₂` has equivariant dual `P=−XI`:
`P=X₀e₁₂−X₁e₂₀−X₂e₀₁`. Its chart coordinates are the negatives of
our Klein coordinates, a fixed half-turn; matching literal chart coordinates
requires that coordinate change and the corresponding conjugation of motions.
In this odd dimension `I` is central and `I²=1`, so dualization commutes
with sandwich action and future unit vectors give `P²=−1`.

Use the spin group covering `SO⁺(2,1)`, generated by the following boosts
and rotations, not the carrier of all multivectors. An even element has
coordinates `r=r₀+r₀₁e₀₁+r₀₂e₀₂+r₁₂e₁₂`, with

```
r reverse(r) = r₀² − r₀₁² − r₀₂² + r₁₂².
T(a) = (1+x e₀₁+y e₀₂)/sqrt(g)
Q(θ) = cos(θ/2) − sin(θ/2)e₁₂
r(a,u) = T(a)Q(θ),  u = cos θ+i sin θ.
```

Direct Clifford expansion gives norm 1 and the sandwich columns
`r eⱼ r⁻¹ = L(a,u)eⱼ`. Multiplication therefore implements composition;
reverse is inverse for unit rotors. A product remains in the generated
group. For the rounded probe inverse is computed as `reverse(r)/norm(r)`,
and a nonpositive computed norm is rejected. That numerical choice is not
a proof that rounded multiplication preserves the spin carrier.

The kernel on these oriented frames is `{1,−1}`. To see the relevant
faithfulness condition, equal sandwich actions imply their quotient
commutes with each basis vector. Comparing even coefficients forces the
bivector terms to vanish; unit norm then leaves a scalar ±1. Thus rotors
are faithful **modulo sign**, whereas a chosen rotor is additional data.
Both `r` and `−r` act identically on every point and frame. A locally chosen
half-angle lift cannot give a global continuous single-valued lift around
the full rotation circle. Do not expose the probe's branch as a canonical
spin structure on an orbifold.

If arbitrary nonzero real multiples of a rotor are admitted, sandwich with
the true inverse is also scale-invariant. Such elements no longer satisfy
the unit-rotor contract. Quotienting them or renormalizing them needs a
separate representation specification. Null blades and arbitrary even
multivectors need not be invertible and are not permitted motions.

A replacement architecture based on Clifford blades could make incidence
operations and dimension-independent sandwich programs central. This is
more than a matrix adapter, but the present client consumes neither blade
incidence nor spheres. Establish that additional consumer before replacing
native poses with general multivectors. The exact conversion laws can be
proved in ordinary Lean; no frontend or embedded-calculus proficiency is
needed to state or consume them.

## Nontrivial observations and symmetry arrows

Take `p=(1/3,i)` and `q=(i/4,(3+4i)/5)`. Then

```
p ⋅ q = (1/11, (−4+3i)/5)
point(p ⋅ q) = 1/11
frame(p ⋅ q) = (−48+36i)/121.
```

The probe tests those independently calculated observations, along with
inverse and noncommutativity. For `p`, the Lorentz matrix is
`[[5/4,0,−3/4],[3/4,0,−5/4],[0,1,0]]`; its first tangent column decodes
to `4i/9`. A rotor lift is
`3/4+e₀₁/4−e₀₂/4−3e₁₂/4`. Scaling the complex matrix by `−3+2i`, or
negating that rotor, changes no observation. The tests also exercise the
half-turn lift where the local half-angle formula needs its explicit branch.

A quarter-turn representative change acts by `(a,u)↦(ia,iu)`. It changes
both observed point and frame. This is not scalar redundancy.
[QuarterTurn](../../Applications/Orbifold/QuarterTurn.lean) preserves the
C4 arrow label in `incrementFunctor`; its `right_increment_equivariant`
justifies body increments after a representative change. In Lorentz
coordinates this change is left multiplication by `R(i)`; in spin
coordinates it is a lift `Q(π/2)`, with its sign ambiguity recorded
separately. Associativity gives `(Q r)s=Q(rs)`, the same equivariance.
Four such lifts multiply to `−1`, whose sandwich is identity, while the C4
arrow still belongs to the external action-groupoid specification. An apex
point's isotropy is not erased by a matrix or spin quotient. The numerical
quarter-turn test checks point/frame action, not an implementation of the
arrow category.

## Reproducible bounded probe

Run from the Nix/direnv shell:

```sh
direnv exec . python3 -m unittest discover -s scripts -p test_lorentz_clifford_probe.py -v
direnv exec . python3 scripts/lorentz_clifford_probe.py --output /tmp/lorentz-clifford-results.json
```

The [probe](../../scripts/lorentz_clifford_probe.py), its
[tests](../../scripts/test_lorentz_clifford_probe.py), and the
[recorded output](lorentz-clifford-probe-results.json) are durable artifacts.
Only Python's standard library is used. Python's recorded binary64 run is
compared with Decimal precision 80; native references are recomputed at
precision 120. There is no random sampling or seed. The hard sequence
cutoff is 64. No platform timing or allocation benchmark is claimed.

Initial poses are `a=r(3/5+4i/5)`, `u=(4+3i)/5`, with `r=0` or
`r=1−2⁻ᵏ`, `k∈{8,20,40,50}`. Each run takes 0, 1, 8, or 64 left
increments from this repeating list:

| Displacement | Rotation |
|---|---|
| `1/8+i/16` | `(3+4i)/5` |
| `−1/10+i/12` | `(4−3i)/5` |
| `−i/9` | `i` |

All four algorithms receive the same intended rational inputs and decode
the same final point and first frame vector. Binary64 input rounding is
included in the discrepancy. There is no retraction or renormalization
between steps. The algorithms are native complex-pair gyro composition,
dense complex 2×2 multiplication, dense real 3×3 multiplication, and an
explicit even Clifford product. Spin observation sandwiches the base point
and first tangent vector, using its computed inverse.

The output records absolute point error, relative frame-vector error, and
`2|Δpoint|/(1−|point_ref|²)`. The last is a local sensitivity diagnostic,
not a global hyperbolic distance bound. Strict disk membership is tested
using Decimal applied to the actual binary64 coordinates, avoiding another
binary64 cancellation in that diagnostic. Carrier defects use binary64
arithmetic and can themselves suffer cancellation; they are observations,
not certified validity tests. Zero-step cases expose conversion/decoding
error separately from iteration. Invalid boundary input and cutoff overflow
are explicit negative tests. There is no claim to have sampled all angles,
long trajectories, inverse round trips near the boundary, or ODE solvers.

For the 64-step runs, rounded values from the recorded output are:

| Initial radius | Backend | Absolute point error | Relative frame error |
|---|---|---:|---:|
| 0 | pose | 1.07e−16 | 1.37e−15 |
| 0 | complex | 1.53e−16 | 1.91e−15 |
| 0 | Lorentz | 5.80e−16 | 2.49e−15 |
| 0 | spin | 1.11e−16 | 3.66e−15 |
| `1−2⁻⁴⁰` | pose | 2.30e−15 | 7.27e−4 |
| `1−2⁻⁴⁰` | complex | 1.39e−15 | 6.16e−4 |
| `1−2⁻⁴⁰` | Lorentz | 9.27e−15 | 5.89e−3 |
| `1−2⁻⁴⁰` | spin | 4.78e−15 | 1.66e−3 |
| `1−2⁻⁵⁰` | pose | 3.32e−15 | 8.98e−1 |
| `1−2⁻⁵⁰` | complex | 4.49e−15 | 6.66e−1 |
| `1−2⁻⁵⁰` | Lorentz | 4.58e−15 | 4.16 |
| `1−2⁻⁵⁰` | spin | 5.45e−15 | 1.81e−1 |

In the last complex case, the decoded point is outside the strict disk.
The 80/120-digit native reference change is below `5.6e−79` in absolute
coordinates. Cross-algorithm Decimal80 discrepancies are also recorded;
these agreement checks support the implementation audit but are not
interval enclosures or a proof of either algorithm. Small absolute frame
error can be a large relative error because the coordinate unit frame
shrinks at the boundary. The outcome supports measuring both retained
observations, not promoting the backend with the smallest entry in one row.

## Cost, storage and reuse

The following counts are executed scalar source events in the instrumented
program. Each add/subtract/multiply/divide/negate/square-root has unit weight
for this table only; the JSON retains the separate counts. Input parsing,
domain guards, diagnostics, allocation and dictionary lookup are outside
this tariff. The valid-input guards are shared but their cost is not zero
in an implementation benchmark. No special treatment of zero coefficients
or vectorization is used. Dense matrix arithmetic and sparse grade-keyed
Clifford arithmetic are specific algorithms, not optimality claims.

A 64-step repeated workload starting at `(1/3,i)` gives:

| Backend | Stored real coordinates per motion | Convert 64 increments + initial | Convert 3 distinct increments + initial | Compose 64 times | Decode once |
|---|---:|---:|---:|---:|---:|
| pose | 4, constrained | 0 | 0 | 3456 | 8 |
| complex | 8, projective | 455 | 28 | 3584 | 48 |
| Lorentz | 9, constrained | 5005 | 308 | 2880 | 13 |
| spin | 4, constrained and double cover | 1495 | 92 | 2048 | 137 |

Cached and uncached inputs produce identical binary64 observations in this
experiment. Caching reduces conversions, not the composition count. These
numbers include square roots for spin conversion and division for decoding;
they do not measure their machine costs. Keeping a representation across
many operations can amortize conversion. A client that requests a frame
after every increment instead pays decoding repeatedly, which changes the
comparison. An optimized direct spin-to-disk formula, specialized Lorentz
boost product, periodic scaling, or a different scalar carrier would be a
new algorithm to measure, not evidence already supplied here.

The [#265 measured implementation](structured-linear-implementation.md)
provides relevant composition/erasure and additive cost laws through
`Resources.Measured`, and instrumented structured linear kernels. Its
semiring matrix multiplication seam fits the multiplication block, but it
does not by itself account for division, square roots, carrier validation,
spin branch choice or allocation of this Python implementation. A Lean
adapter should instrument those primitives separately and reuse the
composition laws. The present counters are not Lean `Measured` proofs.
Neither abstract scalar tariffs nor these counts establish rational bit
complexity, wall time, or an agent-productivity advantage.

## Integration decision and remaining obligations

| Candidate | Disposition | Evidence and remaining obligation |
|---|---|---|
| Native pose and complex projective interfaces | Retain | Existing checked composition/action/frame comparisons; preserve ordinary clients and body-relative increments. Boundary cancellation remains a numerical concern. |
| Future oriented Lorentz frame | Investigate exact adapter | Explicit inverse and frame correspondence; real linear-algebra reuse. Must formalize sheet/orientation, round trips, derivative and all operation squares. Large coordinates and frame decoding cancellation need a numerical contract. |
| `Cl(2,1)` spin presentation | Investigate after or alongside Lorentz adapter | Four even coordinates and sandwich reuse; sign quotient is essential. Must formalize Clifford realization, restricted group and kernel, and compare branch-free quotient meaning. No global canonical lift. |
| Euclidean PGA or CGA as a universal replacement | Defer | Different signature/grade/domain; spheres or incidence may justify a new consumer, but current framed disk motion does not. Euclidean mechanics evidence belongs with #311, not a hyperbolic stability claim. |
| Unrestricted projective or multivector motion carrier | Reject for this contract | Includes wrong sheets, null/noninvertible elements or points outside the metric domain. Add explicit validity structure before assigning the frozen meaning. |
| Floating-point backend replacement | Defer | Probe is bounded and noncertified; no general error propagation or admissibility guarantee. |

A bounded successor should first prove the exact Lorentz point/frame
round trips, identity/composition/inverse/action squares, and finite-list
comparison, consuming the existing native interface. Include the explicit
example above and a quarter-turn arrow case. A second seam can prove the
spin cover comparison while keeping the chosen sign out of ordinary
geometric observations. Both should expose deep operations to clients;
callers should not repeatedly discharge sheet inequalities, denominator
facts or coordinate casts. Model authors own those obligations once.
Neither successor should be blocked on a new frontend.

A numerical follow-up needs a declared compact domain or adaptive precision,
point **and** frame error norms, sound input/output guards, conversion error,
composition and decoding error, and a repeated-use budget. Test inverse
round trips, long boost/rotation sequences, boundary approach, and each
normalization policy separately. It may compare a Clifford-centered
implementation against matrix and native algorithms without assuming that
an adapter is the final architecture.

The [certified rational motion backend](numerical-motion.md) remains
unchanged. It models rational approximations and proved error budgets under
its stated compact-domain and input bounds. These binary64 experiments
are not an extension of that contract; the far-boundary cases are outside
its original compact domain.

Finally, constant curvature is a real scope restriction. A fixed
`SO⁺(2,1)` action cannot supply the full motion/connection semantics of an
arbitrary variable-curvature manifold or orbifold atlas. Tangent frames can
still use local linear representations, but path-dependent transport,
chart transitions and symmetry arrows require their own laws. Coordinate
changes are not automatically global isometries. Preserve the atlas/gauge
work of #408, the variational/mechanics investigation in #311, and the
local-composition investigation in #312 as separate consumers and
comparisons. This report neither rules out a wider groupoid interface nor
establishes a universal gyrovector or Clifford replacement for it.
