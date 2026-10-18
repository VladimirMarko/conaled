# Generalized gyrovector geometry and framed orbifold motion

Assessment for [#33](https://github.com/VladimirMarko/conaled/issues/33),
2026-10-18. This develops Response 2 of the
[historical chat](../history/orbifold/orbifold-simulator-chat.md).
The assessment proposes implementation boundaries. The implementation status
below records the subsequent checked geometry. Paper theorems, Isabelle proofs, mathematical arguments in this
note, and the Python probe have different proof status.

The recommended first implementation is exact framed motion in the disk,
with explicit symmetry arrows and interchangeable representations. Based
paths and transported frames provide a plausible general interface beyond
homogeneous spaces. Selecting a universal gyrovector algebra, general
orbifold foundation, or numerical integrator is premature.

## Conventional foundation follow-up (#40)

The [conventional orbifold assessment](conventional-orbifolds.md) supplies the
foundation/comparison plan alongside #39's exact projective motions. It starts
with explicit finite smooth actions, quotient diffeology and a coordinate
change retaining arrow and tangent information. Reuse the quarter-turn action
across these efforts; #39 continues to own the motion realizations. General
presentation descent and ineffective isotropy remain separate from a motion's
scalar redundancy. These conventional results are future comparison targets
for #36's constructed internal model, which remains a project goal.


## Experimental implementation (#39)

[ProjectiveMotion](../../Applications/Orbifold/ProjectiveMotion.lean) constructs
positive similitudes of a complex sesquilinear form as a subgroup of linear
equivalences, then quotients by the central subgroup of nonzero scalars.
Mathlib's group quotient supplies identity, composition and inverse. Its
projectivization action restricts to negative lines and descends to motions.
`ratio_preserved` proves preservation of the two-point invariant ratio;
`ratio_eq` and `vectorRatio_smul` establish representative independence.

[StandardForm](../../Applications/Orbifold/StandardForm.lean) supplies the
Hermitian form `conj(v₀)w₀-conj(v₁)w₁`, positive and negative vectors, and a
quarter-turn that moves the line through `(1/2,1)`. Scaling by two changes
vectors but gives the identity motion. These cases consume the public quotient
and action constructions. The generic algebra requires no signature assumption;
callers choosing another form must establish the intended geometric signature.
Composition applies the right operand first. These are exact noncomputable
real/complex semantics, with no executable numerical or rounding claim.

[Disk](../../Applications/Orbifold/Disk.lean) proves the negative-line/open-disk
equivalence, including the nonzero denominator and its inverse. The standard
form is proved nondegenerate. [Similitude matrices](../../Applications/Linear/Similitude.lean)
restrict Mathlib's arbitrary-basis decoder by the identity `A† J A = c J`.
The preservation correspondence and inverse encoding laws hold before scalar
quotienting. Identity, multiplication, inverse and represented point application
have squares; the multiplication square is the vertical paste of the linear
and projective layers. Basis changes give `C⁻¹ A C` and `C† J C`, and nonzero
scalar rescaling preserves the decoded motion.

[Pose](../../Applications/Orbifold/Pose.lean) defines gyroaddition and its
rotation correction independently of matrix multiplication. `matrix_comp`
proves the non-unit normalization factor, `motion_comp` proves common projective
meaning, and `motion_injective` recovers raw pose equality from that meaning.
The Möbius derivative and the curvature -1 frame convention satisfy `frame_comp`.
[MatrixDisk](../../Applications/Orbifold/MatrixDisk.lean) derives the matrix
fractional-linear action and its derivative, proves denominator validity, and
compares tangent actions for any certified representative decoding to a pose.
These tangent maps are derivatives of motions, not parallel transport along
chosen trajectories.

[QuarterTurn](../../Applications/Orbifold/QuarterTurn.lean) reuses the conventional
C4 disk action and its apex/regular stabilizers. Its pose action is free.
Prescribed right increments descend to orbits with identity and composition
laws; the action-groupoid functor retains symmetry labels. The `1/5`
counterexample checks both equal input orbits and unequal output orbits.
[DiskRealizations](../../Examples/DiskRealizations.lean) synchronizes the matrix
and gyro multiplication squares and proves agreement for arbitrary finite
compositions and frames. Retained cases swap the positive and negative basis
vectors, rescale by two, and use displacement `1/5` with turn `i`.

Callers supply certified matrix or pose domains, a basis for a matrix realization,
and a full frame when specifying body increments. Matrix normalization is
unnecessary. The abstraction does not classify all orientation-preserving
hyperbolic isometries, formalize a metric/connection or parallel transport,
or prove a discretization/rounding bound. General orbifold atlases, ineffective
symmetry, presentation descent and a simulator remain outside this experiment.
Scalar redundancy in a motion and finite symmetry identification of points
are separate quotients.

## Source comparison and hypotheses

The following sources support different constructions. Their names do not
license treating their interfaces as interchangeable.

### Gyrogroups and the AFP formalization

The AFP entry by Marić and Marković supplies Isabelle/HOL proofs of abstract
gyrogroup results and two-dimensional complex Möbius and Einstein models,
including comparisons to hyperbolic geometry. These are external checked
results, not Lean imports. [AFP entry](https://isa-afp.org/entries/GyrovectorSpaces.html).

Its `GyroGroup` theory assumes a left identity and inverse, gyrations that
are automorphisms, left gyroassociativity, and the left loop law;
gyrocommutativity is additional structure.
[Theory source](https://isa-afp.org/browser_info/current/AFP/GyrovectorSpaces/GyroGroup.html).

The `GyroVectorSpace` theory has several layers:

| AFP layer | Additional obligations |
|---|---|
| `gyrocarrier'` | Injective realization in a real inner-product space, taking gyrozero to zero |
| `gyrocarrier` | Gyrations preserve that inner product |
| `pre_gyrovector_space` | Scalar unit, scalar-addition and multiplication laws, preservation of normalized direction for positive scaling, gyration/scalar compatibility, trivial gyration for scalar multiples of one vector |
| `gyrovector_space_norms_embed` | An embedded signed-norm scalar carrier closed under the operations, norm homogeneity, and a gyrotriangle inequality |

These are actual source obligations, including the scalar norm operations
`oplusR` and `otimesR`. They cannot be inferred from algebraic gyrogroup laws.
[Inspected theory source](https://raw.githubusercontent.com/isabelle-prover/mirror-afp-devel/352a4e06c2e2c1dc358200e2a87bd930e458ca90/thys/GyrovectorSpaces/GyroVectorSpace.thy),
pinned at `352a4e06c2e2c1dc358200e2a87bd930e458ca90`. The AFP browser is a
moving reference; use the pinned source for this axiom comparison.

### Positive-definite matrices

Nguyen's Definition 2.3 requires gyrocommutativity and five scalar axioms:
unit/zero/inverse, scalar addition, scalar multiplication, compatibility with
gyrations, and trivial gyrations on scalar multiples of one element. It does
not supply AFP's inner-product embedding, direction, or norm axioms.
Theorem 3.6 treats real SPD matrices, positive parameter `r`, and positive
matrix powers. At `r = 1`,

```text
A ⊕ B = A^(1/2) B A^(1/2),       t ⊗ A = A^t.
```

These operations are global on SPD matrices. The log-Euclidean alternative
has `A ⊕ B = exp(log A + log B)` and identity gyrations. The Grassmann
construction instead excludes cut loci and weakens the reduction law;
some scalar laws have further parameter restrictions. These are materially
different hypotheses. [Nguyen, Definitions 2.3 and 3.5, Theorems 3.6, 3.10,
3.20](https://proceedings.neurips.cc/paper_files/paper/2022/file/a9ad92a81748a31ef6f2ef68d775da46-Paper-Conference.pdf).

The supplemental proof of Theorem 3.6 derives the gyration as orthogonal
conjugation. For `r = 1` its factor is
`F = (A^(1/2) B A^(1/2))^(-1/2) A^(1/2) B^(1/2)`.
The proof leaves several axiom verifications to the reader; it is a paper
proof, not a machine-checked instance. [Supplement, §14](https://proceedings.neurips.cc/paper_files/paper/2022/file/a9ad92a81748a31ef6f2ef68d775da46-Supplemental-Conference.pdf).

Recommendation: use SPD as a later independent application of algebraic
gyration interfaces. An AFP-style metric instance needs a chosen embedding
and separate proofs; this assessment neither asserts nor refutes its existence.

### Geodesic loops and double exponentials

Kikkawa's account constructs a geodesic local loop from a linear connection
using radial geodesics and parallel transport. Homogeneous left Lie loops
have stronger canonical-connection properties, including parallel torsion
and curvature. Those properties must not be attached to every geodesic
local loop. His curvature and torsion signs also require reconciliation
before transferring formulas. [Kikkawa, §§1.1, 1.3, 2.1](https://ir.lib.shimane-u.ac.jp/3358/files/8459).
This is the author's survey linked by the historical chat, not the original
1964 proof; it identifies that proof in reference [10].

Our proposed operational specialization is
`x ∘_o y = exp_x(P_(o→x)(log_o y))`.
Its domain must record an inverse branch of `exp_o`, the selected radial
path to `x`, existence of the second exponential, and, when returning a
tangent vector at `o`, membership of the result in the chosen log domain.
Shrinking neighborhoods can support a local loop; arbitrary pairs on the
manifold need not be admissible. This formula supplies neither a global
gyrogroup law nor path-independent transport.

Al-Kaabi, Ebrahimi-Fard, Manchon and Munthe-Kaas handle a general affine
connection by enlarging the algebra: Proposition 7 uses the free Lie
algebra over `C∞(M)` generated by vector fields, together with its tensor
algebra, and extends the connection product. The bracket is not simply the
ordinary Jacobi bracket on vector fields. Theorem 6 expresses the double
exponential through post-Lie Magnus operations on formal series. This does
not establish convergence or an error bound for a numerical scheme.
[Paper v1, §4.3 and §6](https://arxiv.org/html/2205.04381v1).
The free algebra is a possible source of expansion machinery; it does not
give a finite pose representation or prove descent across orbifold charts.

### Post-Lie integration under parallel curvature and torsion

Grong, Munthe-Kaas and Stava's Theorem 1.1 assumes a connected affine
manifold with `∇R = 0` and `∇T = 0`. Its carrier is
`Γ(TM) ⊕ Γ(hol)`, with `hol` the bundle of holonomy Lie algebras. In their
conventions,

```text
x ▷ y = ∇_x y,          [x,y] = -T(x,y) + R(x,y),
x ▷ E = ∇_x E,          [E,x] = -E x,
E ▷ y = E y,            [E,F] = -EF + FE,
E ▷ F = EF - FE.
```

The curvature term belongs to the endomorphism summand. For flat connections
with parallel torsion, vector fields with bracket `-T` suffice; flat
torsion-free connections give the pre-Lie case. Integration to global group
actions needs additional completeness, as §2.3 explicitly notes.
[Paper v2, Theorem 1.1 and §§2.1–2.3](https://arxiv.org/html/2305.02688v2).

Recommendation: postpone this numerical-integration route until a chosen
geometry and evolution law meet its hypotheses. A connection on a variable
curvature surface does not qualify merely because its covariant derivative
is defined. Neither cited post-Lie construction proves the chat's orbifold
extension.

## Frame development beyond homogeneous spaces

For a smooth effective Riemannian orbifold, Adem, Leida and Ruan construct
the orthonormal frame manifold with an almost free `O(n)` action recovering
the orbifold. Effectiveness makes the lifted finite chart actions free.
The residual `O(n)` action need not be free; its finite stabilizers recover
the original isotropy. The result does not require a global manifold
orbifold cover. [Orbifolds and Stringy Topology, §1.3, Theorem 1.23](https://www.math.colostate.edu/~renzo/teaching/Orbifolds/Ruan.pdf).

The following is the proposed interface derived from this construction,
not an already verified orbifold implementation. Assume compatible smooth
chart metrics and their Levi-Civita connections. On the frame manifold `P`,
use the solder form `θ` and connection form `ω` to identify
`T_p P` with `ℝⁿ ⊕ so(n)`. Define a controlled trajectory by

```text
(θ,ω)(p'(t)) = (v(t), Ω(t)).
```

The decomposition into horizontal and vertical frame directions is standard
connection geometry; the cited post-Lie paper gives the corresponding frame
fields and their brackets. [Grong et al., §3.1](https://arxiv.org/html/2305.02688v2).
For the proposed Levi-Civita interpretation, `Ω = 0` transports the frame
parallelly, and constant `v` gives geodesic motion. General controls require
an ODE existence interval; neither frame coordinates nor the algebra imply
complete flows. Cartan development here does not identify an arbitrary
curved geometry with a fixed transformation group.

If isotropy acts ineffectively, a nonidentity element acting trivially on a
chart also fixes every frame in that chart. Consequently the lifted action
is not free. A coarse frame manifold obtained by forgetting that kernel
would lose symmetry arrows. Support for such orbifolds must retain a frame
groupoid or additional ineffective-group data; it is an unresolved extension
of the proposed effective interface.

## Proposed based displacement contract

Keep representative changes and physical paths as distinct data. A symmetry
arrow identifies two local descriptions; a physical path can change position
without defining an orbifold automorphism. This distinction permits motion
between regular and singular strata without asserting a transitive symmetry
of the position orbifold.

The contract below is a design proposal with explicit proof obligations.

1. **States and domains.** A lifted state includes a chart point `x`, an
   orthonormal frame `u : ℝⁿ → T_x U`, and any mechanical variables. An
   admissible command has a duration, controls, and a domain witness for its
   solution. A one-step exponential additionally carries its log/exponential
   domain conditions. Chart exit requires an explicit transition or a new
   segment.
2. **Source and target.** A displacement has a source framed state and a
   target framed state, with its developed path or equivalent semantic data.
   Compose only when the first target equals the next source, or after
   inserting a specified representative-change arrow. Endpoints alone do
   not determine transport.
3. **Frame transport.** Record the path's parallel transport map. It preserves
   the metric for Levi-Civita transport. Turning commands add the explicitly
   prescribed vertical frame evolution. Do not interpret every such change
   as parallel transport.
4. **Chart equivariance.** For a connection-preserving chart map `φ`, the
   lifted change is `(x,u) ↦ (φ(x),Dφ_x ∘ u)`. Require the developed solution
   and transport to commute with this change on common valid domains.
   In particular, `Dφ_y ∘ P_c = P_(φ∘c) ∘ Dφ_x`. The symmetry label and
   its source/target evidence remain available after the change.
5. **Frame relabeling.** With the right convention `u ↦ u k`, transform
   body controls by `(v,Ω) ↦ (k⁻¹v,k⁻¹Ωk)` for constant `k ∈ O(n)`.
   This preserves the underlying physical path. A time-dependent relabeling
   also needs its derivative contribution to the connection component.
6. **Composition and equality.** Use piecewise smooth paths with explicit durations, so
   concatenation joins matching endpoints and adds durations. Transport
   satisfies `P_(c₂*c₁) = P_c₂ ∘ P_c₁`; zero-duration constant paths give
   composition identities, and reversed paths give inverse transport.
   A positive-duration constant path has identity transport but retains its
   elapsed time. Associativity is available for path
   concatenation with appropriate parametrization conventions. It does not
   imply associativity of projected endpoint addition. Any later quotient
   of paths must state which observations it preserves; ordinary homotopy
   does not preserve transport for a curved connection.

For the homogeneous frame model, take a Lie group `G`, a closed discrete
subgroup `Γ`, and the appropriate compact frame subgroup `K`; the intended
position model is `Γ\(G/K)`. Left multiplication by `Γ` on `G` is free
and proper, so `Γ\G` is a manifold even when the position action has
stabilizers. A fixed body increment `h ∈ G` has
the exact update `Γg ↦ Γ(gh)`. Associativity gives
`(γg)h = γ(gh)`, hence representative independence and
`(Γg·h₁)·h₂ = Γg·(h₁h₂)`. These are right-action laws. Multiplication
of arbitrary cosets would require additional normality and is not proposed.
A state-dependent body increment must satisfy `h(γg)=h(g)` for this simple
descent proof; more general commands require their stated equivariance law.

Connection holonomy records parallel transport around loops. Isotropy
records automorphisms of a particular orbifold object. They can interact
when a lifted loop closes by a chart symmetry, but one does not determine
the other. Flat rotation quotients with different finite rotation groups
already have the same zero chart curvature and different apex isotropy.
Conversely, a curved manifold has trivial orbifold isotropy while transport
can have nontrivial holonomy. A displacement implementation must retain both
the transport and the closing symmetry arrow.

## Recommendation and unresolved scope

Reject a transitive point arithmetic required to preserve all orbifold
stabilizers, arbitrary-representative quotient addition, and silently
globalized logarithms. Reject assigning post-Lie laws directly to ordinary
covariant differentiation on a general curved manifold. Retain gyrogroups
as useful specialized algebra and framed paths as the broader candidate
interface.

Implementable follow-up slices, in dependency order:

1. Formalize the exact disk action and quarter-turn symmetry, including
   representative changes and the flat specialization. Prove the independent
   representative counterexample before defining any quotient operation.
2. Connect gyro-plus-rotation and projective matrices to common action
   semantics; transport laws through the shared categorical interfaces.
3. Formalize path-indexed frame transport for one chosen connection and its
   chart-equivariance theorem. Include a variable-curvature test to prevent
   homogeneous assumptions entering the interface.
4. Assess a chosen integrator only after fixing its dynamics, time interval,
   norm, and domain. Prove discretization and floating-point contracts
   separately. Post-Lie machinery is conditional on that choice.

Open decisions are the scope of effective versus ineffective orbifolds,
which path observations define semantic equivalence, whether the next
nonhomogeneous example needs multiple charts, and which mechanical system
justifies an integrator. General presentation equivalence and descent remain
research tasks. The exact homogeneous slice can proceed without resolving
all of them.

## Exact disk realizations and shared law transport

This section records the design that preceded #39. Its disk constructions
now have the checked implementations listed above; the Lorentz, connection
and numerical-error extensions remain proposals. The semantic types describe
geometric points and motions; coordinates and storage belong to realizations.

### Geometric types before coordinates

For this homogeneous slice, take a complex vector space `V` of dimension two
with a nondegenerate Hermitian form `H` of signature `(1,1)`. A point is a
negative complex line in `V`: a projective class `[v]` with `H(v,v) < 0`.
The sign is independent of the nonzero representative because
`H(λv,λv)=|λ|² H(v,v)`. In a basis where the form is
`H(v,w)=conjugate(v₀)w₀-conjugate(v₁)w₁`, the chart
`[v] ↦ v₀/v₁` gives the disk. Negativity ensures `v₁ ≠ 0`.
The standard negative-line construction and projective unitary action are
described in [Parker, §§2.2 and 3.3](https://www.maths.dur.ac.uk/users/j.r.parker/img/NCHG.pdf);
here we specialize the construction to signature `(1,1)`.

Define the proposed motion carrier as projective classes of complex linear
equivalences `L : V ≃ₗ[ℂ] V` satisfying

```text
∃ c : ℝ, 0 < c ∧ ∀ v w, H(L v,L w) = c H(v,w).
L ~ L'  iff  L' = λ • L for some nonzero complex λ.
```

These are positive Hermitian similitudes modulo scalars. Composition multiplies
the positive factors, inversion reciprocates them, and scalar multiplication
changes the factor by `|λ|²`. They therefore act on negative lines by
`[L] • [v] = [L v]`. The invariant ratio
`|H(v,w)|² / (H(v,v) H(w,w))` is preserved, giving the hyperbolic distance
contract after choosing the curvature `-1` normalization. This specifies
the orientation-preserving motion model; identifying it with all
orientation-preserving hyperbolic isometries is a separate completeness
theorem. Complex-antilinear maps would be needed to include reflections.

The useful public operations are identity, composition, inverse, point
action, and the induced frame action. A lifted pose can be recovered as the
image of a chosen reference frame. The scalar quotient here removes redundant
linear representatives of one motion. The orbifold identification by `Γ`
is a later, different quotient whose symmetry arrows must remain explicit.

### Families of realizations

For each finite basis `β`, let `Jβ` represent `H`. A matrix realization has
invertible matrices `A` with `A* Jβ A = c Jβ` for some `c > 0`, where `A*`
is conjugate transpose. Its decoder first uses `Matrix.toLin β β`, then
takes the projective class of the resulting similitude. This is the
coordinate expression of the abstract preservation property. It need not
be the public definition of a motion.

```text
certified matrices in basis β → Hermitian similitudes → projective motions
gyro-plus-rotation coordinates ───────────────────────→ projective motions
```

These arrows form successive exact representation layers. Before projective
quotienting, a basis gives an equivalence between the certified matrices and
the abstract similitudes. After quotienting, decoding is intentionally
many-to-one. A change of basis, with `C` taking new coordinates to old ones,
changes `A` to `C⁻¹ A C` and `J` to `C* J C`, preserving the decoded motion.
No preferred basis or matrix normalization belongs in the geometric interface.

Use [`MatrixBackend`](../../Applications/Linear/Matrix.lean)'s existing
matrix-to-linear-map squares for the coordinate-vector case. Mathlib's
[`Matrix.toLin` and `LinearMap.toMatrix`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/ToLin.lean)
provide the arbitrary-basis version, with inverse and composition theorems.
Restrict those decoders to the preservation subtypes and prove closure of
the operations. Then use `Squares.Rep.after` and `Squares.vertical` to
compose with projective motion semantics. The intermediate linear maps are
specification data; a concrete matrix implementation need not store them.

The pinned Mathlib also supplies the
[sesquilinear-form/matrix correspondence](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/SesquilinearForm/Star.lean)
and a [linear group action on projectivization](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Projectivization/Action.lean).
These Mathlib ingredients supplied the starting point. `ProjectiveMotion`,
`Disk`, `Pose` and `MatrixDisk` now prove negative-line preservation, scalar
descent and the disk/frame comparison.

Preserve only the operations closed on the motion carrier. Adding two valid
motion matrices can produce a singular matrix, so the matrix backend's
addition square and its full linear compiler cannot be inherited wholesale.
Composition, identity, inverse, and action are the relevant contracts.
`Squares.product` still combines represented inputs, for example a motion
and a point; it does not assert closure under matrix addition.

Gyro-plus-rotation is another exact realization of these motions. A real
Lorentz realization would instead use sheet- and orientation-preserving
isometries of a quadratic space of signature `(2,1)`, then choose a basis for
real matrices. Mathlib's
[`QuadraticMap.IsometryEquiv`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean)
already expresses the form-preserving linear equivalence. The sheet/orientation
restrictions and its comparison with projective motions remain obligations.
That comparison is between geometric models, not a change of basis between
complex two-dimensional and real three-dimensional spaces. Storage layouts
or factored products can supply further realizations once their decoding and
operation laws are proved. No numerical performance ranking is implied.

### Disk coordinates as a specialization

The following formulas fix the conventions of the preserved
[probe](../history/orbifold/orbifold_gyro_probe.py).
Let `D = {z : ℂ | |z| < 1}` and let a pose be `(a,u) ∈ D × U(1)`, denoting

```text
δ(a,u)(z) = (a + u z) / (1 + conjugate(a) u z).
a ⊕ b = (a+b)/(1+conjugate(a)b).
gyr(a,b) = (1+a conjugate(b))/(1+conjugate(a)b).
(a,u) ⋆ (b,v) = (a ⊕ (u b), gyr(a,u b) u v).
M(a,u) = [[u, a], [conjugate(a) u, 1]].
```

Here `p ⋆ q` denotes `δ(p) ∘ δ(q)`. All disk-action denominators are nonzero
because the product of the relevant norms is less than one. The identity
`1-|a⊕b|² = (1-|a|²)(1-|b|²)/|1+conjugate(a)b|²` proves disk closure;
the numerator of `gyr` is the conjugate of its denominator, proving unit norm.
The matrix determinant is `u(1-|a|²)`, hence nonzero. Direct multiplication
also gives `M(a,u)† J M(a,u) = (1-|a|²) J` for `J=diag(1,-1)`,
where `†` denotes conjugate transpose. Thus the probe's matrix
represents a positive Hermitian similitude. It generally does not preserve
`J` with scale exactly one; the projective semantics makes that normalization
unnecessary. Matrix multiplication
gives `M(p) M(q) = λ M(p⋆q)`, where
`λ = 1+conjugate(a) u b ≠ 0`. Thus matrix multiplication preserves the same
action **projectively**, rather than as equality of these normalized matrices.
The preservation certificate supplies the required restriction; arbitrary
invertible complex matrices need not preserve `D`.

Prove that both realizations decode to the projective motions above and that
their induced disk action satisfies `δ(p⋆q)=δ(p)∘δ(q)`. Equality
of actions gives semantic associativity. To obtain literal equality of pose
pairs, also prove faithfulness: evaluation at zero recovers `a`, and the
derivative there is `u(1-|a|²)`, recovering `u`. A point observation alone
would lose orientation. With the curvature `-1` metric, the orthonormal frame
at `a` represented by `u` is `e(w)=(1-|a|²)u w/2`. This distinguishes a unit
complex phase from the coordinate length of a metric-unit tangent vector.

SquareKit already supplies the required semantic maps, law transport, comma
squares, and agreement constructions. Its
[implementation record](felix-parity-implementation.md) documents the Felix
port and local extensions, including
[closed law transport](../../SquareKit/ClosedMap.lean), which completes the
corresponding upstream TODO. The disk realization should instantiate these
existing interfaces:

| Obligation | Existing interface and application |
|---|---|
| Operations before laws | [`CategoryOps`, `HomEquiv`](../../SquareKit/Category.lean); view global motions as a one-object category, or endpoint-indexed paths as a category after choosing reparametrization semantics. |
| Semantic composition and law transport | [`RawMap`, `MapLaws`, `induced`, `transportLaws`](../../SquareKit/CategoryMap.lean). Use action equality as induced equivalence; separately prove reflection if requesting raw pose equality. |
| Implementation of a prescribed right increment `h` | [`Squares.Square`](../../Squares.lean), with `δ(I_h p)=δ(p)∘δ(h)`. Composition of squares handles finite sequences. |
| Agreement of independent realizations | [`synchronized`, `synchronize`](../../SquareKit/Combinators.lean), or [`Comma.Exact.agreement`, `agree_comp`](../../SquareKit/CommaAgreement.lean), with the same semantic operation on both sides. |
| Explicit identification arrows | Mathlib action groupoids and functors, adapted through `RawMap.ofFunctor`; retain labels rather than inducing arrow equivalence from coarse position observations. |

The implementation now proves disk closure, faithful pose decoding,
preservation and equivariant action-groupoid adapters using the shared
foundation. General smooth presentation equivalence and descent remain
outside this construction and require more than a commuting square.

The implemented realization connects certified matrices to abstract linear
equivalences and then the scalar quotient and point action. The retained basis
swap and non-unit scalar case consume the general preservation results. The
disk specialization proves the displayed similitude identity for every
admissible `(a,u)` and agreement of independently composed matrices and poses,
including their frame actions.

There are three separate contracts. Exact coordinate and projective-matrix
realizations preserve the same ideal finite step. Approximating continuous
development by that step needs a discretization theorem. Evaluating its
formulas in floating point needs a rounding theorem and domain guarantees.
For example, a proved error recurrence might have the form
`e_(n+1) ≤ L_n e_n + τ_n + ρ_n`, with a stability constant, local truncation
bound and rounding bound in a stated metric. This is a proposed obligation,
not a bound supplied by the probe. [`RelSquare`](../../SquareKit/Relations.lean)
can compose such contracts once the error budget and validity domain are in
the relation; it does not supply the analytic estimates.

## Required examples and evidence

### Flat framed motions

On Euclidean space with its standard connection, a pose `(x,R)` denotes
`z ↦ x+Rz`. Composition is `(x,R)⋆(y,S)=(x+Ry,RS)` and the homogeneous
matrix is `[[R,x],[0,1]]`. Associativity follows by expanding both sides;
parallel transport is the identity in the standard coordinates. This is a
mathematical specialization of the framed interface, with no Lean proof added
here. For a finite orthogonal symmetry group, relabel both components by
`γ·(x,R)=(γx,γR)`. Then `γ·(p⋆h)=(γ·p)⋆h` for a fixed body increment.

Flat quotients `ℝ²//C₂` and `ℝ²//C₃` have trivial connection holonomy upstairs
but different origin stabilizers. Quotient loops can combine transport with
a symmetry identification. This does not make a stabilizer group identical
to connection holonomy, or allow curvature alone to recover isotropy.

### Quarter-turn hyperbolic cone

For `Γ=C₄`, `k·(a,u)=(i^k a,i^k u)`. The identity
`(γg)h=γ(gh)` proves that the right action on `Γ\G` is independent of the
chosen representative of `g`. It does not define multiplication of arbitrary
left cosets. Nor does an arbitrary right increment descend through the further
quotient by the frame rotation subgroup `K`: changing `g` to `gk` changes the
body direction of that increment. Retaining the frame is therefore part of
the input contract.

At the position `0`, all four rotation labels are isotropy arrows; away from
zero the stabilizer is trivial. On full poses the action is free since
`i^k u=u` forces `i^k=1`. The framed space's right rotation action recovers
the position isotropy. A transitive family of orbifold equivalences on position
space is impossible: each equivalence induces an isomorphism of automorphism
groups, whereas `C₄` and the trivial group are not isomorphic. This argument
does not forbid a lifted trajectory from crossing the apex.

### Independent representatives fail

Retain the chat's exact counterexample on `D//C₂`: choose `a=1/5`.
Then `a⊕a=5/13`, while `a⊕(-a)=0`. The second arguments represent the same
orbit, but the outputs do not. The same counterexample works for `C₄`, since
a nonzero point cannot lie in the zero orbit. Simultaneous equivariance
`γ(a⊕b)=(γa)⊕(γb)` therefore does not imply independent-representative
invariance. `QuarterTurn.quotient_addition_values`, `second_inputs_same_orbit`
and `addition_outputs_different_orbits` now check the C₄ counterexample in
Lean. The reused conventional C₄ action supplies the checked apex and
regular-point stabilizer results.

### Variable curvature limits the homogeneous and post-Lie routes

Consider `ℝ²` with `g=e^(2x²)(dx²+dy²)` and its Levi-Civita connection. A
coordinate calculation gives
`Γ¹₁₁=2x`, `Γ¹₂₂=-2x`, `Γ²₁₂=Γ²₂₁=2x`, with other coefficients zero.
Using `R(X,Y)Z=∇_X∇_Y Z-∇_Y∇_X Z-∇_[X,Y]Z` gives
`R(∂x,∂y)∂y=-2∂x`, hence Gaussian curvature `K=-2e^(-2x²)`.
Its derivative is `8x e^(-2x²)`, nonzero when `x≠0`; thus `∇R≠0` there.
Torsion is zero. A transitive isometry model would force the scalar curvature
invariant to be constant, so this is not such a homogeneous model. It also
fails the parallel-curvature hypothesis of the finite-rank holonomy enlargement
post-Lie construction. Local exponential maps and framed development remain
available on their existence domains. This is an explicit mathematical
calculation illustrating the limit, not a numerical test or Lean theorem.

### Reproduced numerical evidence

Running `direnv exec . python3 docs/history/orbifold/orbifold_gyro_probe.py`
on 2026-10-18 passed every existing assertion, using 1,000 samples and seed
1729. Maximum coordinate residuals were approximately `7.45e-16` for framed
associativity and `4.52e-16` for agreement with projective matrices. The
40-step diameter trajectory agreed with its analytic formula to `3.89e-16`.
Changing position alone during relabeling produced the deliberately failing
residual `0.11224`; position-only associativity had sampled defect `0.18139`.
These are reproducible floating-point observations in the sampled region.
They establish neither universal identities nor intrinsic error bounds.
The historical probe was not changed. The original numerical assessment adds no Lean claims. The implementation
status above lists the subsequent checked results.
