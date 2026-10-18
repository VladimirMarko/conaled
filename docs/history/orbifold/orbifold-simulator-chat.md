Prompt 1:
````md
Do you have the Lean toolchain available? (This seems to vary with ChatGPT sessions.) 
Read "Orbifolds as microlinear types in synthetic differential cohesive homotopy type theory" (https://arxiv.org/abs/2205.15887).
I want to do some simulations with objects moving in orbifolds. Would the above be any help in that regard?
Even in three-dimensional Euclidean space the, nicest way of describing objects and their movement is not settled, with some advocating representations in terms of Clifford algebras (or "geometric algebras") in recent years.
There is also the path of using a very elegant specification and connecting it with proofs to an arbitrarily elegant implementation via something like the Felix library (https://github.com/conal/felix/).
What options exist or are conceivable to develop for orbifolds?
````

Response 1:
````md
**There is no Lean toolchain available in this session:** I checked for `lean`, `lake`, and `elan`, and none is available. I have not type-checked anything in Lean here.

**Yes—the paper could help, particularly with the specification and proof architecture. But I would not make its entire foundational framework a prerequisite for getting simulations running.** My preferred approach would combine an intrinsic specification with an explicit, computable presentation of the orbifold, then use conventional numerical geometry inside that presentation.

Your three interests are compatible rather than competing:

> Synthetic geometry can describe what the system means; groupoids or atlases can represent the space; geometric algebra can implement local geometry; refinement proofs can connect these layers.

The important questions are where to draw the boundaries, and which properties must survive each translation.

## 1. What the paper contributes

Myers’ central definition makes an orbifold a **microlinear type \(Q\) whose identity types \(x=y\) are properly finite**. These identity types retain isotropy rather than merely identifying points in an orbit. Infinitesimals give the tangent construction
\[
D=\{\varepsilon:R\mid \varepsilon^2=0\},
\qquad
TQ=Q^D.
\]
Microlinearity supplies coherent \(R\)-module structures on tangent spaces. Theorem 6.3.7 shows that the Rezk completion of a crisp ordinary proper étale pregroupoid satisfies the definition. This provides a bridge from conventional orbifolds into the synthetic framework, not an algorithm extracting executable atlases from arbitrary synthetic types. [arXiv](https://arxiv.org/html/2205.15887v1)

A crucial distinction is that **identifications \(x=y\) are not time-parametrized movements**. A trajectory is a smooth map \(I\to Q\), with \(I\) a real interval; an isotropy automorphism is not a little physical journey. For simulation, the paper offers intrinsic differential geometry, not a metric, force law, time-stepping scheme, or numerical-error bound. Microlinearity alone also does not promise finite-dimensional computational data. [arXiv](https://arxiv.org/html/2205.15887v1)

My assessment is that this is valuable as a *specification language*: one can formulate tangent vectors, bundles, transformations, and compatibility laws without making a particular atlas part of their meaning. That matters when comparing implementations.

But the implementation still needs answers to questions such as “Which coordinates are stored?”, “How is a chart transition computed?”, and “What happens when a numerical step approaches a singular stratum?” An elegant intrinsic definition does not itself answer those questions.

## 2. The most direct computational approach: simulate upstairs, retain the symmetries

Start with an orbifold presented as
\[
Q=M//\Gamma,
\]
where \(\Gamma\) is a discrete group acting properly on a manifold \(M\), with finite stabilizers. Here `//` denotes the quotient retaining the action and its identifications, not merely the set of orbits. This is the action-groupoid viewpoint. [math.colostate.edu](https://www.math.colostate.edu/~renzo/teaching/Orbifolds/Ruan.pdf)

The computational idea is to store a representative upstairs in \(M\), together with enough information about the identifications.

First choose the **state space**, which need not be the ambient orbifold. For point-particle mechanics, position alone is insufficient: one normally uses position and velocity, or position and momentum. In the following construction, let \(\widetilde S\) be the lifted state space and let
\[
\rho_g:\widetilde S\to\widetilde S
\]
be the action of \(g\in\Gamma\) on the *whole* state.

A lifted differential equation
\[
\dot z=F(z)
\]
is compatible with the quotient when
\[
F(\rho_g z)=D\rho_g(z)\,F(z).
\]
This is equivariance: equivalent descriptions receive equivalent velocities.

For an ideal numerical step \(\Psi_h\) to descend **exactly** to the quotient, the corresponding condition is
\[
\Psi_h(\rho_g z)=\rho_g\Psi_h(z).
\]
These two conditions are different. The differential equation can possess a symmetry that a discretization fails to preserve.

In the flat, affine-action case, there is a useful advantage: ordinary Runge–Kutta methods respect affine symmetries in exact arithmetic. This is connected to the characterization of B-series methods by affine equivariance. Arbitrary nonlinear coordinate changes do not enjoy the same property. [arXiv](https://arxiv.org/abs/1409.1019)

For example, Euler stepping before and after a nonlinear coordinate transformation \(\phi\) generally gives different answers:
\[
\phi(x+hF(x))
\ne
\phi(x)+hD\phi_xF(x).
\]
The discrepancy is visible just by expanding the left side. Thus, “coordinate-independent differential equation” does not automatically mean “coordinate-independent finite-step algorithm.”

There are two reasonable responses: choose an intrinsically defined geometric integrator, or accept a coordinate-dependent algorithm and prove its intrinsic approximation error. What would be wrong is claiming exact representation independence without establishing it.

### The seam is not a physical wall

My implementation prescription would be to retain a lift as long as convenient, rather than repeatedly forcing the state into a fundamental domain.

When changing representatives, transform everything:
\[
x\mapsto gx,\qquad
v\mapsto Dg_xv.
\]
Momentum, orientation, attached tensors, and internal states require their corresponding transformations too. Moving the position across a seam while leaving the velocity or orientation unchanged describes a different motion.

I would also keep group elements symbolically, with exact multiplication, rather than identify them by approximate matrix equality. Numerical evaluation of their action can then have its own error bound.

An ordinary solver such as SciPy’s `solve_ivp` can supply the upstairs ODE solver for an initial experiment; its documented functionality is ordinary initial-value integration, so the quotient handling and its correctness would be your additional layer. [SciPy Documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.solve_ivp.html)

## 3. A small example that exposes the main issues

Consider
\[
Q=\mathbb R^2//C_n,\qquad n\ge2,
\]
where a generator \(R\) rotates through \(2\pi/n\).

Represent the particle’s phase space by
\[
S=(\mathbb R^2\times\mathbb R^2)//C_n,
\]
with the diagonal action
\[
R\cdot(x,v)=(Rx,Rv).
\]

Free motion upstairs is
\[
\dot x=v,\qquad \dot v=0,
\]
with exact step
\[
\Psi_h(x,v)=(x+hv,v).
\]

The compatibility proof is immediate:
\[
\begin{aligned}
\Psi_h(Rx,Rv)
 &= (Rx+hRv,Rv)\\
 &= R\cdot(x+hv,v)\\
 &= R\cdot\Psi_h(x,v).
\end{aligned}
\]

So the same formula handles trajectories passing through the cone point. Nothing in this model requires a singular force or a special boundary rule there.

There is a subtlety that is easy to miss. A smooth **position-dependent vector field** \(W\) on this orbifold must satisfy
\[
W(0)=RW(0),
\]
hence \(W(0)=0\). It cannot prescribe a preferred nonzero direction at the apex.

But this does **not** imply that a moving particle cannot pass through the apex. Particle mechanics uses the state \((x,v)\), not just \(x\). When \(v\ne0\), the phase-space point \((0,v)\) has trivial stabilizer under this rotation group, even though its position has stabilizer \(C_n\). The velocity supplies information that position alone lacks.

This is a strong reason to distinguish:

- the ambient orbifold;
- the configuration or phase space;
- the coarse picture used for display.

There is also a modeling choice about what “geodesic” means. An orbifold geodesic, defined by locally lifting to a geodesic in a smooth chart, need not be locally distance-minimizing in the coarse metric when it passes through a singularity. Lange discusses this distinction explicitly. A shortest-path simulation, a smooth orbifold-mechanics simulation, and a collision/billiard model can therefore require different behavior. [arXiv](https://arxiv.org/html/1703.00850v2)

For a closed trajectory, one may additionally need to retain an identification such as
\[
x(T)=g\,x(0),\qquad v(T)=Dg\,v(0).
\]
The group element \(g\) can matter for transporting an attached orientation or internal state even when the displayed position has returned to its starting point.

## 4. What to do beyond a single discrete-group quotient

### Atlases and proper étale groupoids

The broadly applicable presentation is a proper étale groupoid
\[
G_1\rightrightarrows G_0.
\]
Operationally, \(G_0\) supplies smooth local representatives and \(G_1\) supplies identification arrows. The usual orbifold chart and orbibundle constructions fit this framework. [math.colostate.edu](https://www.math.colostate.edu/~renzo/teaching/Orbifolds/Ruan.pdf)

A simulation state can then contain a chart identifier, local coordinates, local velocity or pose, and the arrows used when changing representatives. The proof obligations concern transition maps and their compositions, not merely equality of displayed coordinates.

This route is needed when there is no global manifold orbifold cover. The teardrop is a standard example. Importantly, that does **not** mean it has no global quotient presentation of any kind: it can be represented as a weighted \(S^1\)-quotient of \(S^3\). The distinction is between a discrete-group covering presentation and a more general Lie-group quotient. [math.colostate.edu](https://www.math.colostate.edu/~renzo/teaching/Orbifolds/Ruan.pdf)

For such a Lie-group quotient, my proposed implementation would use constrained or horizontal dynamics upstairs, chosen to project to the intended dynamics downstairs. Simply integrating an arbitrary upstairs equation would not establish that correspondence.

### A particularly attractive alternative for moving objects: frames

For an effective Riemannian \(n\)-orbifold, the orthonormal frame space is a smooth manifold, and the orbifold can be recovered as
\[
Q\simeq \operatorname{Fr}(Q)//O(n).
\]
The \(O(n)\)-action has finite stabilizers; it need not be free. This is the standard frame-bundle presentation of effective orbifolds. [arXiv](https://arxiv.org/pdf/math/0107168)

This suggests an appealing computational option: **add a full frame to the state and work on a manifold**. In dimension three the frame manifold has dimension six, so this also resembles a position-and-orientation representation.

For a small framed object, I would investigate \(\operatorname{Fr}(Q)\) as the pose space. For an object with a finite intrinsic symmetry group \(H\), a natural proposed pose model is
\[
\operatorname{Fr}(Q)//H.
\]
In this construction, some symmetry that was removed by specifying a complete frame is deliberately restored by forgetting distinctions the object itself does not possess.

There are limits to this proposal. A frame describes local pose, not automatically an extended rigid solid in arbitrary curved geometry. The latter needs a model of the object’s shape, admissible placements, and collisions. Also, ineffective isotropy is not removed by the effective-orbifold frame theorem.

The same distinction between ambient and configuration space appears with identical particles. A natural construction is
\[
(M^N)//S_N,
\]
where permutations encode indistinguishability. Coincidences create stabilizers; removing all coincidences makes the permutation action free. Here orbifold structure arises from the objects’ configuration, even if the ambient \(M\) is an ordinary manifold.

### Coarse coordinates and meshes are another option—but specify what they forget

For some tasks, a metric-space or mesh representation of the coarse quotient may be enough. I would regard that as a legitimate, deliberately weaker model, not as an intrinsically incorrect one.

The danger is silently expecting it to retain isotropy and transport data. A useful design is to let a coarse representation handle visualization or spatial queries while the authoritative state retains the groupoid information.

## 5. Where Clifford or geometric algebra fits

I would not pose the decision as “geometric algebra versus orbifold geometry.” Geometric algebra can implement parts of the local or upstairs geometry while the quotient structure is represented separately.

For flat three-dimensional geometry, projective geometric algebra is relevant because it treats points, lines, planes, and Euclidean motions within one algebraic framework. Gunn’s account also explains its relationship to quaternion and dual-quaternion representations and its use in kinematics. [arXiv](https://arxiv.org/html/1901.05873v2)

Thus, for a flat quotient, one could use matrices, quaternions, dual quaternions, or projective geometric algebra to implement the upstairs transformations. The orbifold-specific question remains:

> How does each identification act on every component of the physical state?

For a general metric orbifold, the natural construction is not one global Euclidean Clifford algebra, but a **Clifford algebra orbibundle**
\[
\mathrm{Cl}(TQ,g).
\]
The construction is local: form the Clifford algebra of each tangent space, let local isometries induce algebra isomorphisms, and glue using the orbifold identifications. This combines the ordinary equivariant-bundle construction with the functoriality of Clifford algebras. [arXiv](https://arxiv.org/pdf/math/0107168)

It would generally be a mistake simply to take orbits of individual multivectors and assume multiplication remains well defined. Choosing different representatives independently can change the product. Fiberwise operations with explicit transport avoid that problem.

Two distinctions also matter. Rotors handle orientation-preserving rotations; reflections require the corresponding broader versor/Pin treatment. And using local quaternion or rotor coordinates does not itself require a global spin structure, whereas a globally defined spinor field requires compatible spin lifts of the orbifold isotropy actions. Such lifts are additional structure, not automatic. [arXiv](https://arxiv.org/abs/1101.4542)

My preference would be to give each algebraic backend a denotation into the same geometric specification. Then “matrix implementation versus geometric-algebra implementation” becomes a concrete question about proofs, performance, numerical conditioning, and usability—not a prerequisite for settling the whole geometry.

## 6. A Felix-like architecture is plausible—and need not start with all of cohesive HoTT

Felix describes itself as an **Agda category-theory library for denotational design**. That makes it relevant infrastructure and a useful design precedent, but it should not be mistaken for an already implemented orbifold compiler or a numerical-analysis verification framework. [GitHub](https://raw.githubusercontent.com/conal/felix/main/readme.md)

There is an especially relevant middle route: **tangent categories**. Cockett, Cruttwell, and Lemay develop differential equations, vector fields, and flows abstractly in this setting. This provides a way to abstract differential structure without immediately adopting the whole synthetic differential cohesive foundation. [arXiv](https://arxiv.org/abs/1911.12120)

I would investigate a tangent-category-inspired interface containing a tangent operation \(T\), tangent projections, differentiation of maps, and the required compatibility laws. Metrics, connections, group actions, and mechanical systems would be additional structure.

For orbifolds, this interface must also account for identifications between maps. It is not enough merely to import a one-categorical interface and assume all the higher coherence questions have disappeared. Establishing the interpretation in the chosen groupoid or stack semantics would be part of the project.

There is existing dynamics theory to build on: Hepworth develops vector fields and flows on differentiable stacks, including existence and uniqueness, up to the appropriate uniquely determined 2-cell, for flows on compact proper differentiable stacks. This is more directly about dynamics than the microlinearity paper. [arXiv](https://arxiv.org/pdf/0810.0979)

### The refinement boundary I would use

I would separate four kinds of correctness.

**Presentation correctness.** Different charts, quotient representatives, or equivalent groupoid presentations describe the same geometric state. The denotation must preserve identification arrows and their composition, not merely send both representations to the same coarse point.

**Exact implementation correctness.** Let \(\Psi_h\) be an ideal mathematical *discrete* step, \(I_h\) its implementation over exact scalars, and \(\delta\) the denotation of representations. The desired statement is schematically
\[
\delta\circ I_h \simeq \Psi_h\circ\delta.
\]
The equivalence may be an isomorphism of the relevant geometric maps rather than literal equality of stored coordinates.

**Discretization correctness.** Separately, prove that repeated ideal steps approximate the continuous flow \(\Phi_t\). This is where the order of the method, regularity assumptions, stability, and existence interval enter.

**Machine-arithmetic correctness.** Finally, account for floating-point evaluation, approximate transformations, chart-validity checks, and accumulated rounding errors.

Combining the latter two might produce a theorem of the form
\[
d_{|S|}
\!\left(
\operatorname{decode}(\widehat I_h^{\,N}(r_0)),
\Phi_{Nh}(\operatorname{decode}(r_0))
\right)
\le C_T h^p+E_{\mathrm{fp}}(N,h),
\qquad Nh\le T,
\]
where the comparison takes place in a chosen metric on the coarse state space. This is a *target theorem*, with hypotheses to establish for the particular system and method—not a guarantee for arbitrary orbifolds or arbitrary code.

The metric estimate is not the whole correctness statement. It does not, by itself, verify the isotropy action or the identification accumulated around a loop. Those need separate exact structural guarantees, together with bounds on any numerical evaluation of that structure.

This separation is important for the kind of elegance you are after. Changing a representation can be an exact semantics-preserving transformation. Replacing continuous evolution by a numerical integrator is usually an approximation. Replacing real arithmetic by floating point is another approximation. A proof architecture should not blur those three operations.

Likewise, a nilpotent \(\varepsilon\) with \(\varepsilon^2=0\) is not a finite timestep \(h\). Infinitesimal calculations can simplify differentiation, but they do not turn a finite-step truncation into an exact evolution.

## 7. What can actually be formalized with available tools?

### Ordinary Lean: a sensible route for explicit presentations

For an implementation-oriented project, I would first consider ordinary Lean with explicit group actions and groupoids, rather than trying to make native Lean equality carry orbifold isotropy.

Lean uses definitional proof irrelevance. Consequently, distinct isotropy arrows cannot simply be distinct proofs of an ordinary Lean equality proposition; they should be represented explicitly as mathematical data, or inside a modeled theory. [Lean Language](https://lean-lang.org/faq/)

Useful existing mathematical ingredients include mathlib’s manifold/tangent-bundle infrastructure, local ODE existence results, and Clifford algebras. These are components from which to build, rather than evidence that the entire proposed simulation stack is already packaged. [leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorBundle/Tangent.html)

### There is now a Lean SDG formalization

A relevant recent development is Brasca and Clemente’s March 2026 paper, **“Synthetic Differential Geometry in Lean.”** It formalizes synthetic differential calculus, including multivariable Taylor theorems on infinitesimal neighborhoods. The development carefully avoids classical choice dependencies and uses custom versions of Lean, mathlib, and Batteries. [arXiv](https://arxiv.org/html/2603.17457v2)

So it would be incorrect to say that Lean has no SDG work. But this is not Myers’ full differential cohesive higher-type framework, nor an orbifold simulator. It also does not justify adding nontrivial nilpotent infinitesimals to ordinary classical `ℝ`: the synthetic scalar object and its logical setting are essential. [arXiv](https://arxiv.org/html/2603.17457v2)

### Agda and Cubical Agda: attractive for the intrinsic side

Cubical Agda provides computational path types, univalence machinery, and higher inductive types. Those are relevant to retaining quotient identifications, although they do not automatically supply differential cohesion or smooth infinitesimals. [agda.readthedocs.io](https://agda.readthedocs.io/en/latest/language/cubical.html)

There is also a concrete precedent for formalized modal geometry: Felix Wellen’s *Formalizing Cartan Geometry in Modal Homotopy Type Theory* reports Agda checking of its main results. This is distinct from the Felix library, despite the shared name. [KITopen](https://publikationen.bibliothek.kit.edu/1000073164/4287789)

### Verified numerics can be pursued independently

For the numerical layer, Isabelle/HOL’s **HOL-ODE-Numerics** is particularly relevant: its development includes rigorous numerical solution enclosures using Runge–Kutta methods and affine arithmetic. It is not an orbifold engine, but it demonstrates a practical alternative to building the entire numerical-verification foundation yourself. [ISA Archive](https://isa-afp.org/entries/Ordinary_Differential_Equations.html)

Choosing such a numerical layer would not require abandoning an intrinsic specification. The connection between proof systems, however, would need an explicit trust and translation story; it is not automatically supplied by either library.

## 8. What I would build first

I would start with
\[
Q=\mathbb R^3//C_4,
\qquad
r(x,y,z)=(-y,x,z).
\]

This is a useful test case because it has genuine orbifold isotropy along an axis, yet its group action is just a signed permutation of coordinates. Group bookkeeping needs no trigonometric approximation.

The initial model would use lifted position and velocity, first for free motion and then for an invariant oscillator or another simple invariant mechanical system. I would establish exact-real equivariance of the step before addressing floating-point error. Then I would give a matrix-based implementation and a geometric-algebra implementation the same denotation.

The decisive tests would involve crossing a displayed seam, passing through the singular axis, transporting an attached frame, and showing that equivalent representatives produce equivalent results. After that, I would move to a genuinely curved or multi-chart example—possibly a teardrop—to expose assumptions hidden by the simple global cover.

**My overall recommendation is to aim first for a verified library of equivariant geometric mechanics with interchangeable representations.** Use the microlinear-type perspective to guide the intrinsic semantics; use explicit presentations to execute; and let Clifford algebra be an optional algebraic backend.

That would preserve the central benefit of the paper—geometry that does not depend on its presentation—without requiring every foundational theorem to be formalized before the first object moves.
````

Prompt 2:
````md
I've read that the game "Hyperbolica" uses gyrovector spaces to model its hyperbolic geometry. It makes me wonder whether we are missing some generalization of one of these suggested presentations that is actually far more appropriate for modeling the internals of orbifolds. If none are known, speculate what one could look like and investigate a bit.
````

Response 2:
````md
**Yes. I think your Hyperbolica example points to a substantial missing layer in my previous answer.** I emphasized representations of the *space*—atlases, groupoids, frame bundles—but not enough the algebra of *finite displacements within that space*.

There are established generalizations of gyrovector geometry that are relevant: **geodesic loops, Cartan geometry, and the post-Lie algebraic approach to geometric numerical integration**. They connect rather well. In particular, some recent work explicitly enlarges ordinary vector fields by infinitesimal holonomy transformations so that curved-space dynamics acquires an algebra suitable for numerical integration. [Shimane Math Dept.](https://www.math.shimane-u.ac.jp/memoir/32/kikkawa2.pdf)

My resulting proposal is:

> For orbifold simulation, investigate a calculus of **based displacements with transported frames and explicit symmetry identifications**, rather than trying to put one generalized addition directly on orbifold points.

Below I separate the established mathematics from the construction I would investigate. I also implemented a small numerical experiment to test the simplest version.

## 1. What Hyperbolica’s gyrovectors are buying

There is an important detail in the developer’s description: his “gyrovector” represents an object’s hyperbolic transformation using **a vector and a quaternion**. He contrasts this with a Minkowski-coordinate, matrix-based representation, and explains the preference partly in terms of editing and animation. Thus, the implementation is retaining orientation as well as displacement—not merely replacing Euclidean vector addition with a nonassociative operation. [Game Developer](https://www.gamedeveloper.com/design/q-a-the-mind-bending-geometry-of-non-euclidean-experiment-hyperbolica-)

Here is the mathematical significance.

Write \(a\oplus b\) for hyperbolic gyroaddition, and let
\[
T_a(x)=a\oplus x
\]
be the associated translation-like isometry. Its composition law has the form
\[
T_aT_b=T_{a\oplus b}\,\operatorname{gyr}[a,b].
\]
The *gyration* is a rotation fixing the chosen origin. Composing two translation-like motions produces both a displacement and an orientation correction. This is the geometric content behind the gyroassociative law. [arXiv](https://arxiv.org/html/1303.4785v1)

Now represent a full transformation by a pair \((a,R)\), meaning \(T_aR\). Using rotation-equivariance of gyroaddition, its composition is
\[
\boxed{
(a,R)\star(b,S)
=
\left(
a\oplus Rb,\;
\operatorname{gyr}[a,Rb]\,RS
\right).
}
\]

This formula follows simply by factoring
\[
T_aRT_bS=T_aT_{Rb}RS.
\]

**The full composition is associative**, because it is composition of isometries. Nonassociativity appears when you keep the displacement but discard the correction rotation.

That suggests a useful interpretation of Hyperbolica:

> Its representation is not an alternative to Lie-group geometry. It is a convenient factorization of that geometry into translation-like and rotation-like parts.

The broader mathematical pattern is a homogeneous space \(G/K\). Choose representatives \(s(a)\in G\) of points \(a\in G/K\). Then the failure of representatives to multiply like points is recorded by
\[
k(a,b)=s(a\oplus b)^{-1}s(a)s(b)\in K.
\]
Under suitable symmetry assumptions this becomes the familiar gyrostructure. Related constructions recover an associative transformation group from a nonassociative point multiplication and its correction transformations. Arbitrary homogeneous spaces, however, do not automatically satisfy all gyrogroup axioms or admit a convenient global choice of representatives. [Shimane Math Dept.](https://www.math.shimane-u.ac.jp/memoir/32/kikkawa2.pdf)

So the opportunity is real: find factorizations and correction laws that expose the geometry more conveniently than raw coordinates. But the correction data are essential.

## 2. Why a universal “orbifold gyrovector space” cannot quite be the answer

There is a simple obstruction that helps narrow the search.

Suppose an orbifold had a global gyrovector-like arithmetic whose left translations were orbifold equivalences, and could move the origin to any point. An equivalence preserves a point’s automorphism group:
\[
\operatorname{Aut}(L_a x)\cong\operatorname{Aut}(x).
\]
Consequently, every point reachable this way would have isomorphic isotropy.

**An orbifold with both regular points and genuine singular points cannot have such a transitive arithmetic preserving its orbifold structure.** This is a direct deduction from what an equivalence preserves.

It does not prevent a particle from crossing a singularity. It prevents treating every particle displacement as a global symmetry of *position space*.

There is also a concrete failure of the most obvious quotient construction. Consider the hyperbolic disk modulo the half-turn:
\[
Q=\mathbb D//C_2,\qquad z\sim -z.
\]
For real disk coordinates, Möbius addition is
\[
a\oplus b=\frac{a+b}{1+ab}.
\]
Since \([a]=[-a]\), an addition defined by adding arbitrary representatives would require \([a\oplus a]=[a\oplus(-a)]\). But with \(a=1/5\),
\[
a\oplus a=\frac5{13},
\qquad
a\oplus(-a)=0,
\]
and these are different orbits.

The lesson is not that gyroaddition is deficient. The same problem occurs with ordinary addition on many Euclidean quotients. **Simultaneous equivariance of two arguments does not make an operation independent of choosing representatives for each argument separately.**

A second distinction is equally important:

- **Curvature corrections** describe how transport and displacement interact.
- **Orbifold isotropy** describes identifications of local representatives.

For example, \(\mathbb R^2//C_2\) and \(\mathbb R^2//C_3\) have the same zero curvature in their smooth covering charts, but different isotropy at the origin. No algebra computed solely from that local curvature can distinguish them.

Thus, a generalized gyrostructure needs *both* differential-geometric information and discrete symmetry information. Neither can generally replace the other.

## 3. Established generalizations worth investigating

### Geodesic loops: addition made from a connection

There is a very direct generalization of “add a displacement”: use the exponential map and parallel transport.

Fix a base point \(o\) on a manifold with a connection. In a sufficiently small normal neighborhood, define
\[
x\circ_o y
=
\exp_x\!\left(P_{o\to x}\log_o y\right).
\]
Here \(P_{o\to x}\) transports along the selected radial geodesic. Operationally: interpret \(y\) as a displacement from \(o\), carry that displacement to \(x\), and execute it there. This is the construction underlying **geodesic local loops**, associated with Kikkawa’s work. “Loop” here means a nonassociative algebraic structure with an identity, not a closed trajectory. [Shimane Math Dept.](https://www.math.shimane-u.ac.jp/memoir/32/kikkawa2.pdf)

Equivalently, work entirely with tangent vectors at \(o\):
\[
u\boxplus_o v
=
\log_o\!\left(
\exp_{\exp_o u}
\left(P_{o\to\exp_o u}v\right)
\right).
\]
This is a version of the **double exponential**: perform two successive, geometrically interpreted displacements, then express their result back at the original base point. Its expansion is studied as a geometric analogue of the Baker–Campbell–Hausdorff formula. [arXiv](https://arxiv.org/html/2205.04381v1)

This is close to the generalization you are asking for. In flat Euclidean geometry it reduces to ordinary addition. In more general geometry it is local, depends on the base point and connection, and need not satisfy all gyrogroup identities.

The failures of commutativity and associativity encode torsion and curvature. More general infinitesimal theories—Akivis and Sabinin algebras—organize such nonassociative operations and their higher-order data. The completely general situation is not necessarily captured by a single binary product or a short finite multiplication table. [arXiv](https://arxiv.org/html/0803.1241v1)

**My assessment:** this is the right conceptual generalization of gyroaddition itself. It is not yet, by itself, an orbifold representation.

### Genuine gyrostructures already extend beyond hyperbolic space

A useful example is the space of symmetric positive-definite matrices. For its affine-invariant geometry, one gyroaddition and scalar multiplication are
\[
A\oplus B=A^{1/2}BA^{1/2},
\qquad
t\otimes A=A^t.
\]
The correction transformations come from orthogonal factors. Nguyen’s *The Gyro-Structure of Some Matrix Manifolds* develops this explicitly and proves gyrovector-space properties for the relevant positive-definite-matrix constructions. [NeurIPS Proceedings](https://proceedings.neurips.cc/paper_files/paper/2022/file/a9ad92a81748a31ef6f2ef68d775da46-Paper-Conference.pdf)

This matters because it shows that the useful abstraction is not confined to “Euclidean space with a curvature parameter changed.” Structured matrix spaces can have useful gyro-arithmetic too.

For simulation, I would consider these constructions not only for ambient space but also for configuration variables—such as positive-definite shape or deformation data. The appropriate algebra could differ between the position, orientation, and internal-state parts of one object.

### Post-Lie algebras: a particularly relevant bridge to numerical integration

The most directly relevant paper I found is Grong, Munthe-Kaas, and Stava’s **“Post-Lie algebra structure of manifolds with constant curvature and torsion.”** Despite the title’s wording, the precise hypotheses are **parallel curvature and torsion**:
\[
\nabla R=0,\qquad \nabla T=0.
\]
Their construction enlarges vector fields by endomorphisms representing infinitesimal holonomy transformations:
\[
\mathfrak X(M)\oplus\Gamma(\mathfrak{hol}).
\]
They obtain a post-Lie algebra and develop applications to numerical solutions of differential equations, using a frame-bundle construction. [arXiv](https://arxiv.org/html/2305.02688v2)

This seems especially suggestive in light of Hyperbolica:

> When displacements alone do not close under the desired algebra, retain the frame transformations generated by curvature.

There is also a broader algebraic treatment for general connections in Al-Kaabi, Ebrahimi-Fard, Manchon, and Munthe-Kaas’s **“Algebraic aspects of connections…”**, connecting enlarged post-Lie structures, torsion, curvature, and the double exponential. It is important not to simplify this into the false statement that covariant differentiation on ordinary vector fields is always a post-Lie algebra. The enlargement matters. [arXiv](https://arxiv.org/html/2205.04381v1)

**My assessment:** for a verified simulator, this line is potentially more immediately useful than adopting the whole synthetic differential cohesive foundation. It already addresses the algebra behind geometric integration. Extending the appropriate constructions equivariantly across orbifold charts, and proving descent, would be additional work—not a theorem I can attribute to those papers as written.

## 4. A concrete orbifold generalization: framed displacement geometry

Here is the construction I would investigate, first in a particularly clean case and then generally.

### Hyperbolic orbifolds: the frame space gives a simple answer

Assume an oriented hyperbolic orbifold has the presentation
\[
Q=(G/K)//\Gamma,
\qquad
G=SO^+(n,1),\quad K=SO(n),
\]
with \(\Gamma\) a discrete subgroup.

Instead of representing position in \(G/K\), represent a framed pose in
\[
P=\Gamma\backslash G.
\]
Even when \(\Gamma\) has torsion and the position quotient has singularities, its left action on \(G\) is free. Thus \(P\) is a manifold. The orbifold is recovered by forgetting the frame:
\[
Q\simeq P//K.
\]
The right \(K\)-action can have finite stabilizers. This distinction between the smooth framed space and the orbifold position space is explicit, for example, in the hyperbolic surface construction using \(PSL(2,\mathbb R)\). [arXiv](https://arxiv.org/html/math/9911102v1)

Now a prescribed body-frame increment \(\xi\in\mathfrak g\) gives the update
\[
\boxed{
\Gamma g\longmapsto \Gamma\bigl(g\exp(h\xi)\bigr).
}
\]

Representative independence follows immediately:
\[
(\gamma g)\exp(h\xi)
=
\gamma\bigl(g\exp(h\xi)\bigr).
\]

This is a substantial simplification. Store a full isometry representative, execute local motion by right multiplication, and identify representatives by left multiplication.

There are two qualifications. First, \(\Gamma\backslash G\) is not generally itself a group: we are using a well-defined right action, not multiplying two arbitrary cosets. Second, state-dependent controls must also respect the representation equivalence.

For this model, gyrovector-plus-rotation coordinates and Lorentz matrices are two candidate implementations of the same framed transformations. That gives a natural target for representation-refinement proofs.

### General effective Riemannian orbifolds: replace fixed group multiplication with Cartan development

For a general effective Riemannian orbifold \(Q\), its orthonormal frame space
\[
P=\operatorname{Fr}(Q)
\]
is again a smooth manifold, with a locally free \(O(n)\)-action recovering the orbifold. This frame construction does not require the orbifold to have a global manifold orbifold cover. [math.colostate.edu](https://www.math.colostate.edu/~renzo/teaching/Orbifolds/Ruan.pdf)

The additional structure I omitted previously is what makes this frame presentation useful for *motion*.

The tautological form \(\theta\) measures displacement in the carried frame; the Levi-Civita connection form \(\omega\) measures rotation relative to parallel transport. Together they give
\[
A_p=(\theta_p,\omega_p):
T_pP\overset{\sim}{\longrightarrow}
\mathbb R^n\oplus\mathfrak{so}(n).
\]
This is the Riemannian instance of a Cartan connection. Cartan geometries on orbifolds, including their realization on parallelizable manifolds with locally free group actions, have been developed explicitly by Zhukova. [ResearchGate](https://www.researchgate.net/publication/228546605_Cartan_geometries_on_orbifolds)

Here is my proposed implementation interpretation:

\[
\boxed{
\dot p=A_p^{-1}(v,\Omega).
}
\]

The input \(v\) is a translation command in the object’s local frame; \(\Omega\) is a rotation command. Setting \(\Omega=0\) and keeping \(v\) constant produces a geodesic with a parallel-transported frame. A mechanical model would additionally evolve \(v\) and other state variables according to forces.

This looks like ordinary rigid-pose kinematics, except that the conversion from “local move/turn command” to a tangent vector depends on the current geometric state.

The curvature connection to gyrovectors becomes visible directly. Write \(H_u\) for the horizontal vector field corresponding to a fixed local displacement \(u\). For a torsion-free connection, the structure equations give schematically
\[
[H_u,H_v]_p
=
-\,V_{R_p(u,v)},
\]
where \(V\) denotes the vertical, frame-rotation direction.

In words: **the commutator of two local translations produces a rotation governed by curvature**. That is the infinitesimal counterpart of the correction retained by gyrovector composition.

In a homogeneous model, these relations can close into a fixed Lie-algebra description and yield closed-form motion formulas. In generic geometry, the curvature coefficients vary with \(p\), and repeated operations encounter their derivatives. The finite state remains manageable—in three dimensions the frame space has dimension six—but the geometry is supplied by varying fields rather than one universal multiplication table.

This is the generalized representation I find most promising:

> **Gyrovector-style commands, interpreted through a Cartan connection, on a framed presentation of the orbifold.**

For generic curvature, finite movement requires integration rather than a few closed-form arithmetic operations. That is a limitation of the available geometric structure, not something notation alone can eliminate.

Effectivity is essential to the claim that the frame space is a manifold. With ineffective isotropy, invisible symmetries must still be retained in a groupoid or equivalent additional structure. Likewise, a frame describes local pose, not automatically the placement of an extended rigid object in arbitrary curved geometry.

## 5. What I tested

I implemented a small, independent prototype for
\[
Q=\mathbb H^2//C_4,
\]
where \(C_4\) acts by quarter-turns about the disk origin. This is a hyperbolic cone orbifold.

A pose is a disk point \(a\) and a unit complex number \(u\) describing its frame. Its action is
\[
z\longmapsto a\oplus uz.
\]
The identification acts on both:
\[
(a,u)\sim(ia,iu).
\]

The program implements the framed composition law, compares it with independently computed projective-matrix composition, and follows a geodesic through the singular point while randomly changing representatives.

| Check | Observed result |
|---|---:|
| Framed associativity, 1,000 random samples | Maximum coordinate residual \(7.5\times10^{-16}\) |
| Agreement with matrix composition | Maximum residual \(4.6\times10^{-16}\) |
| Forty-step geodesic versus its exact position formula | Maximum error \(3.9\times10^{-16}\) |
| Deliberately changing position without changing frame | Disagreement about \(0.11\) |

Randomly changing the full pose representative introduced no additional discrepancy in this particular run. The intentionally incorrect position-only change did.

This checks the proposed algebra and catches an important implementation mistake. **It is not a formal proof, a performance benchmark, or a validation for arbitrary orbifolds.** The tests stay in a well-conditioned part of the disk, and the residuals are coordinate residuals, not certified intrinsic error bounds.

:chatgpt-content-reference{index="16"}[Python prototype: framed hyperbolic motions on a cone orbifold](sandbox:/mnt/data/orbifold_gyro_probe.py)

It uses only the Python standard library and runs with `python orbifold_gyro_probe.py`.

## 6. What I would develop—and what the proof interface should expose

I would use **“orbifold displacement calculus”** as a working name, not as a claim that an established package with precisely this design exists.

The essential change from an ordinary vector API is that a displacement has a **base point and a frame**. Its composition is not generally an untyped operation on two positions.

The specification should distinguish three things:

**Motion.** A local displacement or time-parametrized trajectory, with transported geometric data.

**Representation change.** An orbifold-chart identification or group action relating two descriptions of the same state.

**Frame change.** A change of local axes, with the corresponding transformation of coordinates and controls.

Conflating these is precisely how one loses the orientation correction, forgets isotropy, or treats an identification as if it were a physical journey.

A key exact compatibility law would be
\[
\phi(\exp_xv)
=
\exp_{\phi(x)}(D\phi_xv)
\]
for an isometric chart identification \(\phi\), together with the corresponding law for parallel transport. These follow because an isometry preserves the connection and its geodesics. They tell us how chart-local displacement operations can fit together, without trying to quotient their arguments independently.

For arbitrary curved trajectories, endpoints alone do not determine transport. The interface therefore needs either the path information relevant to transport or an explicitly accumulated transport operation—not just “start point, end point.”

I would give this interface several implementations:

| Geometric setting | Candidate implementation |
|---|---|
| Constant-curvature quotient | Gyrovector-plus-frame formulas or isometry matrices |
| Suitable symmetric or homogeneous space | Geodesic-loop operations and structure-preserving integrators |
| General effective Riemannian orbifold | Frame-space development with chart/groupoid bookkeeping |

This table is a proposed architecture, not a report of one existing library.

The Felix-like opportunity is to make all implementations denote the same geometric operations, and then separate two kinds of theorem. Changing from a gyro representation to a matrix representation can preserve an ideal discrete operation **exactly**. Replacing continuous development by a finite numerical step generally preserves it only **within an error bound**. Floating-point evaluation adds another approximation. A good algebraic interface makes those distinctions easier to state rather than hiding them.

There is also a concrete formalization lead: the Archive of Formal Proofs contains **“Formalization of Gyrovector Spaces as Models of Hyperbolic Geometry and Special Relativity”**, by Marić and Marković. It formalizes general gyrogroup/gyrovector notions and concrete two-dimensional Möbius and Einstein models, including connections with the Poincaré and Klein models. It is an Isabelle development, not a verified three-dimensional game engine or an orbifold library, but it is a much more substantial starting point than proving every gyro identity from scratch. [isa-afp.org](https://isa-afp.org/entries/GyrovectorSpaces.html)

## Where this leaves the synthetic paper

Myers’ framework remains attractive for the presentation-independent meaning of the orbifold and its differential structure. Its definition, however, does not itself choose a metric, a connection, or a finite-displacement algorithm. Those are the additional ingredients under discussion here. [arXiv](https://arxiv.org/html/2205.15887v1)

I would therefore revise my earlier recommendation to:

\[
\boxed{
\begin{array}{c}
\text{intrinsic orbifold semantics}\\[2pt]
\downarrow\\[2pt]
\text{connection-aware, framed displacement calculus}\\[2pt]
\downarrow\\[2pt]
\text{gyro / Lie-group / numerical-development implementations}
\end{array}
}
\]

The middle layer is the important addition.

I found substantial established mathematics supporting it, but not a turnkey system combining generalized displacement algebra, orbifold isotropy, executable mechanics, and refinement proofs. The numerical experiment supports the simplest framed-quotient case; extending and verifying the general case remains a proposed development.

**The direction I would prioritize is not “invent a vector space for every orbifold,” but “generalize the move-and-turn algebra that makes gyrovectors convenient, while retaining exactly the symmetry and transport data an orbifold requires.”** That seems both mathematically well motivated and plausibly more useful for simulation than an atlas API alone.
````
