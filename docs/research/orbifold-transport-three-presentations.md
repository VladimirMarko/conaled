# Orbifold motion through frames, stack transport and synthetic geometry

The quarter-turn cone admits a common transport calculation in explicit coordinates and in a bundle-with-connection presentation over its quotient stack. A higher synthetic formulation offers a different way to organize tangent and connection reasoning, but the supplied artifacts do not yet connect that formulation to the same finite physical paths and numerical observations. The useful next comparison is a designated transport map, including its closing symmetry and clock, rather than an equivalence of entire foundations.

This completes the mathematical investigation requested by [#310](https://github.com/VladimirMarko/conaled/issues/310). It recommends investigating stack transport as a possible mathematical interface, while retaining the current executable realization and the independently useful synthetic developments. It does not select a universal winner or make a common Lean formalization a prerequisite. Independent acceptance belongs to the enclosing review. The initial local source baseline is `d677a1d`; the source and artifact identities below make the comparison reproducible.

## The frozen problem

Let D be the open unit disk in C, with metric

```text
g_z(v,w) = 4 Re(conj(v) w) / (1 - |z|²)².
```

Let C4 = {1,i,-1,-i} act by multiplication. Work with the orbifold presented by the action groupoid, retaining arrows, not only the orbit space. An input consists of a starting point x, an oriented orthonormal frame u at x, a finite piecewise smooth physical path γ:[0,T]→D, and, when closing the path, a specified group element g satisfying g γ(T)=x. Zero durations and holds are allowed. A motion input may instead consist of finitely many timed body-velocity, turn and hold controls; this additionally requires development to produce γ and the moving frame.

The requested outputs are the endpoint and transported frame, the retained path and its elapsed time, and the closed transport endomorphism

```text
H(γ,g) = Dg ∘ Pγ : TxD → TxD.
```

The comparison must prove composition for matching paths, compatibility with connection-preserving changes of coordinates or presentation, and agreement of these designated outputs. It must retain these controls:

- At the origin there are four automorphisms. At a nonzero point only the identity stabilizes it. The origin arrow i acts on tangent vectors by multiplication by i.
- A nonconstant loop and a hold can have identical endpoints and different transport. A closing symmetry is additional data, not inferred from the endpoints or from transport.
- Holds of different duration can have identical endpoint and transport. A transport quotient alone cannot recover elapsed time.
- Ineffective isotropy may act identically on tangent vectors while remaining distinct in the base orbifold.

A frame is an element of a fiber or its coordinate realization, not a canonical global choice on the coarse quotient. At an orbit represented by another lift, compare frames by the specified derivative action. This avoids asking any route for a nonexistent representative-independent vector formula.

## Worked core: the same calculation in three presentations

### Explicit connection and labeled paths

Put a(z,v)=2 conj(z)v/(1-|z|²). Parallel vectors satisfy

```text
V'(t) = -a(γ(t),γ'(t)) V(t).
```

For the supplied smooth path on a compact time interval, the coefficient is continuous and the linear initial-value problem has a unique solution. Concatenating solutions with the common intermediate value proves `P(γ⋆δ)=Pδ ∘ Pγ`; reversing the path gives the inverse. Since `a(hz,hv)=a(z,v)` for h∈C4, multiplication by h takes a parallel solution to the solution over hγ with the transformed initial vector. Thus `Phγ ∘ Dh = Dh ∘ Pγ`. These are paper derivations for this problem, with corresponding bounded Lean results below.

For γ(t)=r exp(it), r²=1/5, the coefficient is i/2. Hence `Pγ(v)=exp(-iT/2)v`. At T=2π the loop returns to x and transports v to -v. A hold at x transports v to v. At the origin a hold followed by the closing arrow i has `H(v)=iv`; replacing that arrow by 1 changes H while preserving the physical path. These calculations separate curvature, physical motion and isotropy.

A connection-preserving diffeomorphism F gives

```text
DF_y ∘ Pγ = P(Fγ) ∘ DF_x.
```

The proof takes a solution through DF and uses preservation of the connection and uniqueness. The Christoffel transformation for a nonlinear F includes its second derivative; arbitrary coordinate substitution in the coefficient is insufficient. If the closing arrow is also transported, the closed endomorphisms are conjugate by DF_x. For a general presentation equivalence, local lifts and their compatible transition arrows replace one global F; those coherence data must be supplied.

The current [disk transport](../../Applications/Orbifold/DiskTransport.lean) constructs finite paths from segments carrying a nonzero scalar factor and its differential equation. `field_unique`, `Path.append_transport` and `transport_unique` prove the needed uniqueness/composition for those inputs. It is not a general solver for every smooth curve. [TransportSegments](../../Applications/Orbifold/TransportSegments.lean) constructs the circle and proves `loop_transport` and `path_dependence`. [TransportComparison](../../Applications/Orbifold/TransportComparison.lean) proves rotation and the explicit ellipse connection comparisons. [TransportFrames](../../Applications/Orbifold/TransportFrames.lean) retains the closing arrow in `ClosedLift` and defines exactly the composition order above.

### Bundle and stack transport

Use the oriented orthonormal frame bundle of D with its Levi-Civita connection. The C4 action lifts by derivatives and preserves that connection. Over the action groupoid, this is concrete descent data: the frame bundle over objects, a connection-preserving isomorphism over each arrow, its unit law and its composition law. The rotation calculation above supplies the differential compatibility; the group action supplies the cocycle. Thus the object is a principal SO(2)-bundle with connection over [D/C4]. This paragraph is a paper construction, not an existing Lean stack-connection instance.

Schreiber–Waldorf define transport with local trivializations over a surjective submersion and smooth descent data (Definitions 3.1 and 3.6). Their Theorem 5.4 identifies principal bundles with connection and the corresponding transport functors on a manifold. The path groupoid uses thin homotopy and sitting instants. These conditions exclude an arbitrary assignment of linear maps to paths. [Parallel Transport and Functors, §§2–3 and Theorem 5.4](https://arxiv.org/html/0705.0452v5).

Collier–Lerman–Wolbert use smoothness on thin loop groups in Definition 3.5. Their Theorem 4.1 is the manifold equivalence; Theorem 5.4 makes holonomy an equivalence of categories fibered in groupoids over manifolds. Theorem 6.4 induces the equivalence over a stack, and Theorem 6.7 expresses it through Lie-groupoid cocycles. Remark 3.6 describes equivalence with Schreiber–Waldorf's definition as a belief, not a proved identification of those definitions. Use either theorem with its own hypotheses. [Parallel Transport on Principal Bundles over Stacks](https://arxiv.org/html/1509.05000v1).

Applied to the constructed cocycle, the stack route sends a lifted path to Pγ and a closing action arrow to Dg. Functoriality then gives their composite H and path concatenation. A connection-preserving change of presentation pulls back the same bundle and its descent isomorphisms; naturality compares the designated fiber maps. This absorbs recurring chart-transition calculations once the cocycle comparison is proved. It does not choose a connection, produce a path from controls, or imply that any two presentations with the same coarse space are equivalent.

The existing finite Lean paths are piecewise segments with physical durations. A formal bridge must compare them with smooth sitting-instant representatives, prove reparametrization invariance of parallel transport, and retain the original clock separately. Keeping only a thin class loses timing. Keeping only H loses even more: different paths and closing labels can have the same endomorphism. This intentional quotient is useful for transport, but cannot become the sole execution record.

### Higher synthetic tangent and connection reasoning

Myers defines tangent fibers by pointed infinitesimal maps (Definition 4.1.8), obtains the isotropy action through dependency (Remark 4.1.10), and proves coherent tangent-module structure from microlinearity (Theorem 4.2.19). The proper-étale comparison is Theorem 6.3.7 in the ambient differential cohesive theory. These results do not construct finite-path parallel transport or a chosen metric. [Myers, arXiv:2205.15887v1](https://arxiv.org/html/2205.15887v1).

Kock formulates affine and bundle connections using neighboring points (§§2.3–2.5) and groupoid connections/curvature in Chapter 5. Section 5.8 explicitly assumes unique path integration; its subdivision equation (5.8.3) yields composition, and Proposition 5.8.6 yields a path connection. The differentiation recovery in Theorem 5.8.9 additionally uses weak flatness on infinitesimal line images. A complete endpoint-only integral requires flatness; that is unsuitable for our curved loop. [Synthetic Geometry of Manifolds, §§5.2–5.8, especially pp.196–201](https://users-math.au.dk/~kock/SGM-final.pdf).

Here is the conditional argument for the frozen core. Supply a higher smooth setting with the disk/C4 quotient, its tangent family, the metric and connection matching the coefficient a, and unique integration along the admitted physical paths. On infinitesimal intervals solve the parallel equation using that connection. Integration gives Pγ; uniqueness gives concatenation and naturality. The selected identity arrow g acts on the terminal tangent fiber, so composing it with Pγ gives H. Evaluation on the displayed circle recovers exp(-iT/2), provided the interpretation preserves the line, exponential and integration used in this calculation. Identity elimination handles isotropy action; it does not replace the connection-dependent integration step.

The economy is real at the level of the conditional argument: tangent action and change of fibers are expressed through dependency, and connection laws use infinitesimal diagrams. The unmet obligation is a joint interpretation validating these particular higher, smooth, infinitesimal and integration principles, with the designated comparison maps. Neither set-valued SDG connections nor a Cubical checker supplies that interpretation automatically. This route remains eligible to replace the geometry-author interface if that work succeeds; fitting the current implementation first is not a requirement.

## Developing controls and intrinsic rolling

Transport accepts a supplied path. Development instead solves for a path and frame from body controls. With solder form θ and connection form ω on the oriented frame bundle, use `θ(u̇)=v(t)` and `ω(u̇)=Ω(t)`, with initial frame u₀. For Ω=0 this is horizontal Cartan development; a turn is vertical frame motion, so its final frame is not generally obtained by parallel transport of u₀ along its stationary base path. The finite command semantics must record which operation is intended.

Intrinsic rolling provides another formulation: configurations carry two points and a tangent isometry; no-slip relates velocities, and no-spin preserves parallel fields. Chitour–Kokkonen study smooth connected oriented complete Riemannian manifolds of equal dimension at least two, with a space-form target for their main control analysis. Their global controllability conclusions are not a theorem about arbitrary orbifolds. [Rolling manifolds on space forms, §§2–3](https://www.numdam.org/article/AIHPC_2012__29_6_927_0.pdf).

For the common disk core, ordinary smooth ODE theory supplies local unique development; the admitted closed-form move/turn/hold commands have their existing global finite-duration constructions. For another metric or arbitrary controls, state the maximal existence interval or a completeness/nonexplosion argument. Stack descent transports solutions when local developments agree on overlaps, but does not prove existence by itself.

Bunge–Sawyer's connection-map comparison uses Euclidean module bundles with infinitesimally linear total and base objects; its converse needs short path lifting (§1, Propositions 1–2). Passing from a Lawvere spray to a torsion-free connection requires local existence of exponential maps (§4, Proposition 4); the Joyal version uses the infinitesimal condition (Proposition 6), with local implying infinitesimal in Proposition 7. These are explicit assumptions, not universal flow existence. [On connections, geodesics and sprays in synthetic differential geometry](https://www.numdam.org/article/CTGDC_1984__25_3_221_0.pdf).

A synthetic development theorem therefore needs more than a microlinear tangent object. It must supply the relevant bundle linearity, lifting and integration/exponential hypotheses in its actual higher context. The available source arguments identify candidate obligations; no general higher extension is assumed here.

## Discriminating extensions

**Ineffective isotropy.** Replace C4 by C4×C2 acting through its first factor. There are eight origin automorphisms and a C2 stabilizer at each nonzero point; elements differing only in C2 have the same derivative. This is a paper extension of the core. Explicit labeled groupoids and quotient stacks retain these arrows, as can an untruncated higher quotient. A tangent representation is allowed to be nonfaithful. However, replacing the orbifold by the coarse quotient of its frame space erases this kernel. The effective free-frame presentation argument cannot be reused without checking effectiveness. A stack-valued frame construction can retain the kernel; it must not be confused with that coarse manifold replacement. Existing [ordinary isotropy cases](../../Examples/SmoothOrdinaryIsotropy.lean) check distinct ineffective arrows, without proving this entire new transport extension.

**Variable curvature.** The existing `ConnectionAssessment.variable_vertical` checks a coefficient for conformal exponent f=x². That metric is not C4-invariant: a quarter turn changes x² to y². It is a useful manifold test, but cannot be silently descended to the same cone. For a common cone extension choose instead f=x²+y² and metric exp(2f)(dx²+dy²). The following is an independent paper calculation: its connection has `Γ(u,v)=df(u)v+df(v)u-〈u,v〉grad f`. The oriented orthonormal coframe has rotation connection with exterior derivative corresponding to Gaussian curvature `K=-exp(-2f)(f_xx+f_yy)=-4 exp(-2r²)`. Thus curvature varies, while both f and the metric are C4-invariant. This is not a new Lean curvature theorem.

Explicit coordinates now need new solution or existence arguments. Stack transport still applies after constructing the invariant connection cocycle; it does not retain the hyperbolic closed formulas. The synthetic route can express the same infinitesimal curvature calculation conditionally, but still owes its model and path integration. All routes lose the right to reuse the existing hyperbolic numerical error constants. Variable curvature is not a refutation of any route; it exposes which proof was specific to the original connection.

## Available formalizations and their trust boundaries

The production Lean comparison uses Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` from `lake-manifest.json`. Existing acceptance uses the exhaustive repository audit, allowing `propext`, `Quot.sound` and `Classical.choice`. This report performs source inspection, not another Lean build or declaration-level axiom replay. Ordinary differentiable geometry and synthetic conditional derivations remain different statements.

| Artifact | Exact checking/provenance | Matched contribution and missing result |
|---|---|---|
| Production #44 motion and #99 smooth quotient/tangent work | Integrated Lean source and existing acceptance; [motion reassessment](orbifold-motion-reassessment.md) and the declarations named above | Connection, selected segment transport, frame/time observations and quotient action comparisons. No arbitrary-curve solver or full source-theory interpretation. |
| #363/#367/#368 | [Ordinary quotient comparison](ordinary-open-quotient-comparison.md), [explicit-data audit](myers-checkpoint-083-assessment.md), [proper-étale presentation](disk-proper-etale-presentation.md) | Actual smooth action groupoid, ordinary chart-arrow identification, four origin arrows, regular/ineffective controls. These are symmetry/descent results, not physical trajectories. |
| Myers 080 | Archive SHA-256 `4a2e2178578a9cfcae3877bbe4157cb69ea622fc7b07ff10a273b2276eecf264`; [local replay receipts](../history/orbifold/agda-checkpoints/checkpoint-080/README.md) | Conaled freshly checked 54 ordinary modules with Agda 2.8.0.2, safe/without-K/no external libraries. The separate 539-module Cubical closure has a supplied source-matched warm receipt, not that fresh replay. Reduced atlas results and ordinary constructions do not establish the full original smooth model. |
| Myers 083 | Archive SHA-256 `20a422c90784754a805be00cbeba185c8aab70d7b5a2628f58bcbdb69eb5f863`; [inventory](../history/orbifold/agda-checkpoints/checkpoint-083/README.md) | 63 ordinary modules have the external fresh receipt; 539 Cubical modules retain the source-matched receipt. Conaled checked payload identity, not a fresh 083 compilation. Sheaf adjunction/obstruction constructions strengthen model investigation, not finite-path transport. |
| Kock checkpoint | SHA-256 `7f615fa495853f64cf19ba53259ea01bc429ef631b2f119eef99eb1fca33bd69`; [inventory and pins](../history/orbifold/agda-checkpoints/README.md) | Supplied Agda 2.8.0.2 safe/without-K receipt covers 146 modules with no external library. No conaled replay. Tangent module/calculus proofs provide prerequisites; no matched quarter-turn finite-transport theorem was identified. Its source book is *Synthetic Differential Geometry*, second edition, not the 2009 *Synthetic Geometry of Manifolds* cited above. |

Checkpoint 22 remains a historical artifact, not the latest comparison input. Both later Myers Cubical closures use Cubical v0.9, commit `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`, with `--safe --cubical --guardedness --no-import-sorts --cohesion`. Native crisp support does not discharge additional crisp rules supplied as parameters.

The selected dependency inspection follows `FullProperEtaleOrbifolds` through `ProperEtaleManifoldOrbifolds` and `FullInfinitesimalMicrolinearity`. Its theorem takes a crisp ring/Kock field, crisp identity and flat rules, order/constancy and manifold data, real-flat, crisp excluded middle, tinyness, flat/truncation distribution at the required levels, crystalline pullback preservation, covering/interval/positive-line hypotheses, DP properness and crystalline étaleness. The proof derives the conclusion from these inputs; it does not construct their joint model. `DerivedAtlasOrbifold` instead uses bounded truncation, function extensionality, selected test squares, an effective atlas and lifting premises. Its reduced conclusion cannot substitute for the original theorem.

For Kock, `SDG.Axiom.KockLawvere` is an assumption interface. `Section07Linear` derives module operations with ring setness and function-extensionality premises; its imports include the earlier infinitesimal linearity and jet constructions. `Section15` additionally uses integration data; `Section16`'s finite-free construction has its own axiom/comparison premises. Neither proves that the joint higher orbifold context satisfies them. Their absence of a top-level `postulate` is compatible with substantial module parameters.

For reproducibility, the external handoff records syntactic transitive project-import closures of these selected roots: 121 modules for `FullProperEtaleOrbifolds`, seven for `DerivedAtlasOrbifold`, and 16/34/18 for Kock Sections 07Linear/15/16. These are import reachability counts, not counts of theorem dependencies or completed geometry. External Cubical/builtin imports remain named separately. A lexical scan found no project `postulate`, `TERMINATING` or `NON_TERMINATING` declarations in the extracted sources. It is not a substitute for the compiler receipts, a Cubical-library trust audit, or an audit of every inherited premise. No new Lean or Agda check was run for #310.

The [standalone Lean archive](../history/orbifold/standalone-formalization/README.md) is likewise reference evidence, not an integrated higher smooth model. Its [paper assessment](orbifold-paper-foundations-assessment.md) records the reversed association condition in printed Myers Proposition 6.1.7. This report uses neither that printed condition nor a native compactness formula to infer geometric properness. The 083 conditional RealFlat obstruction retains its site and witness hypotheses; it is not a refutation of every smooth higher interpretation.

## Correspondence to executable observations

| Required link | Present evidence | Remaining obligation |
|---|---|---|
| Isotropy and derivative action | Existing smooth quotient/chart comparisons and ordinary isotropy cases | Identify the same arrows and orientation convention in a stack/synthetic interpretation. Existing chart labels use an inverse convention relative to forward action arrows. |
| Connection and finite-path transport | Existing segment equations, uniqueness, rotation/ellipse squares; paper stack construction above | Construct connection descent as actual data, compare sitting-instant transport with the selected finite paths, and prove equality of designated maps. Mere bundle existence is insufficient. |
| Control development to endpoint/frame | [TimedCommands](../../Applications/Orbifold/TimedCommands.lean) proves command equations, execution/append, move transport and elapsed laws | A new semantics must preserve solder/connection/control meaning and distinguish parallel motion from explicit turns. For general controls supply an existence domain. |
| Closing symmetry | `ClosedLift.endomorphism` retains and applies its labeled arrow | Prove interpretation preserves the label/action and composition order, including ineffective controls. A quotient of H alone cannot recover the arrow. |
| Elapsed time and path record | `develop_duration`, `elapsed_append`, timed trace and hold cases | Retain the original time parameter beside any thin quotient. Prove clock preservation; do not attempt to derive it from holonomy. |
| Finite-run coordinates and error | [NumericalExecution](../../Applications/Orbifold/NumericalExecution.lean): `run_correct`, `run_error`, `run_clock`, under successful checked execution and initial approximation | Connect new position/frame observations to this exact pose decoding and approximation relation. Coordinate change requires a transferred bound; new metric/integrator needs new estimates. No intrinsic-distance or rounded-machine guarantee is inherited. |
| Execution resource observations | [Measured execution](measured-frp-numerical-execution.md) counts actual attempts while retaining failure work | These are separate operation observations; they neither validate geometric integration nor measure physical elapsed time or storage. |

The hypothetical full comparison has three stages: interpret the chosen higher/synthetic source rules in a joint model; identify its disk quotient, tangent connection and selected integration with the stack/explicit construction; then compose with the existing numerical observation theorem. Each stage names actual maps and preservation equations. Successful independent checking of both endpoints supplies none of these stages automatically. The stack route can pursue the middle stage directly without waiting for a full source-language interpretation.

## Author obligations, decisions and owned follow-ups

| Work | Explicit route | Stack route | Higher synthetic route |
|---|---|---|---|
| Model/setup | Smooth charts, groupoid action and tangent representation | Bundle/connection descent and smooth transport correspondence | Higher smooth model, infinitesimal/context principles and integration interpretation |
| New connection | Coordinate equations, compatibility and solution domain | Connection on the bundle plus descent compatibility | Infinitesimal connection/metric laws plus applicable integration hypotheses |
| Repeated composition/change of chart | Reuse uniqueness and action squares; supply concrete comparison | Reuse transport functoriality/naturality once the cocycle map exists | Reuse dependent transport and connection laws, conditional on validated principles |
| Numerical realization | Existing exact/rational coordinate contracts | Separate coordinate realization and error bridge | Separate realization and error bridge |

This is a comparison of matched obligations, not source line counts or a controlled author trial. Library maturity, authors, foundations and existing automation differ. Model-building effort must not be charged only to an alternative, while the incumbent's chart and solver construction is treated as free. Conversely, a shorter paper proof under unconstructed axioms does not establish lower total implementation cost. The synthetic route may reduce recurring geometry bookkeeping even if its initial model cost is higher.

The completed [#292 coherence comparison](dependent-coherence-comparison.md), integrated at `d108142f9b5875437c49441a4b45b3ad4988e5e5`, supports a separate judgment-interpretation boundary. Its Type-family construction and rejection cases neither repair #107 nor refute LF/full comprehension for the concrete groupoid interpretation. Subsequent [higher selected comparison](higher-shared-meaning-client.md) and [cubical model work](cubical-model-construction.md) supply bounded additional evidence, not a joint smooth interpretation. Coordinate that boundary through #289/#315/#316 and the #314–#319 programme. Mathematical geometry authors need not learn an embedded calculus or wait for a new frontend before this comparison is useful.

| Decision | Scope and next evidence | Existing owner |
|---|---|---|
| Adopt | Preserve explicit timed paths, closing labels, native motion APIs and numerical contracts as independently usable observations | #32/#34/#49 |
| Investigate as a possible replacement interface | Construct the disk frame-bundle connection cocycle and compare its stack transport with `ClosedLift`, including the circle, hold and origin-label controls | #34/#100, coordinated #32/#36 |
| Investigate independently | Validate the selected higher infinitesimal/connection and finite-integration fragment, or exhibit the exact failed joint hypothesis; reuse the supplied Agda proofs where a sound interpretation supports them | #36/#100/#289; external artifact owner retains its model investigation |
| Defer broader formal bridge | Arbitrary presentation/Morita transport and general controls require their actual smooth descent, integration and domain proofs | #100/#102/#103 |
| Defer author experiment until its interface exists | Freeze one repeated connection/presentation extension, count setup separately, retain native author route and failed submissions | #235/#289 |
| Reject these shortcuts | Coarse quotient as full isotropy semantics; endpoint-only curved transport; thin transport as clock; checker success as model construction; automatic Agda-to-Lean transfer | Boundaries of this comparison |

These are scoped follow-up obligations, not newly implemented capabilities or authorization for a wholesale migration. #311–#313 retain their separate mechanics, loopoid and realization comparisons. #49 remains independently actionable. #107 stays paused, #108's independent test remains unselected, and #260 stays inactive.

## Source receipts and validation

The primary PDF identities read for this report are retained here so mutable URLs can be checked against the research handoff:

| Source | SHA-256 |
|---|---|
| Collier–Lerman–Wolbert, arXiv 1509.05000v1 | `bccc9c1ba9a2bd97c528a29bcd8b439a491c4e29783b49bf9328b938bcf66b87` |
| Schreiber–Waldorf, arXiv 0705.0452v5 | `985c1325a9b9e3023211af9ef83d6fce06c32d21abe28651b8bb6b79eea7ed90` |
| Myers, arXiv 2205.15887v1 | `7c4709e39e292cd473f9b7543ff27e077a2ec8e0274bab6907cb9930ea4f2266` |
| Kock, SGM beta version August 7, 2009 | `c7f61d15324f0a67a8c5100bd13bc22c2eda8fd8b5c0a2a30b72847c236d0dc9` |
| Bunge–Sawyer, 1984 | `d6c16f2f62128caae94247993bc8b19bfa98d6c09fbeb4199c12c6ba594381f3` |
| Chitour–Kokkonen, 2012 | `0fe373c094615ef67d5a68df2ee2c9699b5286c32efd1af11c6ad5f07807c0ed` |

The external `evidence310` handoff contains downloaded sources, URL/hash receipts, selected archive members and import-edge inventories. Documentation validation checks relative links, cited local declarations, whitespace and the scoped diff. There is no new formalization requiring a Lean/Agda build. Independent Standards and Spec review assesses this report's hypotheses, comparisons and evidence limits.
