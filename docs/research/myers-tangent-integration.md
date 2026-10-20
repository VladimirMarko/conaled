# Finite quotient tangents and the smooth higher-model boundary (#96)

Decision at `23e20af19cba0eaab2883189135335d04401f334`, inspected 2026-10-20:
make **infinitesimal lifting for the finite-action quotient on the existing
smooth site** the next discriminating construction. Start with the cyclic
quarter-turn action, and construct its quotient using torsors and descent.
The test must retain automorphisms and identify their action on first-order
arcs. General transverse-pullback preservation (#97) is not the prerequisite
selected here. This is a recommendation, not authorization to implement a
successor. [#36](https://github.com/VladimirMarko/conaled/issues/36) remains open.

This decision follows the accepted full-faithfulness work in #95. The
[earlier Myers assessment](myers-orbifold-assessment.md) selected external
action-groupoid mathematics, now substantially implemented. The
[internal-language assessment](internal-languages-lean.md) records language
and semantic components; the [KL record](algebraic-kl-model.md) now includes
all-stage manifold reconstruction. Their older missing-capability lists must
be read at their dated baselines. None of these developments constructs the
higher/differential compatibility below.

The subsequent [reuse and outsourcing assessment](higher-theory-reuse-and-outsourcing.md)
identifies existing Agda torsor and differential-HoTT proof blocks. It recommends
developing the source interpretation alongside the torsor checkpoint, with
coherent delegated packages rather than a solely serial prerequisite sequence.
It supplements the reuse search below without claiming those libraries already
provide the constructed smooth interpretation.

## Selected result and classical target

Use Myers, *Orbifolds as Microlinear Types in Synthetic Differential Cohesive
Homotopy Type Theory*, [arXiv:2205.15887v1][myers], submitted 2022-05-31.
All numbering here is v1. The retrieved HTML has a later rendered title date;
it is not evidence of a second arXiv revision. The inspected source and hashes
are retained with the issue's review evidence outside the source diff.

The exact theorem is [Proposition 4.3.5][tangent]: for an infinitesimally
étale map `f : X → Y`, a crisp infinitesimal variety `V`, and `x : X`, the
induced map `T_x^V X → T_(f x)^V Y` is an equivalence. Select its `V = D`
(first-order pointed infinitesimal) consequence for a quotient
`q : M → M//G`, with `G` a crisp finite discrete ordinary group acting on a
set-valued smooth type `M`. The action is a family over `BG`, as in
§2.2; its quotient is the dependent sum of Definition 2.3.1.
The required additional conclusion is compatibility of this tangent
identification with the stabilizer identification of Corollary 2.3.3 and
transport in the tangent family (Definition 4.1.8, Remark 4.1.10).

Concretely, the target comparison is

```
Aut_[x](M//G) ≃ {g : G | g • x = x}
T_[x](M//G) ≃ T_x M
transport(g, v) corresponds to d(ρ_g)_x(v).
```

The assembled equivariant consequence is our selected target, not a single
numbered theorem in Myers and not a new Lean result. The second equivalence depends on the chosen chart lift `x`;
changing that lift uses the third equation. The fixed-point tangent fiber
is `T_x M`, not the residual-gerbe quotient `[T_x M/G_x]`. Composition and that dependence
are part of the contract, not equality of unlabeled orbit representatives.
The source supplies a pointed, 0-connected `BG`; it does not require `f`,
`x`, or the action itself to be crisp for this quotient-lifting argument.
Finiteness is useful for the application but stronger than the discreteness
used to obtain this tangent equivalence. Microlinearity is not needed merely
to define the pointed tangent or prove Proposition 4.3.5. It would be needed
for the paper's general tangent-module and orbifold conclusions.

The external counterpart is the smooth action groupoid: objects `M`, arrows
`G × M`, source `x`, target `g • x`, with tangent arrows
`(x,v) ↦ (g • x,dρ_g(v))`. For a finite discrete group acting by smooth
diffeomorphisms on the ordinary disk this is proper and étale: each source
component is the identity, each target component a diffeomorphism; the anchor
is a finite union of closed graphs over the Hausdorff disk. Those geometric
facts explain the classical comparison target; no assembled proper-étale
instance is claimed checked here.

At the disk origin all four labels survive and the quarter-turn sends
`v` to `i*v`. At a nonzero disk point the stabilizer is trivial. Native Lean
equality is proof-irrelevant and cannot store four loops. An orbit-set
quotient also loses those loops. The model must compare groupoid hom objects,
including their restriction to infinitesimal stages, not replace them by
native equality. A non-effective finite action is a useful additional guard:
labels acting trivially must still remain different arrows.

| Alternative | Why it is not the next target |
| --- | --- |
| Lemma 2.3.2 / Corollary 2.3.3 alone | Detects isotropy but does not connect it to the constructed infinitesimal object. Existing external action-groupoid code already supplies the classical side. |
| Theorem 6.4.1, finite quotient is an orbifold | Adds microlinearity and proper finiteness. Its proof invokes 5.4.1; it does not remove the higher/differential problem. Too much extra logic before testing the tangent connection. |
| Theorems 5.4.9 and 6.3.7, general crisp proper étale presentations | Require completion and modal descent, then compactness/finiteness arguments. They obscure the first compatibility failure behind stronger prerequisites. |

## Proof dependencies and what is actually being proposed

Proposition 4.3.5 identifies the fiber of the tangent pushforward with a
**contractible type of coherent fillers**, not a set of lifts modulo an
existence proposition. Lemma 4.3.4 supplies infinitesimal connectedness;
modal orthogonality supplies contractibility. The boundary identification at
`0` and its coherence with the map of arcs matter at a point with isotropy.

To justify the quotient hypothesis, the proof of [Theorem 5.4.1][quotient]
uses the shape-covering route and Lemma 4.3.7. There is a citation detail:
[*Modal Prism*, arXiv:1908.08034v3, Theorem 7.7][prism], asserts a
shape-fibration for a crisp group. The additional discrete-fiber hypothesis
here is necessary to conclude shape-étaleness: quotient fibers are merely
equivalent to the discrete group; modal maps which are modal fibrations are
étale (the modal-prism classification). It is not valid to quote 7.7 alone
as proving étaleness for every crisp group.

| Obligation | Internal derivation in the source | Constructed-model obligation | External comparison / current status |
| --- | --- | --- | --- |
| Identification and truncation | Lemma 2.2.5 and Lemma 2.3.2 use identity elimination and dependent-pair identities; Corollary 2.3.3 identifies loops. With a set and an ordinary group the quotient is a 1-type. | Hom groupoids must retain distinct arrows and substitution/transport; identities between arrows are set-level. | `ActionCategory` and stabilizers supply external arrows. A native equality translation is invalid. Higher semantics missing. |
| Dependent families and universes | `BG → Type`, Σ quotient, Π/function types, fibers and contractibility; function extensionality enters equality of arcs. §1.7 adopts univalent universes. | A scoped universe of set families over groupoid contexts and coherent reindexing is needed for this source authoring route. A full univalent universe of all 1-types is stronger, and is not supplied by a bare groupoid universe. | Existing restricted Π/Σ rule APIs and sheaf dependent products are set-level ingredients, not a model of these judgments. |
| Tangent family | Definition 4.1.8: pointed internal maps out of `D`; Remark 4.1.10: identity transport. Proposition 4.3.5 uses Σ-identity and coherent fillers. | Relative mapping groupoids, evaluation at zero, homotopy fibers and natural transport. | Need a comparison to analytic tangent vectors. Scalar derivative comparison is proved; arbitrary manifold tangent comparison is not. |
| Modal and crisp rules | Definition 3.2.1, Lemmas 4.3.4/4.3.7, Proposition 4.3.5. The crystalline nullification and crisp finite-limit property are used to establish connectedness. Shape and crisp discreteness establish the quotient's étaleness. | Interpret the modalities and the separate crisp judgment, with their actual laws, if replaying that proof. Do not postulate ordinary left exactness of the crystalline modality: Warning 4.3.9 excludes it. | Missing. The proposed model experiment proves the particular `D`-lifting statement directly; it does not claim to interpret these modal rules. |
| Infinitesimals and KL | Definition 4.1.1, Axiom 3, Lemma 4.2.9 and Lemma 4.3.4 provide the surrounding infinitesimal theory; Axiom 4 gives crisp pullback preservation. | Reuse the actual sheaf `R`, `D`, its zero map and first-order KL. Prove their comparison into the higher construction with evaluation and arbitrary parameters. | General Weil KL and all infinitesimal varieties are unnecessary for this first-order test. They remain needed for stronger source results. |
| Descent / quotient | A supplied action over `BG` makes the source quotient a Σ-type, not a Rezk-completion construction. | A classical action presentation must yield the correct quotient stack, with effective object descent and arrow descent. Pointwise action groupoids contain only trivialized torsors. | Set-valued sheafification and chart colimits are available. They do not provide stack completion or quotient torsor descent. |
| Microlinearity and finiteness | Not needed for the selected tangent-equivalence statement. 5.4.1 additionally uses microlinearity descent 4.3.13; 6.4.1 adds proper finiteness. | No claim of microlinearity, general Weil tests, tiny infinitesimals, Covering Property, or interval compactness is made by this prototype. | Theorems 5.4.7–9 use crisp colimit preservation/tininess; 6.3.7 adds 6.3.4 and 6.2.21. These are deferred, not silently discharged. |

This table separates the source proof from a smaller semantic test. Direct
`D`-lifting is sufficient for its first-order tangent conclusion. It is not
asserted equivalent to full crystalline étaleness; Remark 4.3.6 explicitly
leaves a related converse open. Establishing this test would advance the
combined model without yet furnishing the internal derivation of the whole
source theorem.

## Correspondence with the checked checkout

All local names below refer to the fixed #95 commit. Mathematical source
inspection does not upgrade these declarations' scope.

| Classification | Existing declarations and assumptions | Use and remaining obligation |
| --- | --- | --- |
| Proved, directly usable | `SmoothOpenSite.scalar_isSheaf`, `scalarSheafFact`, `kl`, `dualRepresentable` in `SmoothOpenScalar.lean`, `SmoothOpenKL.lean`. `SmoothGeometricKL.kl` requires scalar sheafness; `dualRepresentable` additionally requires subcanonicity. Both are supplied for the arbitrary-principal-cover topology. | Let `E = Sheaf SmoothOpenSite.topology Type`. Actual internal `R^D ≅ R×R`, and `D×yA ≅ y(dual A)`, with `dualRepresentable_parameter` for restriction. This is the all-stage test input. |
| Proved, directly usable | `SheafFunction.exponential`, `curry`, `evaluation`, `beta`, `eta`; `SheafDependentProduct.pi`, `baseChange`; `SplitSheafPi.substitution`. | Set-valued function objects and dependent reindexing. Reuse on the discrete part; no automatic groupoid lift of their laws. |
| Proved, needs comparison | `ManifoldRealization.homEquiv`, `reconstruct_map`, `map_reconstruct`, `principalIso_naturality`, `homEquiv_principal`. | All smooth maps and all sheaf arrows between interpreted Type-sized finite-dimensional real boundaryless manifolds, dimensions allowed to differ; no extra Hausdorff/countability assumptions. Not exponential, tangent, or transverse-limit preservation. |
| Proved, directly usable in reconstruction | `covering_local_inclusion`, `local_chart_principal`, `ChartFamily.contMDiff_of_localMap`, `Charts.realEquiv`. | #95's local chart lifting plus all-stage descent proves full faithfulness. Real sections identify ordinary points; they do not detect arbitrary infinitesimal sections. |
| Proved, needs comparison | `SmoothGeometricDerivative.derivative_interpret`, `derivative_real`, under `ContDiff ℝ ∞ f` and scalar sheafness; `GeometricProductRule` consumes the explicit synthetic scalar proof. | Scalar synthetic-to-analytic bridge. A vector-coordinate extension and the restriction to the disk are additional comparison work, not consequences of `homEquiv`. |
| Proved, needs comparison | `Applications/Orbifolds/QuarterTurn.lean`: `origin_stabilizer`, `nonzero_stabilizer`, `disk_action_smooth`, `disk_tangent`, `diskEllipse_tangent`. | Actual ordinary stabilizer and derivative targets. Disk uses `𝓘(ℝ, ℂ)`; manifold realization uses `Fin n → ℝ`. Supply the real-coordinate chart adapter, not an assumed definitional identification. |
| Proved external infrastructure | `Applications/Orbifolds/Equivariant.lean`, Mathlib `ActionCategory`, `stabilizerIsoEnd`. | Explicit labels, equivariant functors and coordinate-change comparisons. Their existence is not internal identity soundness. |
| Available, needs a constructed instance | Mathlib `Pseudofunctor.IsPrestack`, `IsStack`, `IsStack.of_isStackFor`, `isEquivalence_toDescentData`. | Pseudofunctors from `LocallyDiscrete Siteᵒᵖ` to `Cat`; `IsStack` includes effective descent, but does not require groupoid fibers. Construct the specific groupoid fibers, restriction coherence and descent, rather than asserting the class. |
| Genuinely missing | A discrete-sheaf embedding into these groupoid stacks with the needed function/evaluation comparison; finite torsor infinitesimal invariance; quotient relative `D`-mapping comparison. | These are the integration gap selected below. |
| Genuinely missing | Higher identity/J, suitable universe rules, modal operators and crisp contexts in the local internal language, and their smooth-model soundness. | `SquareKit.Internal.Derives`, `Internal.DependentFunctions` and `Internal.SyntheticScalar` are explicit restricted APIs. Native Lean Π, `Eq`, `Prop` or functions cannot fill those source-language holes. |

## One bounded next construction

Construct and test the **`C₄` quotient's pointed infinitesimal lifting
comparison in `E`**, using groupoids of torsors. This is a directly constructed
model theorem, with an external derivative comparison as its application.
It is not an implementation of all stacks or all dependent HoTT.

Let `G` be the locally constant finite group sheaf associated to the checked
quarter-turn group, not the naive constant presheaf. Over `yA`, an object of
the proposed quotient `Q(A)` is a `G`-torsor `P → yA` with an equivariant map
`P → M`; morphisms are equivariant isomorphisms over `yA` respecting that map.
A torsor is locally trivial for the **existing site's topology**. Its
isomorphisms retain group labels, including ineffective ones. Objects over
disconnected stages may have locally varying labels. The action-groupoid
chart describes trivialized objects, not all objects of `Q(A)`.

Here is the specific compatibility theorem to construct. Write `i` for the
discrete-sheaf embedding into the proposed groupoid semantics and `q:iM→Q`
for the trivial-torsor atlas. Require

```
i(R^D) ≃ Map(iD,iR), compatible with evaluation, zero, products and i(kl)
i(M^D) → iM ×ʰ_Q Map(iD,Q)   is an equivalence.
```

The second map uses evaluation at zero and `q`; `×ʰ` is a homotopy pullback
with its boundary isomorphism, not a strict equalizer of object functions.
The boundary isomorphism trivializes the torsor at zero. Full faithfulness
and essential surjectivity of the torsor equivalence must extend that
trivialization uniquely up to compatible isomorphism over `D×yA`. Its
equivariant map to `M` then becomes an `M`-valued arc. An equivalence of
isomorphism classes would not supply this argument.

These are to hold naturally over every parameter stage and its restrictions,
then descend to arbitrary parameter sheaves. They imply that the homotopy
fiber of quotient evaluation over the chosen lift is the existing pointed
sheaf of `D`-arcs. Transport along its automorphism is then compared to the
linear action on coefficients. This specifies how the existing differential
model participates in the higher semantics.

The decisive uncertainty is **finite torsor invariance across the represented
dual extension**. For each `A`, pullback along `D×yA→yA` must give an
equivalence of `G`-torsor groupoids, inverse to restriction at zero, including
morphisms and compatibility with base change. Full faithfulness of manifolds
says nothing about these torsors. `dualRepresentable` reduces this to a
concrete site question; a nilpotent algebra calculation alone does not prove
cover refinement, effective descent, or independence of trivializations.

Acceptance for this single prototype:

1. Construct the finite locally constant group sheaf, torsor groupoids,
   restriction pseudofunctor and effective descent using the current site.
   State universes explicitly: small site codes and Type-valued sheaves are
   fixed; categories of their torsors may live one level higher. No resizing
   or univalent universe is assumed to make this semantic construction fit.
2. Prove the torsor pullback equivalence above for all `A`, and its unit,
   counit and base-change coherence. Check a disconnected cover and a
   nonidentity dual-stage restriction. Include a nontrivial torsor example
   (a cyclic cover of an annulus is a candidate requiring construction), or
   identify and construct the smallest available site stage admitting one.
   A trivial-torsor-only example cannot establish the descent claim.
   Do not assume every torsor globally
   trivial or test only the ordinary real stage.
3. Construct the discrete inclusion's `R,D,R^D` comparison and the quotient
   homotopy-pullback comparison, preserving actual zero evaluation and the
   existing KL coefficients. The tangent fiber must be derived from these
   comparisons, not supplied as another field.
4. Consume `QuarterTurn.origin_stabilizer` and `disk_tangent` through a
   proved coordinate/open-domain `D`-arc comparison. At the base quotient point `q(0)` retain four
   automorphisms acting on the fixed-lift tangent fiber and recover `v↦i*v`; at a nonzero point recover trivial
   isotropy. Include a trivially acting finite group on the scalar line to
   ensure that identity tangent maps do not collapse distinct labels.
   These are checked external targets already available in part, and
   specified new applications of the missing comparison, not claimed
   completed mixed-model examples.
5. Use EDD and statement review for all new claims, retain ordinary and
   opt-in internal clients without added obligations, and pass fresh-source
   checks and the exhaustive axiom audit. If the torsor equivalence fails,
   exhibit the precise stage, torsor/descent datum, or failed hypothesis;
   report the counterexample and the smallest required site correction.
   Do not weaken the test to trivial torsors to obtain a pass.

A successful prototype would prove that first-order differential probes and
nontrivial identity transport coexist for this finite quotient in one
constructed semantic setting. It would not prove a general dependent-language
soundness theorem, univalence, cohesion, crisp rules, all Weil KL,
microlinearity, proper finiteness or the proper étale comparison theorem.
Those later choices remain provisional.

### Why no additional Lean experiment is included in #96

The question was whether a finite singular action can discriminate a route
that merely places the models side by side from a route that combines them.
The existing quarter-turn proofs already settle the external algebra and
analytic derivative. Repeating them or making the pointwise action groupoid
of `M(dual A)` would not test effective descent or infinitesimal torsors.
There is no current quotient stack, relative mapping groupoid, or torsor
pullback equivalence to specialize. Assuming those as record fields would
assume the connection being investigated.

The smallest useful new experiment is therefore the torsor equivalence in
items 1–2, followed by the specified pointed quotient comparison; building it
is the proposed successor, not a scratch validation hidden in this research
task. Failure of arrow descent, essential surjectivity under the dual
extension, or coefficient compatibility rejects the proposed route as stated.
Success for pointwise/trivialized objects alone supports neither conclusion.
No Lean claims, axioms, tooling, or build configuration are changed here.

### Disposition of #97

**Propose deferral of #97 as the next implementation task.** Neither the
selected first-order statement nor its torsor test needs preservation of
arbitrary transverse manifold pullbacks. The necessary squares are the
represented dual product, zero evaluation, and the quotient's homotopy
pullback. Ordinary open-domain tangent comparison may require a narrower
open-restriction lifting result; prove that actual requirement within the
test. It is not general transversality. Full manifold well-adaptedness may
later justify #97, but that is not a conclusion of this investigation.
The issue's scope and status have not been changed.

## Targeted references and reuse boundary

The [standalone archive guide][archive] and both linked reviews were read
before selecting reuse. Its external torsor evaluation arguments can explain
trivialized fibers, but cannot establish torsor descent or the dual-extension
equivalence. The retained checkpoint hash is
`788934695d97bd71e34271f29bed615c4106c9acc4b8736804f196e39cad2c9b`,
with Lean 4.33.0-rc1 and no external Lake dependencies. No LICENSE file was
found in the archive listing; code-copy permission is unresolved. The earlier
review, not a new build here, reports a 4.35.0 rebuild and audit.
No archive code is selected for import, and its replacement
algebra/category hierarchy remains excluded.

| Identified gap | Inspected source / version | Use and trust boundary |
| --- | --- | --- |
| Coherent identity, Σ paths and transport | *Homotopy Type Theory: Univalent Foundations of Mathematics* (2013), §§2.3, 2.7, 2.9, 2.12 and §9.9; Myers §2. | Mathematical proof arguments to translate into explicit rule APIs. The book's native HoTT foundation is not Lean 4 equality; §9.9 completion is later than the supplied-family Σ quotient used here. |
| Crisp/modal justification of quotient lifting | Myers v1 §§3.1–3.2, 4.3, 5.4; *Modal Prism* v3 §3 and Theorem 7.7. | Mathematical justification and precise hypothesis checks. Direct semantic `D`-lifting does not require claiming all of these modalities have been constructed. |
| Existing smooth scalar and analytic comparison | Kock, *Synthetic Differential Geometry*, second edition, author's March 2006 PDF, III.1, III.3, III.8. | Exponential/dual-stage and analytic comparison arguments. Theorem III.8.4's well-adaptedness, including transverse limits, is stronger than the selected torsor test. It does not prove the higher compatibility on this particular site. |
| Quotient stack via torsors/descent | Mathlib `CategoryTheory/Sites/Descent/IsStack.lean`, pinned `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean 4.35.0, Apache-2.0. | Reusable current Lean interface: arrow descent plus essentially surjective descent functors. Its imported `DescentData` infrastructure supplies categorical laws, not the smooth torsor instance. Use the repository audit on the actual consumer's transitive dependencies. |
| Torsor descent and quotient interpretation | Stacks Project tag [04UJ](https://stacks.math.columbia.edu/tag/04UJ), Lemma 95.14.2, accessed 2026-10-20; Nikolaus–Schreiber–Stevenson, [arXiv:1207.0248v3](https://arxiv.org/html/1207.0248v3), Theorem 3.17 and Definition 4.2/Example 4.4. | Proof arguments: glue torsor sheaves and actions; interpret associated bundles by action quotients. The Stacks statement is on an fppf site, and NSS assumes an infinity-topos. Neither is an instantiated theorem on our smooth site. No code reuse. |
| Possible nilpotent invariance argument | Stacks Project tag [0ALI](https://stacks.math.columbia.edu/tag/0ALI), Lemma 15.11.2, accessed 2026-10-20. | Invariance of étale algebras under a locally nilpotent ideal is an analogy, not our torsor theorem. Applying it would require a proved comparison with smooth-site torsors; no such comparison was located. Prefer a direct site proof. |
| Possible higher dependent semantic component | SynthLean/HoTTLean `31133dd5b25226ea897f8aa5e2e43b61392459eb`, Apache-2.0, Lean 4.25.0-rc2; Mathlib `32bd6c7c8ca4a4be1c71bc04df0c9cf929d04818`, Poly `aedee22f07d681d845bcbe4a1fb9aa10f95c9977`. | Re-inspected `Groupoids/Id.lean`: `FunctorOperation.IdObj` is the discrete groupoid of arrows and `IdMap` conjugates by endpoint transport. `Groupoids/UnstructuredModel.lean` constructs a groupoid universe. Useful semantic proof design, not a smooth stack model. No source import selected. |

[HoTT book](https://homotopytypetheory.org/book/),
[Kock's author PDF](https://users-math.au.dk/kock/sdg99.pdf),
[Mathlib stack interface](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Descent/IsStack.lean),
[SynthLean identity semantics](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Groupoids/Id.lean).

SynthLean's checker imports conjectured external axioms `EqTp.inv_pi`,
`EqTp.inv_sigma`, `EqTp.inv_Id` from `Syntax/Injectivity.lean`. The separate
Natural path's `ForPoly.lean` contains admissions. This does not show that
every groupoid theorem depends on them; a declaration-level dependency audit
and port would precede any reuse. The inspected files were not rebuilt for
#96 and no dependency was added. This boundary agrees with the earlier
[assessment](internal-languages-lean.md#synthlean--hottlean), rather than
promoting a README claim to a trusted model theorem.

The custom-kernel SDG library and archive's native compactness predicates
were already rejected as direct model implementations in the linked
assessments. They do not address the identified torsor/descent gap, so no new
broad formal-library search or port is proposed. No separate research ticket
is necessary to express this bounded next construction; if its site-level
torsor obligation proves obstructed, that evidence must specify the actual
follow-up before one is linked from #96.

## Formalization handoff and validation

| Handoff | Authoring format and available entry points | Explicitly unsupported |
| --- | --- | --- |
| Torsor/quotient prototype, items 1–3 | Directly constructed model theorem in ordinary Lean using `Sheaf`, `SmoothOpenSite`, Mathlib pseudofunctor/descent and groupoid APIs. Interpret mapping/fiber notation by these constructions and prove the comparison. | No general internal derivation is claimed; no model field may merely assume the target compatibility. |
| Quarter-turn application, item 4 | External comparison theorem using `QuarterTurn.disk_tangent`, `origin_stabilizer`, `SmoothGeometricKL` coefficients and the new model theorem. | Full faithfulness does not provide tangent or coordinate comparisons automatically. |
| Eventual source proof of the selected consequence | Lean derivation over explicit internal rule APIs, extending the current `Internal.Logic`, `DependentFunctions`, `SyntheticScalar` only after a scoped model is validated. | Higher Id/J, dependent sums over `BG`, universe classification and crisp/modal judgments are not currently available there. Native Lean proofs cannot be exported as those derivations. |
| Optional later author interface | Opt-in frontend elaborating to those derivations, with checked interpretation, ordinary clients unchanged. | No frontend implementation is requested; syntax cannot supply missing semantic rules. |

An external formalization request must carry these exact APIs, the
all-stage homotopy-pullback statement, the torsor and universe definitions,
and the quarter-turn checks. Supplying only the theorem name and ordinary
Lean groups would invite another external theorem without its interpretation.

This delivery changes research records only. Validation checks links, named
declarations against the fixed checkout, pinned source evidence, and the
candidate diff. No fresh Lean build is claimed for a documentation-only
change; #95's accepted fresh-source/audit result remains historical evidence
for its unchanged Lean tree. Independent Standards and Spec review results,
immutable candidate SHA, complete requirements, and validation details are
recorded outside the source diff and reported on #96 after both axes pass.

[myers]: https://arxiv.org/html/2205.15887v1
[tangent]: https://arxiv.org/html/2205.15887v1#S4.SS3.Thmthm5
[quotient]: https://arxiv.org/html/2205.15887v1#S5.SS4.Thmthm1
[prism]: https://arxiv.org/abs/1908.08034v3
[archive]: ../history/orbifold/standalone-formalization/README.md
