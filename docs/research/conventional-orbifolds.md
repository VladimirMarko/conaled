# Conventional orbifolds: reuse and comparison plan

Assessment for [#40](https://github.com/VladimirMarko/conaled/issues/40),
2026-10-18. This selects a conventional first comparison and records its
missing prerequisites. It adds no production Lean claims or dependencies.
The constructed internal model remains a goal of
[#36](https://github.com/VladimirMarko/conaled/issues/36); conventional
presentations supply useful mathematics and future comparison targets.

## Recommendation

Start with finite smooth actions and their explicit action groupoids on the
pinned Mathlib. Adapt the smallest quotient-diffeology API needed to compare
an equivariant coordinate change on both groupoids and smooth quotients.
Retain ineffective actions in the groupoid layer. Do not adopt lean-catdg as
a whole dependency: its foundational API overlaps Mathlib, its versions differ,
and some geometric results have admitted dependencies. The source/build/audit
inventory below distinguishes candidates for adaptation from certified imports.

This refines [#32's slices A–D](myers-orbifold-assessment.md#follow-up-tasks).
[#39](https://github.com/VladimirMarko/conaled/issues/39) owns projective disk
motions and exact matrix/coordinate realizations. At assessment base
`00946f11d220ef90d9fb1aff2fffccaa080232d4`, no disk implementation is present
under `Applications` or `Examples`; #39 is open. The first comparison can
start with a finite linear action without duplicating that motion backend.

## Source, compatibility and proof evidence

### Pins and compatibility

Inspected lean-catdg at
[`1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4`][catdg]. Its
[license][license] is Apache-2.0; retain its notices when adapting code.
Its [toolchain][toolchain] is Lean 4.29.0; its [manifest][manifest] pins Mathlib
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. Mathlib is its direct Lake
dependency, with the manifest recording the inherited tooling dependencies.
Conaled remains on Lean 4.35.0 / Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

An actual local compatibility probe, running the unmodified CatDG
`Diffeology/Basic.lean` with conaled's `lake env lean`, failed at line 158
on a source-composition goal for `OpenPartialHomeomorph.univBall` and its
inverse. This is one demonstrated failure, not an inventory of every porting
change. Separately, CatDG Basic redeclares global `DiffeologicalSpace` and
`DSmooth`; Mathlib already defines them and has renamed APIs including
`Diffeology.dSmooth_iff_contDiff`, `dTopology`, `IsDTopologyCompatible` and
`IsContDiffCompatible`. Importing both foundations is not a compatible reuse
strategy.

### Capability and adoption inventory

Links in this table pin the inspected source. “Adapt” means port onto the
existing Mathlib foundation and rerun statement review and dependency audits;
it is not approval to import the current module wholesale.

| Construction | Implemented definitions and results; missing operations | Recommendation |
|---|---|---|
| [Diffeology core][ml-diff] | Mathlib plots, `DSmooth`, finite-dimensional `ContDiff` compatibility, D-topology and generated-plot complete lattice. Only `Basic.lean` exists in its diffeology directory at the pin. | Adopt existing Mathlib; do not copy CatDG's duplicate core. |
| [Induced/coinduced spaces][induced] and [quotients][constructions] | Subspace/quotient instances, `DSmooth.quotient_lift`, `isPlot_quotient_iff`, quotient subduction. Depends on CatDG Basic, Continuous, Induced, DSmoothMap and Reflexive infrastructure. | Adapt the minimal quotient/subspace closure; upstream general lemmas. This is the first missing prerequisite. |
| [Local models and orbifolds][local] | `LocallyModelled`, `IsOrbifold`, D-open restriction; manifold-to-orbifold instance. Local compactness depends on an admitted finite-quotient result. | Adapt the local-model predicate and safe restriction results after quotient APIs; repair local compactness before reuse. Do not treat this as a full orbifold theory. |
| [Manifold smoothness][manifolds], [embedding][mfld-embedding] | `ContMDiff.dsmooth`, `DSmooth.contMDiff`, `contMDiff_iff_dsmooth`; `FinDimMfld.fullyFaithfulForgetToDiffSp`. Converse uses finite-dimensional boundaryless source hypotheses. `IsOpen.dsmooth_iff_smoothOn` is admitted separately. | Adapt the needed bridge preserving hypotheses. Use Mathlib ordinary manifolds for the first tangent action. |
| [Diffeological tangents][tangent] | `InternalTangentSpace`, `internalTangentMap`, identity/composition laws; vector-space comparison uses admitted injectivity and surjectivity. The definition has the additional semantic defect below. | Do not adopt the current tangent quotient. Correct its relations and prove vector-space/manifold comparisons before considering reuse. |
| [Category of diffeological spaces][diffsp] | Category, limits/colimits, Cartesian closed infrastructure, discrete/indiscrete and topology adjunctions. Uses Constructions and DDiffeomorph plus Mathlib category machinery. | Adapt later if a consumer needs it; the first quotient square does not require this entire category. |
| [Smooth spaces][smoothsp] | Set-valued sheaves on `CartSp`; `DiffSp.toSmoothSp.fullyFaithful` and `DiffSp.reflectorAdjunction` give embedding/concretization. `SmoothSp.Ω` is unfinished. | Candidate selective adaptation for #36's set-level smooth semantics; neither higher stacks nor a constructed differential cohesive model. |
| [Sites][sites] and [cohesion][cohesion] | Cartesian/open Euclidean and manifold sites, concrete/local-site tools; abstract adjoint-quadruple `CohesiveStructure`. `CohesiveSite.lean` has unfinished proofs. | Reuse Mathlib sheaf/category infrastructure first; audit any additional site adapter individually. Construct the required model under #36 rather than assuming its law fields. |
| [Action groupoids][ml-action] and [ordinary tangents][ml-tangent] | `ActionCategory`, groupoid instance and `stabilizerIsoEnd`; manifold tangent maps and chain-rule API. | Adopt. Implement equivariant adapters and geometric instances; preserve the distinction between a groupoid and a smooth proper étale presentation. |

The bounded inventory did not locate proper étale smooth groupoids, Morita
comparison or effective-orbifold reconstruction in CatDG or pinned Mathlib.
CatDG's [README][catdg-readme] treats richer orbifolds and differential cohesion
as future work. This finding concerns the inspected sources, not every Lean
library.

**Tangent statement review.** At the pin, `InternalTangentSpace` quotients the
direct sum of pointed plot domains by generators
`lof p w - lof q (fderiv ℝ f 0 w)` for arbitrary plots `p,q` and smooth `f`.
It imposes neither `p = q ∘ f` nor `f 0 = 0`. Taking a constant-zero `f`
makes every `lof p w` a relation, collapsing the intended tangent space.
This is our mathematical analysis of the definition, not an additional
checked Lean theorem. Functoriality of that quotient can pass an axiom audit
without validating its intended geometry. Keep the ordinary manifold tangent
action separate from both this quotient and the tangent of an orbit space.

### Existing upstreaming

Mathlib [PR 26484](https://github.com/leanprover-community/mathlib4/pull/26484)
and [PR 26973](https://github.com/leanprover-community/mathlib4/pull/26973)
merged diffeology basics and generated plots. The author's
[PR 27274](https://github.com/leanprover-community/mathlib4/pull/27274) was
open/unmerged at inspection, head
`ba44f2cdb02cb547e795c9c65c59147de35197cd`. It develops continuous
diffeologies/D-topology and explains its role in preserving definitional
topology compatibility for coinduced diffeology. Coordinate the quotient port
with this work; a moving PR does not change our pinned Mathlib inventory.
CatDG's README also records earlier upstreaming of delta-generated spaces,
global sheaf sections and adjoint triples. Those are components, not an
upstream orbifold theory.

### Build and transitive audit results

The selected upstream build passed under its own pins, with admission
warnings. The imported CatDG closure **fails** the repository whitelist:
transitive traversal of all 2,638 kernel-safe CatDG declaration roots in the
four imports below finds `sorryAx` in addition to `propext`,
`Classical.choice` and `Quot.sound`. This includes private/generated kernel
roots identified by module origin; unsafe runtime declarations are excluded.
The traversal shares a visited set, giving the union of dependencies without
repeating the full graph traversal for every root. Selected `#print axioms`
commands separately attribute the results below.

| Upstream roots | Transitive result under Lean 4.29.0 |
|---|---|
| `IsOrbifold`, `IsOpen.isOrbifold`, `DSmooth.quotient_lift`, `isPlot_quotient_iff`, `contMDiff_iff_dsmooth`, `DiffSp.toSmoothSp.fullyFaithful`, `DiffSp.reflectorAdjunction` | Exactly the three permitted axioms; candidates for selective adaptation, not tested ports. |
| `internalTangentMap_comp` | Exactly the permitted axioms, but the statement concerns the defective tangent quotient discussed above. |
| `IsOrbifold.locallyCompactSpace`, `InternalTangentSpaceVectorSpaceEquivSelf` | The permitted axioms plus `sorryAx`; forbidden dependencies of these specific results. |

The manifold-with-boundary admission in `LocallyModelled` does not contaminate
`IsOpen.isOrbifold`; the finite-quotient compactness admission does contaminate
`IsOrbifold.locallyCompactSpace`. Likewise the unfinished differential-form
object in `SmoothSp` does not contaminate the audited embedding/reflector
roots. File-level source searches alone would not establish these distinctions.

Under the local 4.35.0 pin, transitive `#print axioms` checks also passed for
`Diffeology.dSmooth_iff_contDiff`, `DiffeologicalSpace.generateFrom`,
`DiffeologicalSpace.gc_generateFrom` and `tangentMap` (the three permitted
axioms), and `CategoryTheory.ActionCategory.stabilizerIsoEnd` (`propext` and
`Quot.sound`). These checks certify named roots, not all of Mathlib or the
future comparison. CohesiveSite and the whole CatDG default target were not
built/audited. No claim of a clean wholesale import follows.

Reproduction uses an external checkout at the CatDG pin. From conaled:

```sh
git clone https://github.com/peabrainiac/lean-catdg /tmp/conaled-40-catdg
git -C /tmp/conaled-40-catdg checkout 1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4
direnv exec . bash -c 'cd /tmp/conaled-40-catdg && lake exe cache get'
direnv exec . bash -c 'cd /tmp/conaled-40-catdg && lake build CatDG.Diffeology.LocallyModelled CatDG.Diffeology.TangentSpace CatDG.Diffeology.MfldToDiffSp CatDG.Diffeology.SmoothSp'
direnv exec . lake env lean /tmp/conaled-40-catdg/CatDG/Diffeology/Basic.lean
```

The last command is the deliberately failing 4.35 compatibility probe.
Save the following audit fixture as `ConaledAudit.lean` in the external clone
and run `direnv exec . bash -c 'cd /tmp/conaled-40-catdg && lake env lean ConaledAudit.lean'`.
This is an audit command, not a new geometric formalization:

```lean
import CatDG.Diffeology.LocallyModelled
import CatDG.Diffeology.TangentSpace
import CatDG.Diffeology.MfldToDiffSp
import CatDG.Diffeology.SmoothSp
import Lean.Util.CollectAxioms
#print axioms IsOrbifold
#print axioms IsOpen.isOrbifold
#print axioms IsOrbifold.locallyCompactSpace
#print axioms DSmooth.quotient_lift
#print axioms isPlot_quotient_iff
#print axioms internalTangentMap_comp
#print axioms InternalTangentSpaceVectorSpaceEquivSelf
#print axioms contMDiff_iff_dsmooth
#print axioms DiffSp.toSmoothSp.fullyFaithful
#print axioms DiffSp.reflectorAdjunction
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, info) in env.constants do
    if !info.isUnsafe then
      if let some idx := env.getModuleIdxFor? name then
        let mod := env.header.moduleNames[idx.toNat]!
        if `CatDG |>.isPrefixOf mod then
          roots := roots.push name
  let (_, state) := ((roots.forM Lean.CollectAxioms.collect).run env).run {}
  logInfo m!"AUDIT ROOTS {roots.size}; UNION {state.axioms}"
```

For the local audit, a temporary file importing
`Mathlib.Geometry.Diffeology.Basic`, `Mathlib.CategoryTheory.Action`,
`Mathlib.Geometry.Manifold.MFDeriv.Tangent` and `Lean.Util.CollectAxioms`,
with `#print axioms` for each local root listed above, was checked with
`direnv exec . lake env lean /tmp/Conaled40MathlibAudit.lean`.

Validation of this deliverable is source inspection, those selected builds
and transitive audits, and documentation link/whitespace checks. No production
Lean source changed, so no new full-project source check is reported. Any port
or new comparison must enter the public import closure and pass `check.sh`;
these external probes cannot replace that gate.



## Conventional descriptions and their obligations

| Description | What its data retains | Available basis and missing obligations |
|---|---|---|
| Finite smooth action `G ↷ M` | Named group elements, action laws, smooth maps; permits ineffective kernels | Mathlib actions, manifold derivatives and finite groups. Prove the concrete action smooth, its stabilizers and tangent representation. No atlas or synthetic interpretation is needed for these statements. |
| Action groupoid `G ⋉ M` | Objects `x`, arrows `(g, g • x = y)`, composition and all isotropy, including ineffective labels | Mathlib `ActionCategory` supplies the ordinary groupoid. An equivariant-map functor and its smooth/tangent compatibility are the selected adapters. Its category instance alone says nothing about properness or étaleness. |
| Smooth proper étale presentation | Manifold objects/arrows, smooth structure maps, local diffeomorphic source/target, proper `(s,t)`; may be ineffective | For a finite discrete group acting smoothly on a Hausdorff manifold, prove these facts using finite copies of the manifold and the action diffeomorphisms. General atlases need compatible chart changes, smooth functors and descent/Morita comparisons. No assembled interface was found in the inspected sources. |
| Diffeological orbifold | Smooth plots on a quotient, locally finite linear-group quotient charts; no chosen arrow labels | lean-catdg's `IsOrbifold n` uses finite **subgroups** of real linear equivalences, hence effective local models. It does not bundle Hausdorffness/second countability. Proving an arbitrary smooth finite action quotient satisfies it needs local linearization and quotient-chart compatibility; the definition is not that theorem. |

For the selected finite action, smoothness, chain rule, quotient descent and
coordinate conjugacy are concrete missing obligations over existing ordinary
analysis. The internal route additionally requires constructed infinitesimals,
higher identity semantics, modalities, soundness and their compatibility.
That difference supports doing this conventional slice first. It does not
estimate the effort of a general orbifold library or make the internal route
optional as a project goal.

### Effective reconstruction and ineffective loss

Iglesias, Karshon and Zadka's [*Orbifolds as diffeologies*, v2][ikz]
proves lifting for diffeomorphisms of finite linear quotients (Lemma 23),
invariance of local structure groups (§4), and recovery of compatible
Haefliger atlases (Theorem 46). Satake comparison in Theorem 39 adds
Hausdorffness and excludes reflections. These are paper results, not Lean
results inspected here. They justify retaining quotient **diffeology**, rather
than concluding from a set-valued carrier that effective isotropy is
unrecoverable. Arbitrary smooth maps do not have the same lifting theorem
(Examples 24–25); this is not an equivalence of unrestricted map categories.

Our counterexample for ineffective information is a nontrivial finite `K`
acting trivially on a manifold `M`. Its orbit quotient with quotient diffeology
is diffeomorphic to `M`, while every action-groupoid isotropy group is `K`.
Taking the faithful image of an action removes its kernel. Thus this
observation cannot recover ineffective labels. This is a mathematical argument
to formalize in the first slice, not a checked theorem added by this assessment.

## Comparison map inventory

Write `Q(G,M)` for the orbit set equipped with quotient diffeology and `q`
for its projection. All maps in this table are proposed contracts unless
identified as existing infrastructure. Smoothness hypotheses apply to real
smooth manifolds without boundary in the first slice.

| Map: domain → codomain | Hypotheses and intended result | Arrows, isotropy and tangents |
|---|---|---|
| `F_(phi,f): G ⋉ M → H ⋉ N` | `phi : G →* H`, `f(gx)=phi(g)f(x)`; functor preserving identities/composition. Smoothness only for a smooth presentation functor. | Sends `(g,x)` to `(phi(g),f(x))`. Gives `G_x → H_(f x)`, which need not be injective or surjective. If smooth, `Df_(g x) Dg_x = D(phi(g))_(f x) Df_x` by chain rule. No tangent isomorphism for arbitrary `f`. |
| Coordinate equivalence `F_(phi,f)` | `phi` a group isomorphism and `f` an equivariant diffeomorphism; construct inverse and inverse laws. | Equivalence of these explicit presentations, isotropy isomorphisms and invertible tangent intertwiners. This restricted case needs no general Morita theorem. |
| `bar f : Q(G,M) → Q(H,N)` | Smooth equivariant `f`; quotient universal property gives smooth descent and `bar f ∘ q_M = q_N ∘ f`. A diffeomorphism follows for the preceding coordinate equivalence. | Forgets chosen arrow labels. Effective local isotropy can be reconstructed under the cited orbifold hypotheses; ineffective kernels cannot. No automatic identification of its diffeological tangent with an isotropy representation. |
| `G ⋉ M → Discrete(M/G)` | Orbit projection on objects, identity arrows on each orbit; ordinary functor/coarse observation. | Collapses all stabilizers and parallel arrows. On a free transitive component this can be an equivalence of bare groupoids, but that alone is no smooth descent theorem. It carries no tangent bundle. |
| Diffeological quotient → underlying set/topological quotient | Forget plots, or use D-topology and prove agreement with quotient topology. | Forgetful observations; reconstruction from diffeology does not justify reconstruction from these weaker observations. No tangent preservation asserted. |
| `R → P` for #39 exact realizations | `P` is the negative-line point space; decoder and operation square supplied by #39. Restrict to its finite rotation action, prove decoder equivariance and smooth coordinate bridge before attaching `Q(G,P)`. | The projective scalar quotient identifies representatives of one motion. The later finite symmetry quotient identifies points and has stabilizers. These quotients serve different purposes. Derivative preservation requires a smooth bridge, beyond the exact operation square. |
| `TM → M` and `G ⋉ TM → G ⋉ M` | Differentiate the smooth action; prove action laws via chain rule and projection equivariance. | At `(x,v)` the stabilizer is the subgroup of `G_x` fixing `v`. Retains the full `G_x` representation on `T_xM`; taking its orbit space is a different operation. |
| Smooth presentation → internal action quotient/completion | A constructed model, interpretation of the action diagram and a proved descent/completion comparison. | Intended equivalence on the selected interpreted fragment, including loop/isotropy and tangent transport compatibility. Blocked by the relevant model results in #36, not supplied by an ordinary quotient or square. |

For general presentation changes, use smooth functors or spans that are
Morita equivalences with explicit local lifting/descent hypotheses. Establish
induced quotient diffeomorphisms and compatible tangent-bundle descent before
claiming presentation independence. An equivalence of the underlying abstract
categories does not establish these smooth hypotheses.

## First comparison experiment

The selected target is the smooth quotient of a finite linear action, together
with its action-groupoid presentation. Compare two independently specified
coordinate actions, keeping both an arrow-level equivalence and a quotient
smooth map. This is a useful conventional target before a general proper étale
interface or synthetic model exists.

**Intended theorem (schematic notation).** For a group isomorphism `phi : G ≃* H`, manifolds `M,N`,
smooth actions, and an equivariant diffeomorphism `f : M ≃ₘ N`, construct
`F : ActionCategory G M ≌ ActionCategory H N` and
`bar f : Q(G,M) ≃ᵈ Q(H,N)`. Prove
`bar f (q_M x) = q_N (f x)`, the restriction of `phi` is an isomorphism
`G_x ≃* H_(f x)`, and

```text
Df_x (D(g•)_x v) = D(phi(g)•)_(f x) (Df_x v).
```

Here `g ∈ G_x` in the fiber statement. The more general action formula has
`Df_(g x)` on its left, with codomain `T_(f(g x))N`. State these separately
to avoid accidentally applying a fixed-fiber formula away from a stabilizer.
Require no effectiveness for the theorem; effectiveness enters only future
reconstruction claims. Identity and composite coordinate changes must agree
on functors, quotient maps and tangent intertwiners, with dependent transports
made explicit.

The public consumer is [`RawMap.ofFunctor` and its laws](../../SquareKit/CategoryMap.lean)
for `F.functor`, retaining equality of explicit arrows, and a
[`Squares.Square`](../../Squares.lean) with decoders `q_M,q_N` and horizontal
maps `f,bar f`. Pasting another coordinate change must use the existing square
composition. The quotient square alone cannot certify arrow equivalence.
Later paste #39's exact decoder only after proving the rotation-equivariance
bridge; no claim that arbitrary disk motions descend to a fixed cone quotient.

### Required specializations

These are proposed checked cases; the calculations below are mathematical
proof plans, not numerical probes or newly checked Lean results.

1. **Manifold:** the trivial group on `M`. Identify `Q(1,M)` smoothly with
   `M`, the groupoid with the discrete groupoid on `M`, and each isotropy with
   the trivial group. Use a nonidentity smooth coordinate change.
2. **Quarter-turn cone:** on `D={z:ℂ | ‖z‖<1}`, let `C₄` act by `i^k z`.
   Prove the exponent convention, closure and action laws. At zero all four
   labels remain; at every nonzero point cancellation makes the stabilizer
   trivial. Under the ordinary disk tangent trivialization, the tangent action
   is `v ↦ i^k v`, nontrivial at the apex. An equivariant vector field has
   value zero there, without restricting arbitrary trajectories to stop.
3. **Ineffective action:** nontrivial finite `K` acts trivially on `M`.
   Construct `Q(K,M) ≃ᵈ M`, while the isotropy is `K` and its tangent
   representation is trivial. This disproves an unrestricted reconstruction
   claim, even though quotient diffeology carries more than a bare orbit set.
4. **Coordinate change:** real linear `B(x,y)=(2x,y)` sends the disk to an
   ellipse. Independently define its generator as
   `R'(x,y)=(-2y,x/2)` and the disk generator as `R(x,y)=(-y,x)`.
   Prove `BR=R'B`, smooth inverse, and the groupoid/quotient/tangent comparisons
   through the public theorem. At the apex the representations are conjugate,
   not equal as matrices. This exercises coordinate change without #39's
   projective-motion backend or a general atlas theorem.

### Missing prerequisite and implementation boundary

The pinned Mathlib diffeology file has the basic smoothness and generated
structure machinery, but no quotient-diffeology/subspace descent API.
The complete experiment therefore cannot yet be obtained by specializing
existing public results. lean-catdg's candidate API needs adaptation and
rechecking against the current foundation. No desired comparison has been
inserted as an assumption, and no temporary experiment is represented as a
production checked bridge.

[#41](https://github.com/VladimirMarko/conaled/issues/41) owns that prerequisite and the bounded comparison. Its
acceptance requires quotient universal properties, the equivariant functor,
coordinate equivalence, tangent intertwining, all four cases above and public
SquareKit consumers. Every new formal claim needs statement review, checked
specializations, public import coverage and the full source/transitive audit.
Ordinary clients must need no internal-language parameters or setup.

## Connection to the constructed internal model

This extends the [Myers correspondence](myers-orbifold-assessment.md#theorem-correspondence)
and [#35's model stages](internal-languages-lean.md#stages-and-follow-up-tasks).
The statements below are future obligations, not claims discharged by either
library. Let `I` denote the smooth-object/action interpretation into a model
constructed under #36, and `C` its action quotient or completion operation.

| Myers target | Precise additional comparison obligation | Ownership and dependency |
|---|---|---|
| §2.3 action quotients, Lemma 2.3.2 | Construct a comparison `C(I(G ⋉ M)) ≃ I_action(M//G)` in the chosen model. Specify what `I_action` constructs and prove naturality in equivariant maps; preserve identity/composition up to the model's stated coherence. It must not interpret the ordinary coarse set quotient as the higher quotient. | Classical functors can start now; construction of the internal quotient, interpretation and equivalence depends on #36's higher/model semantics. |
| Corollary 2.3.3 isotropy | Compare the interpreted stabilizer group at `x` with the loop object at its quotient point, preserving multiplication, unit and inverse. Include ineffective `K` and transport along the coordinate equivalence. | External stabilizer isomorphisms now; loop interpretation and its equivalence under #36. |
| §4.1 tangents and transport | Construct a natural comparison from the interpretation of `TM` to the internal infinitesimal tangent object of `I(M)`. Prove compatibility with projection, derivatives and the action of interpreted arrows; require the tangent/isotropy square to commute. | Ordinary chain-rule action now; infinitesimal object, KL validity and derivative comparison depend on the constructed SDG fragment in #36. A dual-number calculation alone is insufficient. |
| §5.4 completion and Theorem 6.3.7 | Interpret the chosen smooth proper étale presentation; prove required smooth descent, local-diffeomorphism/étale comparison, and that its completion satisfies the source microlinearity and proper-finiteness hypotheses. Prove invariance under the selected smooth presentation changes, including coherence of the completion comparison. | Classical properness/étaleness and restricted changes can proceed now. Synthetic descent, crispness, microlinearity and proper finiteness require #36; external `Finite` or topological properness cannot silently replace them. |
| Theorem 6.4.1 finite quotient | Recover the selected finite-action theorem only after proving its interpreted hypotheses and comparing its quotient with the classical presentation above. | Can consume the conventional examples; model soundness and the synthetic conclusion remain #36 work. |

A concrete site, sheaf category, or smooth-space embedding is a candidate
component for `I`, not the full interpretation functor. Specify the logical
fragment each functor preserves, comparison natural transformations and unit/
composition coherence before transporting a theorem. Existing commuting
squares express resulting preservation equations; they neither construct a
higher smooth model nor prove an equivalence of presentations.

## Dependency-ordered follow-ups

| Work | Starts from / depends on | Acceptance and ownership |
|---|---|---|
| Quotient API and coordinate experiment | Existing Mathlib actions, analysis, diffeology core; SquareKit maps/squares | [#41](https://github.com/VladimirMarko/conaled/issues/41). Start now. Adapt a small audited subset; establish the full experiment above. Refines #32 A/C and its comparison consumer. |
| Disk-action integration with exact realizations | Reuse the preceding action if it lands first, or #39's action if already available | #39 retains positive similitudes, scalar quotient, negative lines and matrix/gyro backends. Prove rotation equivariance of its decoder and paste the quotient observation. This needs #39's decoder only for this integration, not for the assessment or generic comparison. Reconciles #32 B. |
| Finite-action proper étale presentation | Smooth action and tangent infrastructure from #32 A/C; topological proper-action API | #32 D: smooth structure maps, source/target local diffeomorphisms, finite-action properness, and a coordinate-change specialization. Add a genuine cover refinement before claiming general presentation independence. |
| Effective reconstruction and atlas descent | Quotient API plus local linearization/lifting and smooth atlas/refinement interfaces | Adapt paper proof obligations with explicit effectiveness and morphism restrictions. Prove local stabilizer reconstruction and presentation comparison. No blanket equivalence of all smooth quotient maps with equivariant maps. Candidate later #32 work, not required by the first experiment. |
| Metric, connection and evolution | #39 realization bridge, chosen invariant geometric data and tangent action | #32 E / #34. Distinguish exact realization agreement, dynamical discretization, and floating-point error contracts as in the gyrovector note. |
| Internal comparisons | Conventional targets plus the specific constructed model, interpretation, tangent and descent results above | #36 owns #32 F. Its graph-language work (#38) is independent of conventional quotient implementation; graph soundness alone does not unblock synthetic orbifolds. |

Only the decoder integration requires the relevant #39 result. Only internal
comparisons require the relevant #36 model results. The initial conventional
slice has neither dependency. This ordering names mathematical prerequisites,
not an effort estimate or a promise that later rows fit one implementation.

[ikz]: https://arxiv.org/html/math/0501093v2

[catdg]: https://github.com/peabrainiac/lean-catdg/tree/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4
[license]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/LICENSE
[toolchain]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/lean-toolchain
[manifest]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/lake-manifest.json
[catdg-readme]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/README.md
[induced]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/Induced.lean
[constructions]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/Constructions.lean
[local]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/LocallyModelled.lean
[manifolds]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/Manifolds.lean
[mfld-embedding]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/MfldToDiffSp.lean
[tangent]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/TangentSpace.lean
[diffsp]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/DiffSp.lean
[smoothsp]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Diffeology/SmoothSp.lean
[sites]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Sites/CartSp.lean
[cohesion]: https://github.com/peabrainiac/lean-catdg/blob/1ee4a2614b033dd1b4aded95759eb31eb9b0fbf4/CatDG/Cohesive/CohesiveSite.lean
[ml-diff]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Diffeology/Basic.lean
[ml-action]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Action.lean
[ml-tangent]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/MFDeriv/Tangent.lean

## Implemented coordinate-change comparison

Issue #41 adds the following public modules on the existing dependency pins:

- `Applications/Diffeology/Constructions.lean`: induced and coinduced
  diffeologies, their smooth-map universal properties, and smooth quotient
  lifts and maps. Coinduction generates the image plots; it requires no
  surjectivity assumption. Quotient maps preserve identity and composition.
- `Applications/Diffeology/Manifolds.lean`: manifold plots, the equivalence
  between `ContMDiff` and `DSmooth` for finite-dimensional boundaryless
  sources, and equality of the D-topology with the manifold topology under
  those hypotheses. Open submanifolds carry the induced diffeology. The
  smoothness bridge adapts the safe CatDG chart argument cited above, with
  a shared local plot/section construction proving topology compatibility.
- `Applications/Orbifolds/Equivariant.lean`: equivariant functors between
  Mathlib action categories, groupoid equivalences for equivariant bijections
  and group isomorphisms, stabilizer isomorphisms, and quotient projection
  squares. This module has only algebraic hypotheses.
- `Applications/Orbifolds/SmoothComparison.lean`: smooth quotient equivalences
  constructed from ordinary manifold diffeomorphisms, and tangent
  intertwining proved by Mathlib's manifold chain rule. Smooth descent itself
  works for arbitrary diffeological spaces.
- `Applications/Orbifolds/QuarterTurn.lean`: the reusable C4 action on the
  open complex unit disk, its stabilizers and tangent action, and the change
  `(x,y) ↦ (2x,y)` to an ellipse. The tangent action is multiplication by
  `i^k` in the open-submanifold coordinates. Both open manifolds instantiate
  the smoothness and topology bridges.
- `Examples/OrbifoldComparison.lean`: trivial and ineffective actions,
  arrow-label preservation, smooth quotient maps in both directions, and
  composition through `RawMap` laws and `Squares.compose`.

The finite linear action is separate from #39's projective motions. The
comparison does not construct a proper étale atlas, a Morita equivalence,
or a diffeological tangent space. Its tangent theorems concern ordinary
manifold tangent maps before taking the orbit quotient. The C4 action on
`ℝ` that fixes every point has the usual real diffeology as its quotient,
while each stabilizer still has four elements.
