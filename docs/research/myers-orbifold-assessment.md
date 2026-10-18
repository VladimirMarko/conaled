# Myers orbifolds: correspondence and first Lean slice

Assessment for [issue #32](https://github.com/VladimirMarko/conaled/issues/32),
2026-10-18. This delivers the issue's assessment-only option. It adds no Lean
claims, axioms, dependency changes, or simulator. The selected source is
Myers, [*Orbifolds as microlinear types in synthetic differential cohesive
homotopy type theory*, arXiv:2205.15887v1][paper]. Numbering below refers to
that version. The [imported discussion](../history/orbifold/orbifold-simulator-chat.md),
Response 1 and Response 2's final section, supplies the motivation; its
[import annotations](../history/orbifold/README.md) and
[preliminary research](orbifold-geometry.md) separate proposals from evidence.

## Assessment

Start with explicit smooth group actions and their action groupoids in ordinary
Lean. Retain symmetry arrows, prove equivariance and tangent preservation, and
connect exact realizations through the existing square machinery. This yields
a classical fragment useful for compositional verified programs without first
constructing a model of differential cohesive HoTT.

This is a reformulation, not a translation of Myers' foundations. Native Lean
equality is proof-irrelevant; distinct stabilizer elements must be data in
arrow types. An ordinary orbit quotient discards those arrows. Ordinary `ℝ`
is reduced: `ε² = 0` implies `ε = 0`. Thus its nilsquare elements cannot supply
the paper's synthetic line with uniquely determined first-order coefficients.
An algebra of dual numbers can encode derivatives, but does not by itself
validate the paper's internal quantification over maps or cohesive modalities.
See the [Lean equality reference][lean-equality] and Myers §4.1.

## Theorem correspondence

The correspondence is published here as a proof-obligation inventory. Each
classical target below remains to be proved in this repository; the Mathlib
ingredients in the next section are already available upstream.

| Myers v1 reference | Source statement and foundational dependencies | Classical target and simulation use |
|---|---|---|
| Definition 1.1.2 | An orbifold is microlinear with properly finite identification types. Depends on the synthetic meanings described below. | Work with a smooth proper étale groupoid presentation. Keep the distinction between a presentation and an intrinsic orbifold. |
| Definition 2.3.1; Lemma 2.3.2; Corollary 2.3.3 | The action quotient is the dependent sum of a family over `BG`. Its identifications are pairs `(g, g • x = y)`; self-identifications give stabilizers. Uses higher identity types, dependent-pair identities and Lemma 2.2.5. | `ActionCategory G X`, its hom types and stabilizer/end correspondence. Supports relabeling and singular states. Restricts to ordinary groups acting on sets; does not construct the higher quotient. |
| Definition 4.1.8; Remark 4.1.10 | Tangents are pointed maps from the nilsquare infinitesimal object; isotropy acts by transport in this family. Depends on the synthetic line and identity elimination. | Derivatives of smooth action maps act between tangent fibers; stabilizers act on a fixed fiber. The action need not be faithful. Supports transformation of velocity/frame data. |
| Definition 4.2.12; Theorem 4.2.19 | Microlinearity tests infinitesimal pushout diagrams (Definition 4.2.11); it gives tangent spaces the module algebraic theory, including higher coherence where applicable. | Ordinary manifold tangent vector spaces and chain rule. No claim about arbitrary microlinear higher spaces or their infinitesimal lifting properties. |
| Definitions 5.4.3, 5.4.5, 5.4.6; Theorem 5.4.9 | Pregroupoids have invertible arrows and set-valued homs; completion is the essential image of Yoneda. Crisp étale groupoids are microlinear. Uses crystalline-modal étaleness and descent, not just a set quotient. | Smooth groupoids with source a local diffeomorphism; smooth descent is a separate target. An orbit set or a skeleton is not the asserted Rezk completion. |
| Definition 6.1.3; Remark 1.3.1 | Properly finite means subfinitely enumerable with decidable equality; internal finiteness would impose unwanted local constancy on isotropy. | Prove external stabilizers finite, using `Finite` or `Fintype` where appropriate. This changes the meaning: it does not model the internal property across generalized points. |
| Definition 6.3.6; Theorem 6.3.7 | The Rezk completion of a crisp ordinary proper étale pregroupoid is an orbifold. Object/arrow spaces are ordinary manifolds, source is crystalline-modal étale, and `(s,t)` is Dubuc–Penon proper. | Prove the selected classical presentation smooth, proper and étale. A comparison with the synthetic completion is still required to recover the source conclusion. |
| Theorem 6.4.1 | A microlinear set modulo a crisp finite group is an orbifold. | The finite smooth disk action is the first classical fragment. Prove its presentation and tangent laws, without calling it a Lean proof of the synthetic quotient theorem. |

All references were checked against [Myers v1][paper]. The foundational
budget matters: §§3.1 and 4.1 assume cohesive HoTT with higher identities,
crisp variables, and a synthetic smooth line. Axiom 3 includes the
Kock–Lawvere principle for Weil algebras, tiny infinitesimals and the Covering
Property. Axiom 4 concerns preservation of crisp pullbacks by the crystalline
modality; Axiom 5 supplies Dubuc–Penon compactness of the unit interval.
Crispness is a restriction on external parameters, not permission to replace
all internal propositions with classical ones.

The dependency chain for Theorem 5.4.9 uses microlinearity descent
(Theorem 4.3.13), étale descent (Theorem 5.4.7) and preservation of the needed
colimits (Theorem 5.4.8, via tiny infinitesimals and Appendix A). The stated
descent theorem has an inhabited-domain hypothesis; an empty presentation
needs separate treatment. Theorem 6.3.7 then uses discreteness of crystalline
subsets (Lemma 6.3.4) and proper finiteness of discrete Dubuc–Penon compact
subsets of ordinary manifolds (Lemma 6.2.21). Countable charts, the Covering
Property and interval compactness enter these arguments. Corollary 5.2.12
compares crystalline-modal étaleness with local diffeomorphisms for crisp
ordinary manifolds. A classical replacement must explicitly supply smooth
atlases and structure maps.

There is also a direct obstruction to copying the compactness definition.
Definition 6.2.1 uses `(∀ x, A ∨ B x) → (A ∨ ∀ x, B x)`. In classical logic,
splitting on `A` proves this for every type. Thus copying that formula into
classical Lean would not express topological compactness. This is our
deduction from the definition. The proposed route instead uses topological
properness; the change must remain visible in any later correspondence proof.

## What the two routes preserve

| Route | Preserves or can express | Changes or leaves unproved |
|---|---|---|
| Explicit classical presentations | Group elements as identification arrows; stabilizer groups including ineffective actions; smooth maps, derivatives and equivariant bundles; functorial evolution and explicit natural isomorphisms | Starts from presentations and ordinary analysis. Presentation independence needs smooth descent/Morita equivalence, not merely equality of orbit sets or equivalence of bare categories. It does not prove Myers' microlinearity or synthetic proper finiteness. |
| Internal model in Lean | Could interpret higher identity types, cohesive and infinitesimal modalities, the internal real line, microlinearity and the original statements with their hypotheses | Requires constructing a suitable higher categorical model, interpreting dependent types and universes, validating the modal and infinitesimal axioms, and proving soundness and a comparison with classical presentations. A sheaf category or a groupoid alone does not discharge these obligations. No such model is constructed here. |

In the second route, Lean would be the external metatheory. The internal real
line would be an object of the model, not Mathlib's field `ℝ`. Proving a model
satisfies the synthetic assumptions is different from declaring those assumptions
as Lean axioms. The latter would violate
[ADR 0010](../adr/0010-composition-and-proof-audit.md). Even with a model,
extracting executable coordinates, a metric, a connection and an integrator
would require separate comparison and refinement results. The assessment
therefore defers that route; it does not assert that constructing it is impossible.

## Pinned Mathlib inventory

The inspected checkout and `lake-manifest.json` both identify Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0). Links in this table
are pinned to that revision. These are reusable ingredients, not a claim of
an existing orbifold implementation.

| Need | Available construction | Interface or obligation still needed |
|---|---|---|
| Actions and identification arrows | [CategoryTheory/Action.lean][ml-action]: `actionAsFunctor`, `ActionCategory`, groupoid instance, `objEquiv`, `stabilizerIsoEnd`; `comp_hom` records the label order | Instantiate the disk action; prove the concrete stabilizer results. `stabilizerIsoEnd` is stated using the stabilizer submonoid and categorical endomorphisms; use the group structure for isotropy. |
| Equivariant operations | [GroupAction/Hom.lean][ml-hom]: `MulActionHom`, `MulActionSemiHom`, identity and composition | Construct the induced action-groupoid functor, with object and arrow preservation; add smoothness only when differentiating. |
| Coarse observation | [GroupAction/Defs.lean][ml-orbit]: `MulAction.orbitRel` and ordinary `Quotient` | Descend equivariant maps; document the deliberate loss of isotropy. This is not the paper's homotopy quotient. |
| Smooth presentations | [Diffeomorph.lean][ml-diffeo]: `Diffeomorph`, identity, inverse and composition | Assemble smooth object/arrow manifolds, source/target local diffeomorphisms, structure maps and their compatibility. An ordinary `Groupoid` supplies none of this topology. |
| Tangents and chain rule | [MFDeriv/Defs.lean][ml-tangent-defs]: `tangentMap`; [MFDeriv/Basic.lean][ml-chain]: `mfderiv_comp`, `tangentMap_comp` with differentiability hypotheses | Build the action on the tangent bundle and restrict it to each stabilizer's fiber; prove projection equivariance and derivative formulas. |
| Bundles and fields | [VectorBundle/Tangent.lean][ml-bundle], [ContMDiffSection.lean][ml-section]: tangent bundle and `ContMDiffSection` | Add equivariant bundle maps and sections; prove descent and compatibility with chosen presentation changes. A section of the ordinary bundle is not automatically an orbifold vector field. |
| Properness | [ProperAction/Basic.lean][ml-proper]: `ProperSMul` asserts properness of `(g,x) ↦ (g • x,x)` | Establish the finite disk action's properness, plus smooth étaleness. This topological property is not synthetic proper finiteness. |
| Hyperbolic comparison | [UpperHalfPlane/MoebiusAction.lean][ml-moebius], [Metric.lean][ml-metric], [ProperAction.lean][ml-hyperbolic-proper] | The upper-half-plane action and metric need a proved disk coordinate bridge, normalization and action conventions before transferring hyperbolic claims. |
| Later connections | [CovariantDerivative/Basic.lean][ml-connection]: `CovariantDerivative` and regularity classes | Prove invariance, path-dependent transport and descent for the chosen geometric data. The first slice does not require these. |
| Alternative smooth spaces | [Diffeology/Basic.lean][ml-diffeology]: diffeological spaces; its TODO points to external orbifold work | A diffeology on an orbit set still does not retain stabilizer arrows. No external package is adopted or claimed compatible here. |

A bounded search of `Mathlib/Geometry` and `Mathlib/CategoryTheory` for
`orbifold`, `Morita`, `LieGroupoid` and `EtaleGroupoid`, followed by inspection
of the files above, did not locate an assembled smooth proper étale groupoid
or its Morita/descent interface. The diffeology TODO is a research lead.
This records the boundary of this inventory, not a proof that every useful
component is absent elsewhere. Full stack semantics and an internal synthetic
model remain unimplemented in this repository.

## Reuse of the shared architecture

Compare Felix at the repository's pinned revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`:
[Comma/Type.agda][felix-comma] stores a connector, two arrows and a commuting
condition in a chosen hom equivalence; [Comma/Homomorphism.agda][felix-projections]
proves categorical preservation for its projections.
[MakeLawful.agda][felix-laws] transports category and Cartesian laws through
structure-preserving maps using induced equivalence. Its Cartesian-closed
transport remains TODO. These are the applicable architectural capabilities;
none of these files supplies orbifold geometry.

Use the existing [Category.lean](../../SquareKit/Category.lean)
`ofCategory`, `equality` and `ofCategoryLaws` on Mathlib's action
groupoid. Use [CategoryMap.lean](../../SquareKit/CategoryMap.lean)
`RawMap.ofFunctor` and `ofFunctor_laws` for the functor induced by an equivariant
map. This separates operations, semantic equivalence and preservation laws
without another geometry-specific category hierarchy. Arrow equivalence is
initially equality of the explicit arrows, retaining distinct group labels.
Inducing equivalence through a coarse observation would identify isotropy
arrows; that choice belongs only to the observation layer.

For a fixed group `G`, an equivariant `f : X → Y` induces `F_f` with object
map `f` and arrow map sending label `g` to the same label. The endpoint proof
uses `f (g • x) = g • f x`. Required laws are `F_id = id` and
`F_(h ∘ f) = F_h ∘ F_f`, on objects and arrows. Group-change maps can later use
`MulActionSemiHom` with an explicit group homomorphism. Arbitrary smooth maps
are not implicitly equivariant.

An exact realization with decoder `δ : R → X`, implementation `I : R → R`
and semantic operation `f : X → X` must prove `δ (I r) = f (δ r)` for every
`r`. Package that obligation with [Squares.Square](../../Squares.lean);
`Squares.compose` then handles arbitrary finite sequences of certified steps.
If `R` also carries the action, require equivariance of `δ` and `I` and retain
their induced functors as well. The pointwise square alone does not establish
arrow preservation. For exact coordinate changes, prove the corresponding
arrow diagram as well as the object square. General comparisons only up to
natural isomorphism require coherent components and naturality; the existing
[comma interface](../../SquareKit/Comma.lean) is not a substitute for a
bicategory of smooth presentations and descent.

For the first composition example, implement quarter-turns independently as
complex multiplication and real 2×2 matrices. Decode `(a,b)` to `a + b*i` and
prove agreement for every rotation word, every input in the disk, and every
identification label. Reuse the existing matrix operations rather than
introducing another matrix representation. Distinguish this planned theorem
from [Examples.MatrixStack](../../Examples/MatrixStack.lean), which already
synchronizes a different linear source fragment and does not prove this disk
bridge. A separate observation square uses `q : X → X/G` and the descended
`f̄`, with `q ∘ f = f̄ ∘ q`; pasting it gives coarse observations of the exact
realizations without replacing their groupoid semantics.

Approximate evolution would use [RelSquare](../../SquareKit/Relations.lean)
with a specified state relation, error budget and validity domain, after local
preservation has been proved. Existing AD can support derivatives of chosen
smooth coordinate formulas; existing interval arithmetic can support bounds.
Neither supplies an ODE discretization theorem or floating-point guarantee
for this workstream. Metric and connection assumptions belong with those
operations, not with the algebraic action-groupoid adapter.

## Selected first formalization slice and acceptance obligations

The selected slice is the quarter-turn action on the open disk
`D = {z : ℂ | ‖z‖ < 1}`, viewed first as a smooth real manifold. Use the cyclic
group of order four (for example `Multiplicative (ZMod 4)`) and the action
`ρ(k,z) = i^k z`, with a proved well-defined exponent convention modulo four.
This is the underlying action used by the hyperbolic disk example. A
hyperbolic metric and its isometry theorem are a later obligation, not a
consequence of defining `D`.

The following are proposed theorem statements and proof plans, not checked
Lean results from this assessment:

- Prove disk closure, identity and multiplication laws. Construct the existing
  `ActionCategory` instance. An arrow `x → y` carries a rotation label `k`
  with `ρ(k,x) = y`; composition first by `k`, then by `l`, has label `l*k`.
- At `0`, prove that every group element fixes the point and that its
  endomorphism group is isomorphic to `C₄`. Exhibit distinct identity and
  quarter-turn arrows. For every `z ≠ 0`, prove the stabilizer is trivial,
  using cancellation and the four distinct powers of `i`. Testing only a
  nonzero point would miss the required singular behavior.
- Prove each rotation smooth and its derivative `v ↦ i^k v` under the disk's
  tangent trivialization. At the origin the isotropy action on `T₀D ≃ ℂ`
  remains nontrivial. The tangent action is `(z,v) ↦ (i^k z,i^k v)`; it must
  preserve the tangent projection and composition by the chain rule.
- Construct functors for equivariant maps and prove their identity/composition
  laws. For an equivariant vector field `V`, state
  `V(ρ(k,z)) = Dρ(k)_z(V(z))`. At the origin this forces `V(0)=0`, since a
  quarter-turn has no nonzero fixed vector. This is a useful singular-point
  specialization, not a claim that all physical trajectories must stop there.
- Prove the complex/matrix decoder square and arrow compatibility for all
  rotation words, then compose with the orbit observation square. Include
  both the apex and a nonzero point. Rotation words exercise exact
  representation changes; they do not establish a physical motion algorithm.

A groupoid arrow relates descriptions of the same orbifold point. A physical
trajectory requires a time-indexed curve, dynamical law and, where relevant,
velocity/frame data; it can join different orbits. A coarse observation is
`q(z)` and forgets which identification was used. At the apex, four different
identification arrows have the same coarse observation. A lifted curve through
the apex is not ruled out by the vector-field specialization: arbitrary curves
and phase-space dynamics differ from an equivariant position-only vector
field. Frame changes must also transform velocity and controls; orbit classes
cannot be independently substituted into a binary displacement formula.

## Follow-up tasks

These are scoped work items for #32's next implementation and the parent
[#34](https://github.com/VladimirMarko/conaled/issues/34); they are not new
tracker issues created by this assessment. Gyrovector and displacement choices
remain with [#33](https://github.com/VladimirMarko/conaled/issues/33).

| Task | Depends on | Completion evidence |
|---|---|---|
| A. Action-groupoid adapter and disk isotropy | Existing Mathlib action API | Generic equivariant functor laws; `C₄` disk action; singular and regular stabilizer theorems. Geometry-specific modules belong in `Applications/Orbifold/`; shared adapters belong in `SquareKit/` only if reusable. |
| B. Exact realizations and observations | A | Complex/matrix agreement for all words and inputs, arrow preservation, pasted coarse observation square. Put the independent-realization composition in `Examples/`. |
| C. Tangent action and fields | A | Smoothness, chain rule, stabilizer representation, apex tangent action and invariant-field specialization. Bundle equivariance must be explicit. |
| D. Classical proper étale presentation | A, C | Smooth source/target local diffeomorphisms and proper `(s,t)` map for the finite action. Then design descent/presentation-change laws against a second presentation. Do not name this a Lean proof of Myers 6.3.7. |
| E. Hyperbolic and dynamical extension | B, C, plus #33's selected geometry | Proved disk/upper-half-plane bridge and metric normalization; chosen invariant geometric data, trajectory and frame semantics. Integration and numerical error require further tasks with explicit regularity and domain hypotheses. |
| F. Synthetic comparison research | The correspondence above; independent of A–C | Specify a model and prove its type-theoretic, cohesive and infinitesimal assumptions, then interpret the paper's theorem and compare with D. No axiom declarations standing in for these proofs. |

Each implementation task must use statement review and checked
specializations under [example-driven development](../../.agents/skills/example-driven-development/SKILL.md),
including the singular point and composition cases above. Register every new
module in the public import closure and run the normal `check.sh` source
recheck/proof audit; validate incrementally with `lake build` in the Nix shell.
No extra axioms are allowed. This assessment's validation is source and
correspondence review plus documentation checks; it does not report a Lean
build or the proposed examples as completed.

[paper]: https://arxiv.org/html/2205.15887v1
[lean-equality]: https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/
[ml-action]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Action.lean
[ml-hom]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/GroupTheory/GroupAction/Hom.lean
[ml-orbit]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/GroupTheory/GroupAction/Defs.lean
[ml-diffeo]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/Diffeomorph.lean
[ml-tangent-defs]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/MFDeriv/Defs.lean
[ml-chain]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean
[ml-bundle]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean
[ml-section]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/VectorBundle/ContMDiffSection.lean
[ml-proper]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Algebra/ProperAction/Basic.lean
[ml-moebius]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean
[ml-metric]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean
[ml-hyperbolic-proper]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/UpperHalfPlane/ProperAction.lean
[ml-connection]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean
[ml-diffeology]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Diffeology/Basic.lean
[felix-comma]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda
[felix-projections]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda
[felix-laws]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda
