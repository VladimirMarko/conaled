# Orbifold geometry: foundations and compositional implementation

Preliminary research, 2026-10-18. This note evaluates the
[imported chat and numerical probe](../history/orbifold/README.md). It proposes
work for the orbifold workstream; it adds no Lean definitions or proved
geometry. Repository terminology is recorded in [GLOSSARY.md](../../GLOSSARY.md).

Follow-up work is tracked in [#32: paper assessment and formalization](https://github.com/VladimirMarko/conaled/issues/32),
[#33: generalized gyrovector geometry](https://github.com/VladimirMarko/conaled/issues/33),
and [#34: long-term simulator](https://github.com/VladimirMarko/conaled/issues/34).

The [Myers assessment](myers-orbifold-assessment.md) delivers #32’s
assessment-only scope: versioned theorem correspondence, pinned-library gaps,
shared-architecture contracts, and the first disk-action formalization tasks.
It adds no Lean geometry or synthetic axioms.

## What to extract from Myers

David Jaz Myers' [paper, version 1](https://arxiv.org/html/2205.15887v1)
defines orbifolds as microlinear types with properly finite identification
types (Definition 1.1.2). Its foundations include cohesive HoTT, synthetic
differential geometry, and a Kock–Lawvere axiom for nilsquare infinitesimals
(§4.1). These are substantive assumptions, not notation for ordinary calculus.

The useful initial inventory is §2.3 (action quotients and their arrows),
§4.1 (tangent spaces and isotropy action), Theorem 5.4.9 (microlinearity of
crisp étale groupoids), and Theorem 6.3.7 (the Rezk completion of a crisp
ordinary proper étale pregroupoid is an orbifold). The latter depends on the
paper's synthetic compactness and finiteness arguments. “Properly finite”
must not silently become Lean `Fintype`: Remark 1.3.1 explains why its internal
meaning matters when isotropy changes. These sections specify a foundation
and comparison results; they do not supply a numerical simulator.
[Source: Myers, §§1.3, 2.3, 4.1, 5.4, 6.3](https://arxiv.org/html/2205.15887v1).

**Proposed route:** reformulate a selected classical fragment using explicit
group actions, groupoids, smooth maps and tangent bundles in Mathlib. Record
for each selected statement its original assumptions, classical replacement,
lost generality, and intended simulator use. Reserve an internal categorical
model of the synthetic theory for separate research unless this inventory
shows it is necessary.

This distinction follows from the foundations. Lean equality is a proposition
and its proofs are irrelevant; different symmetry arrows must therefore live
in explicit data, rather than distinct proofs of `x = x`.
[Lean reference: propositional equality](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/).
Likewise, in Mathlib's real field, `ε * ε = 0` forces `ε = 0`. Substituting that
type of infinitesimals into the proposed unique linear expansion would make
its slope undetermined. This is an elementary obstruction to using ordinary
`ℝ` as the paper's synthetic line, not an obstruction to modeling an internal
line in a suitable category. New synthetic axioms would also conflict with
the repository's [axiom audit policy](../adr/0010-composition-and-proof-audit.md).

## Retain symmetry arrows before taking observations

For an action of a group `G` on `X`, the proposed semantic starting point has
objects `x : X` and arrows from `x` to `y` labeled by elements `g` satisfying
`g • x = y`. Endomorphisms retain the stabilizer. Mathlib already implements
this as `CategoryTheory.ActionCategory`, with a groupoid instance for a group
action and `ActionCategory.stabilizerIsoEnd`.
[Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Action.lean).

A coarse orbit quotient answers whether two positions are equivalent. It
does not retain the individual arrows responsible for that equivalence. The
distinction is observable in the proposed quarter-turn disk example: the
origin has all four rotation symmetries, whereas a nonzero point has trivial
stabilizer. Make both cases checked specializations before abstracting the
presentation. Equivariant evolution should preserve arrows as well as
positions. A coarse rendering observation can then deliberately forget them.
This is a proposed specification, not a theorem supplied by the Python probe.

The chat's homogeneous framed model suggests a useful second slice: retain
a representative `g` of a left coset `Γ g` and apply prescribed body-frame
increments on the right. The elementary identity
`(γ * g) * h = γ * (g * h)` supplies the representative-independence obligation.
State-dependent controls need their own equivariance law. There is no proposed
multiplication of arbitrary left cosets. For general orbifolds, chart changes,
smoothness, presentation equivalence, and ineffective isotropy remain separate
requirements. The chat's general frame-space and Cartan-geometry claims need
a dedicated theorem-level review before they become library assumptions.
[Proposal provenance: response 2, §4](../history/orbifold/orbifold-simulator-chat.md).

## Existing Lean material to reuse

This is a bounded source inventory at the Mathlib revision in
[SOURCES.md](../SOURCES.md), not a claim that Mathlib contains a ready-made
orbifold library.

| Need | Inspected starting point | Remaining work |
|---|---|---|
| Action arrows and stabilizers | [Action.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Action.lean) | Smooth presentation and application-specific equivariance |
| Hyperbolic reference model | [UpperHalfPlane/MoebiusAction.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean), [Metric.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean), [ProperAction.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/UpperHalfPlane/ProperAction.lean) | Bridge the probe's disk coordinates and conventions; preserve action hypotheses |
| Smooth changes and tangent maps | [Diffeomorph.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/Diffeomorph.lean), [MFDeriv/Tangent.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/MFDeriv/Tangent.lean) | Identify exact support needed for connections, transport and flows |

No new version or dependency is required for this investigation. Inventorying
full proper étale groupoids, Morita equivalence, general connections and
certified integration remains part of the proposed work.

## Generalizations of gyrovector geometry

The recorded chat offers distinct candidates with different hypotheses.
Research should compare them on checked examples before selecting an interface.

* **Gyrogroups and gyrovector spaces.** The Isabelle AFP development by Marić
  and Marković formalizes abstract structures and two-dimensional complex
  Möbius/Einstein models, related to Poincaré and Klein geometry. It is a source
  of definitions and proof plans, not an imported Lean dependency.
  [AFP entry and theory links](https://isa-afp.org/entries/GyrovectorSpaces.html).
* **Geodesic local loops.** Kikkawa constructs local multiplication using a
  connection. Investigate the chat's expression
  `exp_x (P_(o→x) (log_o y))` with explicit neighborhood, path, and domain
  conditions. A local operation should not acquire global gyrogroup laws
  merely because its formula resembles gyroaddition.
  [Kikkawa, original paper](https://www.math.shimane-u.ac.jp/memoir/32/kikkawa2.pdf).
* **Matrix geometries.** Nguyen's affine-invariant positive-definite matrix
  construction includes `A ⊕ B = A^(1/2) B A^(1/2)` and `t ⊗ A = A^t`
  (the parameter `r = 1` case). Its definition of gyrovector space differs
  from other cited conventions. Compare axioms explicitly before combining
  this example with AFP's interface.
  [Nguyen, §§2–3](https://proceedings.neurips.cc/paper_files/paper/2022/file/a9ad92a81748a31ef6f2ef68d775da46-Paper-Conference.pdf).
* **Post-Lie integration.** Grong, Munthe-Kaas and Stava assume parallel
  curvature and torsion and include infinitesimal holonomy endomorphisms.
  Ordinary vector fields alone do not provide their non-flat construction.
  [Paper v2](https://arxiv.org/abs/2305.02688v2).
  Al-Kaabi and collaborators investigate general connections and the double
  exponential through a broader algebraic construction. Audit the carrier
  and operations before claiming it handles a chosen geometry.
  [Paper v1](https://arxiv.org/abs/2205.04381v1).
* **Framed Cartan development.** Treat the chat's move-and-turn calculus as
  a proposal connecting these ideas. It still needs connection-preserving
  chart changes, representative independence, integration domains and a
  treatment of ineffective isotropy. Neither a local loop nor a post-Lie
  algebra alone supplies orbifold descent.

Suggested examples are Euclidean translations, the framed hyperbolic disk,
and a positive-definite matrix geometry. A variable-curvature case should
expose where homogeneous formulas cease to apply. These are proposed research
tests; none has been formalized in this change.

## Fit with Felix and the current architecture

The comparison uses Felix revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, as required by
[architectural-quality.md](../agents/architectural-quality.md).
Its [comma objects and arrows](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda)
retain a connector and both square sides, with commutation in a chosen hom
equivalence. Its [projection homomorphisms](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda)
prove category preservation; additional structural homomorphisms are left
as a comment there. [MakeLawful.agda](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
transports category and Cartesian laws along structure-preserving maps using
induced equivalence. Cartesian-closed transport is marked TODO. These files
provide the compositional standard; they do not implement orbifold geometry.

The repository already separates `CategoryOps`, `HomEquiv`, congruence and
laws in [Category.lean](../../SquareKit/Category.lean). It supplies `RawMap`,
`MapLaws`, induced equivalence and law transport in
[CategoryMap.lean](../../SquareKit/CategoryMap.lean), and general squares in
[Comma.lean](../../SquareKit/Comma.lean), with a
[Mathlib comma comparison](../../SquareKit/CommaLawful.lean).
Use those constructions where their hypotheses match. A geometric groupoid
contains invertible arrows in explicit types; a `HomEquiv` alone does not
replace that data. General presentation equivalence may need functors,
natural isomorphisms or richer descent machinery beyond the existing square
interface.

Proposed boundaries are:

1. **Geometry and presentation:** action/groupoid data, isotropy, metric and
   connection hypotheses only where needed. Geometry-specific definitions
   would belong in `Applications/Orbifold/`.
2. **Exact transformations:** coordinate and matrix representations sharing
   an action semantics; prove composition preservation and representation
   changes. Exact [squares](../../Squares.lean) can express this layer.
3. **Approximate evolution:** a relation to exact states or trajectories,
   with an explicit error budget and validity domain. Reuse
   [RelSquare](../../SquareKit/Relations.lean) only after proving its local
   preservation obligations; its existence supplies no integration error
   theorem.
4. **Composition across domains:** state observations and input updates can
   eventually meet FRP contracts; smooth local calculations can use analytic
   AD. Existing [AD](../adr/0003-ad.md) does not differentiate arbitrary seam
   switches, and [interval arithmetic](../adr/0007-incremental-and-enclosure.md)
   does not already certify floating-point ODE integration. A checked bridge
   between independent implementations would belong in `Examples/`.

The first architectural test should quantify over composed motions and retain
isotropy, rather than prove only a single numerical example. Candidate checks
include identity/composition, changing representatives, the cone apex,
frame relabeling, and agreement of independently constructed coordinate and
matrix actions. The archive's matrices are projective complex matrices;
a Lorentz backend would be new work. A general simulator also needs a chosen
mechanical model, numerical guarantees and observation semantics. The current
probe establishes none of those contracts.
