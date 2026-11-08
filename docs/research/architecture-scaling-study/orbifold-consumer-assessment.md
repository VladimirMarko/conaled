# Orbifold consumer requirements and source comparison

This assessment treats the supplied Agda checkpoint as external consumer
evidence for [#362](https://github.com/VladimirMarko/conaled/issues/362).
It supports a concrete ordinary-open arrow comparison and a later joint
interpretation test. It does not establish that conaled already interprets the
consumer's theorem, that its smooth foundations admit an unchanged constructive
port, or that every missing capability can be supplied by an adapter.

The consumer wants an end-to-end Agda formalization. Reuse means reconstructing
and checking mathematical constructions there. A Lean theorem is not an
unchecked premise in that deliverable. This requirement is explicit in the
supplied [comparison report](../../history/orbifold/agda-checkpoints/checkpoint-080/Conaled%20and%20semantic%20libraries%20for%20an%20Agda%20formalization.md)
and [research checkpoint](../../history/orbifold/agda-checkpoints/checkpoint-080/Orbifold%20semantic%20foundations%20research%20checkpoint.md).

## Evidence and validation boundary

The supplied audit pins conaled at
`5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`. This assessment inspected local
source at the assigned baseline
`700786fa2f691d6db196f388d69c2f12bc5d1afb`. Rehashing the audit's 42 listed
files with Python in `direnv exec .` found no mismatches. This establishes
identity of those files, including their listed formal sources. It does not
establish identity of every transitive dependency or certify a build.

The audit and its JSON are inside the preserved
[checkpoint archive](../../history/orbifold/agda-checkpoints/checkpoint-080/myers-orbifolds-agda-checkpoint-080.tar.gz),
at `myers-agda-checkpoint/formalization/research/semantics/CONALED-REUSE-080.md`
and `CONALED-REUSE-080.json`. Agda paths below are relative to the archive's
`myers-agda-checkpoint/formalization/` directory. This assessment read source;
it did not run Lean, Agda, or a transitive axiom audit. The checkpoint's native
acceptance receipts are supplied historical evidence, not new execution here.
The supplied report's failed Nix bootstrap concerns its own environment;
the local direnv shell worked for the source-hash comparison.

## What the consumer actually needs

The reduced theorem is
`Orbifolds.Intensional.DerivedAtlasOrbifold.Theory.Family.finite-branch-pushout-atlas-orbifold`
in `src/Orbifolds/Intensional/DerivedAtlasOrbifold.agda`. Its explicit inputs
include `BoundedTruncation`, `FunExt`, an effective atlas, sethood of the atlas
object, finite local branch charts, object-square comparisons, and four pointed
vertex liftings for each selected test. Its conclusion is `ReducedOrbifold`
relative to that test family. This is a useful reduction of the geometric
obligations, not a completed geometric instance.

Two details constrain any comparison architecture. `PointedPushoutTest`
contains a chosen boundary and its pushout universal property, but imposes no
Weil-algebra condition. That geometric meaning must be supplied by the
instance. `ObjectSquares` requires equivalence of the actual
`Test.mapping-comparison`, defined by postcomposition with the selected cocone.
An unrelated equivalence between the same endpoint types cannot replace it.
The proof's `comparison-computation` retains the cocone's gluing path, then
derives source locality by cancellation. Selected maps and witnesses are part
of the contract.

`src/Orbifolds/Intensional/BoundedTruncation.agda` sets `Code ℓ = lsuc ℓ` and
`Truth ℓ = lsuc (lsuc ℓ)`. Its truncation interface raises universes and supplies
elimination into propositions; it is not a declaration of arbitrary HIT
closure or resizing. Its existence as a record parameter does not constitute
an internal semantic universe. The separate full-foundation target also needs
its crisp principles: `src/Orbifolds/Crisp.agda` exposes crisp excluded middle
as a hypothesis type. Neither the reduced theorem's safe header nor removing
choice from geometric code proves the full original foundation constructive.

The requested external theorem additionally requires an actual proper étale
Lie groupoid, a formal quotient recovering the ordinary quotient stack on
ordinary probes, descent/refinement compatibility, and interpretation of the
exact admitted proof. Those requirements exceed finite stabilizers, a coarse
orbit set, or a direct proof of an external special case. The supplied research
checkpoint states these as completion requirements and separately leaves the
original full-model question open.

## Conaled constructions that survive source inspection

| Consumer requirement | Inspected construction | Scope that must be retained |
|---|---|---|
| Dependent substitution | [SplitSheaf](../../../SquareKit/SplitSheaf.lean), `subPresheafIso`, `tySub` | Reindexed total spaces obtain sheafhood through a pullback comparison; this is ordinary Type-valued sheaf semantics. |
| Dependent functions | [SplitFunctionSheaf](../../../SquareKit/SplitFunctionSheaf.lean), `diagramIso`, `piType` | The compatible-function presheaf is compared with a constructed sheaf and its total sheaf. Sheafhood is proved rather than demanded as the desired conclusion. |
| Soundness of source rules | [DependentFunctionSheafSoundness](../../../SquareKit/Internal/DependentFunctionSheafSoundness.lean), `beta_sound`, `eta_sound`, `dep_sound`, `func_sound` | These interpret the declared dependent-function fragment. They do not certify an arbitrary Agda proof or its whole import closure. |
| Actual infinitesimal calculus | [SmoothGeometricKL](../../../SquareKit/SmoothGeometricKL.lean), `kl`, `allParameters` | The isomorphism retains the original affine map and constructs its inverse. Unique natural affine coefficients hold for arbitrary sheaf parameters, for first-order dual numbers. |
| Ordinary smooth maps | [SmoothManifoldFullFaithfulness](../../../SquareKit/SmoothManifoldFullFaithfulness.lean), `homEquiv`, `interpret_reconstruct`, `reconstruct_comparison` | Full sheaf-arrow equality includes non-real stages. The models are finite-dimensional real boundaryless manifolds with the stated charted-space/manifold assumptions; the file does not require separation or countability. |
| Effective descent | [SheafTorsorDescent](../../../SquareKit/SheafTorsorDescent.lean), `compatible_isSheaf`, `torsor`, `mapEquiv`, `canonicalRecovery` | Compatible sections construct the descended family and torsor. Cover and descent data remain inputs; effectiveness is obtained from them. |
| Quotient arrows and descent | [SheafActionQuotientDescent](../../../SquareKit/SheafActionQuotientDescent.lean), `arrowEquiv`, `canonicalRecovery`, `Map.arrow_comp` | Torsors with equivariant maps retain objects, arrows and their composition. They are not merely orbit sets. |
| A higher observation | [CocycleHigherNonzero](../../../SquareKit/Internal/Cubical/CocycleHigherNonzero.lean), `secondIdentity_no_erasure` | An integer observation distinguishes the selected second identity from zero even through a third identity. This construction is separate from the smooth sheaf model. |

These are substantive reuse candidates. The supplied assessment is correct to
distinguish them from records that assume an entire desired model. Its
comparative ranking against every other semantic library is not independently
established by this focused audit. Nor does this table discharge the imported
analytic foundations, universe closure, or exact source-language interpretation.

The separation between higher and smooth semantics is a model-construction
gap. The existence of an ordinary sheaf model and a distinct higher model does
not supply a simultaneous instance. [LocalUniverses](../../../SquareKit/LocalUniverses.lean)
provides presentations and reindexing of split families; it does not establish
the consumer's object-language universe. The advertised
[cubical fragment](../cubical-model-construction.md) excludes internal universes,
Glue/univalence, HITs and cohesive geometry. This does not invalidate its bounded
higher result. It prevents treating the juxtaposition of module names as the
missing higher smooth interpretation.

## The missing inverse is precisely located

[SmoothConstantOrdinary](../../../SquareKit/SmoothConstantOrdinary.lean)
already proves `constantLabelRealEquiv` at the real point,
`ordinaryLabel_mul`, `ordinaryLabel_natural`, and
`ordinaryLabel_isLocallyConstant`. Its `ordinaryLocallyConstant` sends a section
of the sheafified constant group over an ordinary open to a locally constant
function on that open. The inspected file supplies no inverse for this
ordinary-open map. Its real-point equivalence must not be mistaken for that
stronger result, nor should this bounded observation become a whole-repository
absence claim.

[SheafActionQuotient.chartArrowEquiv](../../../SquareKit/SheafActionQuotient.lean)
already has both inverse laws. It identifies arrows between chart objects with
sheaf-valued labels satisfying `a.onMap g n = m`. Thus the missing step is the
ordinary-open section/label comparison, not an inverse to `chartArrowEquiv`.
The report's proposed fiber-cover construction is plausible: cover an ordinary
open by constant-label regions, refine by principal opens, glue constant
sections, and prove recovery by separatedness. Compatibility on overlaps and
coverage in the actual formal topology are obligations; pointwise agreement
alone is not a theorem that arbitrary sheaves are point-detected.

After constructing that inverse, compose the actual maps with manifold full
faithfulness and `chartArrowEquiv`. Prove that identities, composition and
restriction agree. The relation `m = a.onMap g n` uses inverse labels relative
to a conventional arrow from `m` to `n`. The existing
[quarter-turn module](../../../SquareKit/SmoothQuarterTurnQuotient.lean)
already distinguishes `origin_arrow_label_derivative` from
`origin_forward_label_derivative`; changing conventions without a comparison
would change an observable result. Extending from chart objects to arbitrary
torsors requires the descent construction and its arrow laws. An arbitrary
torsor need not have the global trivialization required by
`Object.chartOfTrivialization`.

## Constructive reconstruction needs declaration-level evidence

The source exhibits several different obligations. They should not be merged
into a host-language verdict.

* [SmoothQuotient](../../../SquareKit/SmoothQuotient.lean) defines a representative
  with `(Ideal.Quotient.mk_surjective q).choose` and builds finite-arity smooth
  operations from representatives. `ideal_stable` supplies independence.
  Finite quotient elimination is a plausible replacement, but has not been
  implemented here.
* [SmoothOpenDescent](../../../SquareKit/SmoothOpenDescent.lean) chooses
  representatives for an arbitrary cover-indexed family. A finite-arity repair
  does not discharge this simultaneous selection. Refinement by all witnesses
  would still require coverage, compatibility and descent proofs.
* [SheafTorsorLocal](../../../SquareKit/SheafTorsorLocal.lean) selects local group
  elements from unique solutions and uses uniqueness to prove compatibility.
  In a suitable constructive setting, eliminating truncated existence into a
  proved proposition of complete solutions can replace such selection. That
  needs the propositionhood, extensionality and size arguments, rather than a
  blanket choice principle.
* [SmoothOpenCover.Covers](../../../SquareKit/SmoothOpenCover.lean) uses negative
  nonzero values at real points. `ambient_cover` splits on a relation being
  nonzero. Replacing this by positive apartness changes the basis until the
  localization and comparison theorems are proved. The analytic gluing in
  [SmoothIdealArbitraryGluing](../../../SquareKit/SmoothIdealArbitraryGluing.lean)
  also uses a constructed locally finite smooth partition. Merely exposing a
  partition as input yields a conditional core, not an unchanged theorem for
  arbitrary covers.
* [SplitSheafPi](../../../SquareKit/SplitSheafPi.lean) uses proof irrelevance in
  composition of substitution transports. Replacing proof equality in an Agda
  set-valued layer needs its coherence evidence. Higher identities cannot be
  replaced by proof-irrelevant host equality without losing the consumer's
  isotropy.

An explicit-data interface is useful when it isolates these requirements and
the existing concrete specialization is recovered under its current
assumptions. Moving an unconstructed result into a field only relocates the
obligation. A transitive per-declaration axiom audit plus checked replacement
constructions is stronger evidence than searching for `classical` or
`noncomputable`. Neither keyword supplies that audit.

## A matched consumer test and architectural consequences

The first bounded comparison should use the existing C4 disk action and the
same ordinary-open arrow contract on both the direct and shared routes. The
research checkpoint initially proposes a sign action, then recommends reusing
conaled's stronger existing C4 example. Retain this evolution explicitly; the
two examples are different tests. An Agda implementation may choose an explicit
four-element group instead of conaled's roots of unity, but must prove the
action comparison before claiming a matched implementation.

The proposed test has the following acceptance contract:

1. Construct the ordinary-open inverse of `ordinaryLocallyConstant`, with both
   inverse laws and restriction compatibility for the actual forward map.
2. Obtain ordinary chart-arrow equivalences preserving action equations,
   identities, composition and label orientation. Exercise a disconnected open
   with different component labels so a constant-only shortcut cannot pass.
3. Retain four origin automorphisms and the nonzero stabilizer result from
   `origin_arrow_count` and `nonzero_arrow_identity`. Include the existing
   ineffective action as a check that the chosen representation does not erase
   arrows merely because their action on points is equal.
4. Compare descent after an explicit open-cover refinement, on objects and
   arrows. Retain the nontrivial clutching torsor from
   [SmoothTorsors](../../../Examples/SmoothTorsors.lean) so a global-chart-only
   implementation cannot satisfy the test.
5. Separately construct actual properness of the anchor and étaleness of the
   finite-action groupoid. A finite union of closed graphs gives a proof route
   for compact-preimage properness when its topological hypotheses are proved.
   Finite stabilizers alone do not establish that property.

Steps 1–4 test reuse of existing mathematics and expose comparison laws missing
from a usable specialization. Step 5 adds external geometry. None interprets
the exact Agda source proof. A later interpretation test must also instantiate
the selected four-vertex test family, bounded truncation, identities and
substitution in one smooth setting, with the required universe bounds. The
first-order arc comparison in
[SmoothQuotientArcs](../../../SquareKit/SmoothQuotientArcs.lean) is useful input;
it does not instantiate every proposed Weil square.

For #362, this consumer changes the evaluation criteria in three ways. First,
comparison interfaces must retain designated maps and coherence, not just
equivalence of endpoint objects. Second, constructing the joint model and its
logical dependencies is part of reuse cost; syntax adapters cannot remove it.
Third, successful specialized geometry must survive any shared-interface
revision, including nontrivial torsors, higher observations and the existing
derivative convention. Measure direct and shared author work on the same frozen
contract, with preparation and missing infrastructure recorded separately.
This supplied audit is demand evidence for that trial, not an independent
successful author trial or a measured architectural scaling result.

The source supports a bounded comparison project now and a separate joint
model research obligation. It does not justify either abandoning conaled's
constructed geometry or declaring the full Myers interpretation complete.
