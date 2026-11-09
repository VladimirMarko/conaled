# Finite-action presentation requested by the Agda consumer

The external Agda agent's [2026-11-09 feedback](../history/orbifold/conaled-feedback-2026-11-09.txt)
asks for a generic finite-action proper étale presentation, extracted from the
existing quarter-turn disk construction. This is a concrete consumer request for
reusable geometry. It does not require a joint higher/cohesive model first.

## Evidence and provenance

The feedback is preserved byte-for-byte. Its SHA-256 is
`17039eef7c2729f6aeb59026bdc9146f34fd600127d6bbf5e19ac011915fbce1`.
It reviews `cce531c116d10d93306a40a7178de0361df09bec`, against the earlier
`d7debd4e0d510a1a5f8d18513a1fb80e69e51410`. The author explicitly reports source
inspection, not a fresh build or transitive axiom audit. Its embedded links and
mathematical claims remain attributed to that report.

This response inspects local source at `7ef2aaaddde72a10d735f844d599602598e031f9`.
The changes since the feedback's reviewed revision are documentation and
scheduling changes, not new Lean implementations. The initial assessment did not rebuild Lean or replay Agda. The later
[checkpoint 096-10 verification](myers-properness-096-10-verification.md) now
records a fresh targeted Agda check and statement review of the properness
claims. It does not establish whole-checkpoint acceptance.

## What is available for extraction

A repository-wide Lean search for the proper-map and local-diffeomorphism
predicates found the concrete orbifold construction in
[`DiskPresentation.lean`](../../Applications/Orbifolds/DiskPresentation.lean),
not a generic finite-action theorem. In namespace
`Orbifolds.QuarterTurn.DiskPresentation`, `sourceChart`, `rotation`,
`targetChart`, `source_etale`, `target_etale` and `anchor_proper` construct the
geometric evidence. `unit_smooth`, `inverse_smooth`, `compose_smooth`,
`composableEquiv` and `homEquiv` supply the structure-map and arrow comparisons.

The `anchor_proper` proof reduces properness of the anchor to properness of
projection from the compact label factor using `isProperMap_of_comp_of_t2`.
The Hausdorff intermediate space in that application is the object product,
not the arrow space. Compactness is required of the label factor, not the disk.
The generic extraction should expose these dependencies separately.

Reuse the existing action-groupoid representation in
[`Equivariant.lean`](../../Applications/Orbifolds/Equivariant.lean) and retain
[`SmoothDiskPresentation.lean`](../../SquareKit/SmoothDiskPresentation.lean)'s
`ForwardLabel` laws and disk-specific `smoothChartEquiv`. General manifold-base
quotient-arrow comparison remains outside this bounded extraction.

There is a test distinction worth preserving. In
[`Examples/DiskPresentation.lean`](../../Examples/DiskPresentation.lean),
`ineffective_control` combines disk anchor properness with distinct arrows in
a separate ineffective sheaf action. It does not prove properness of that
action's manifold presentation. `noncommutative_order` tests the generic label
comparison rather than a generic manifold presentation. Keep both tests and
add direct specializations of the new construction. A proposed trivial `S3`
action on the real line would exercise a noncompact manifold, ineffective
labels and noncommuting geometric composition together. The trivial-group
real-line specialization would expose the external diagonal test separately.
These are proposed tests, not new checked results.

## Consequences for the work queue

1. Prioritize one bounded finite-action extraction as a proposed successor under
   #32/#100, coordinated by #235. Its acceptance should follow sections 1 and 3
   of the supplied feedback: explicit finite group data, action by supplied
   diffeomorphisms, constructed structure maps, local diffeomorphisms and exact
   Mathlib `IsProperMap`, with the disk as a retained specialization. The
   signature must state the actual manifold, topology and smoothness hypotheses.
   Compactness of the manifold and effectiveness of the action must not become
   hidden requirements. The approved extraction is now [#435](https://github.com/VladimirMarko/conaled/issues/435);
   it has not been implemented as part of this verification task.
2. Keep #426's TwoFamily experiment. The feedback independently requests the same
   all-cell diagram and rejecting controls; no duplicate ticket is needed.
3. Keep #427's genuinely weakly stable model comparison. The external author
   recognizes the implemented Type-family constructions and the finite-set
   paper calculation, while explicitly distinguishing them from a higher model
   or an internal universe. Implementing the finite-set eliminator could be a
   useful regression, but this feedback does not establish its priority over
   the requested finite-action geometry or #427's model question.
4. Feed the source-to-model boundaries into #428's consumer-path assessment and
   #433's smooth interpretation. Neither monodromy nor the smooth transport
   checkpoint supplies all the Agda orbifold source requirements. The new
   finite-action target is useful independently of those larger comparisons.
5. Keep #107's resumed authoring repair and #429's effort assessment distinct
   from external adoption. This consumer intends to use our results as precise
   mathematical references and independently check its Agda construction.
   That is a real use, but not an automated Lean-to-Agda transfer or evidence of
   improved author productivity.

## Properness is a comparison obligation

The existing external construction exports Mathlib `IsProperMap`. The feedback
reports an internal predicate quantifying over varying proposition-valued
subtypes, and conditional Agda theorems connecting its diagonal case to decidable
equality. Those are different specifications. The reported obstruction concerns
a bridge preserving the relevant ring and diagonal while identifying those
predicates under the stated synthetic hypotheses. It is not a claim that every
formulation of Myers's foundations lacks a model.

The requested generic theorem must retain the external predicate. A finite-action
restriction alone does not justify the internal comparison: the trivial-group
action includes the real-line diagonal test highlighted by the external agent.
Any future comparison proposal must state its quantifiers, universe levels and
restriction policy and address that test. A different internal predicate would
change the specification and must be identified explicitly.

We have independently checked the supplied properness module and its import
closure; see the later verification report for exact hypotheses and receipts.
The external agent retains responsibility for its broader development. No new
conaled internal-properness formalization or general model nonexistence result
is claimed here.

## Declaration-level answer to the optional higher questions

The following are inspected implementation entry points, not a fresh proof audit.
Paths are relative to the repository root.

| Question | Existing evidence and boundary |
|---|---|
| Which judgments are interpreted? | `SquareKit/Internal/PathTransport/Typed.lean` defines `CtxDeriv`, `TelDeriv`, `TyDeriv`, `TmDeriv`, substitutions and their equality judgments. The type grammar includes the parameterized base, fiber, identity and substitution; `TmDeriv.pathInduction` carries a finite dependent tail, motive and branch. This is the supported generated fragment, not arbitrary Cubical Agda. |
| Where are actual term interpretations? | The same module's `interpretCtxChecked`, `interpretTyChecked`, `interpretTmChecked` and `interpretSubChecked` construct interpretations, with public `interpret*_agrees` comparisons. See also the explicit `jCode`, `TmDeriv.reflexiveJ` and `TmEqDeriv.contextualBeta` entry points. |
| Does the higher model supply J or assume it? | `TwoFamilyFullModel.lean` constructs `HigherInterpretation.fullModel` using `rootContraction` and `rootContraction_square`. `TwoFamilyModelFromContractions.lean` fills `j`, `j_beta` and `j_sub` using `SourceContraction.eliminate`, `eliminate_beta` and `eliminate_reindex`. Its auxiliary constructor takes contractions, but `fullModel` supplies constructed providers. |
| Where is Sigma stability? | `TwoFamilyFullModel.fullSigma` supplies the separate `DependentJudgments.Sigma.Stable` capability through `sigmaStable`. `TwoFamilySigmaStable.lean` provides `sigmaFormation_reindex` and the pack comparison. This does not by itself extend `Typed.TyDeriv` with every Agda Sigma judgment. |
| Are higher reindexing cells retained? | `TwoFamilyHigherReindex.lean` provides `reindex_whiskerLeft`, `reindex_whiskerRight`, `reindexHigher` and `reindexHigher_projection`, retaining the higher comparison rather than just object maps. |
| Is there one inspected model combining this with the smooth site, all required crisp/modal rules and internal universe closure? | These entry points do not construct that joint model. #419–#422, #426/#427, #428 and #433 retain different outstanding obligations; their individual results must not be reported as a completed joint interpretation. |
| Is the requested properness comparison established? | This assessment identifies no theorem connecting the unrestricted internal predicate reported in the feedback with the external `IsProperMap` result. The predicates must remain separate until an applicable comparison is constructed. |

The original feedback includes the primary-source references and its full
acceptance proposal. Preserve its distinction between constructive interface
data and the transitive classical dependencies of the surrounding Lean proof.
