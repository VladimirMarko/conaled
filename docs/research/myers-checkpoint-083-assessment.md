# Checkpoint 083 feedback against the reviewed conaled batch

The feedback supports retaining conaled's constructed smooth geometry and
selected-map comparisons. Its first proposed improvement, the two-sided
ordinary locally constant comparison, has already landed in the reviewed
batch. The quotient-arrow recommendation is implemented for the disk action
on ordinary domains, with generic label laws and canonical cover-recovery
controls. General manifold-base descent comparison and external properness
remain separate work. The constructive feedback justifies a small
explicit-data and dependency audit, not a claim that Lean makes the
mathematics intrinsically classical or a decision to rebuild the library.

This assessment compares the external audit's revision
[`5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`](https://github.com/VladimirMarko/conaled/tree/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff)
with reviewed revision
[`3c24a1cea327036be137313a6beb326a27354ec5`](https://github.com/VladimirMarko/conaled/tree/3c24a1cea327036be137313a6beb326a27354ec5).
It is a source assessment. It performs no fresh Agda replay, constructive
port, properness proof, or investigation of the external author's Myers
model question. Repository acceptance records for the reviewed batch are
separate from this assessment.

## Evidence and checkpoint scope

The [supplied chat response](../history/orbifold/agda-checkpoints/checkpoint-083/myers-orbifolds-agda-checkpoint-083-chat-response.md)
and [preserved checkpoint 083](../history/orbifold/agda-checkpoints/checkpoint-083/README.md)
are primary evidence for what its author reports. The archive's `formalization/CHECKPOINT-083.md`,
`research/semantics/CONALED-REUSE-080.md`,
`LIBRARY-COMPARISON-080.md`, `CONSTRUCTIVITY-NOTES-080.txt`, and
`ANALYSIS-LIBRARIES-083.md` give the detailed comparison and constructive
addendum. Paths in this paragraph are relative to the preserved checkpoint's
`formalization/` directory except for `CHECKPOINT-083.md`.

The checkpoint declares a fresh ordinary aggregate of 63 modules and a
retained, source-matched 539-module Cubical receipt, totaling 602 disjoint
project modules. It explicitly does not claim a fresh Cubical aggregate.
Those are the archive's verification claims, not checks replayed by this
assessment. Payload/hash validation establishes artifact identity; it does
not replay Agda or validate mathematical scope. The external conaled audit
was also source-only: its Nix bootstrap failed before a Lean build.

Inspection of the five new ordinary modules supports the narrower semantic
account in the checkpoint:

- `CoverRefinement.agda` supplies `SelectedCoverRefinements`, including a
  small selected family, universal image coverage, and `PreservedPullback`
  with a target universal property. These data remain inputs.
- `SheafRestriction.agda` proves `compatible-unique`, makes complete
  compatible values the proposition-valued membership of `good`, and uses
  sheaf gluing to construct `restriction-is-sheaf`. This avoids selecting a
  factorization for each target arrow; it does not construct the selected
  site data from nothing.
- `SheafAdjunction.agda` constructs `adjunction`, the actual `counit`, and
  canonical terminal/product comparisons. `FullyFaithfulBase.counit-is-iso`
  and `extension-fully-faithful` require a fully faithful base functor.
  This is not an equivalence of entire sheaf categories.
- `ContractibleSheafConstants.agda` constructs `constant-sheaf` only at a
  contractible small carrier, its local universal property and evaluation
  counit. `SheafObstructionInstance.agda` uses genuine sheaf nullity and
  the actual exponential constant map and counit. Its
  `ForEmbedding.ForCounterexample.real-flat-contradiction` remains
  conditional on the specified sites, cover lifting, line certificates and
  counterexample sheaf. General sheafification, a general constant-sheaf
  functor and the exact source interpretation are not supplied.

These constructions strengthen the case for explicit inputs, unique outputs
and comparisons of designated maps. They do not combine conaled's smooth
sheaves with its higher cocycle model, or decide the original model question.
The external Agda implementation remains independently owned.

## Which geometric recommendations are already implemented

The following declarations were inspected at the reviewed revision, rather
than inferred from the feedback's older source inventory.

| Recommendation | Current evidence | Disposition |
|---|---|---|
| Invert ordinary locally constant labels | `SmoothOpenSite.ordinaryLocallyConstantEquiv` in [SmoothConstantComparison](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/SquareKit/SmoothConstantComparison.lean) has forward map `ordinaryLocallyConstant`, inverse `ofOrdinaryLocallyConstant`, and both `Equiv` inverse laws. | Accept; already implemented by #363. |
| Preserve restriction and group operations | `ordinaryLocallyConstantEquiv_natural`, `ofOrdinaryLocallyConstant_natural`, and `ordinaryLocallyConstantEquiv_mul` cover every admitted ordinary smooth map and arbitrary small group. `ordinary_empty_section_unique` handles empty domains. | Accept; reuse these declarations. Multiplication preservation is a theorem on the equivalence, not a separately bundled `MulEquiv`. |
| Identify actual quotient chart arrows | `SmoothOrdinaryQuotient.diskChartArrowEquiv` in [SmoothOrdinaryQuotient](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/SquareKit/SmoothOrdinaryQuotient.lean) identifies arrows for every pair of ordinary maps into the disk with locally constant C4 labels satisfying the action equation. | Implemented for this action and these bases. General manifold-base comparison remains open. |
| Preserve actual arrow operations | `ordinaryArrowLabel_ident`, `_comp`, `_inverse`, `_reindex` are generic in the group and action. The disk equivalence exports `_ident`, `_comp`, `_inverse`, and `_restriction`. | Accept; already implemented. Generic composition prevents C4 commutativity from concealing label-order errors. |
| Compare descent and refinement | `Descent.recoveryComparison`, `_commutes`, `recoveryArrowComparison`, `_commutes`, and `recoveryComparison_natural` in [SmoothOrdinaryCoverRecovery](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/SquareKit/SmoothOrdinaryCoverRecovery.lean). | Partial: actual canonical recovery comparisons exist; a general change-of-cover functor on independently supplied descent data and its coherence are not constructed here. |

The equation is `diskMap (k x) (n x) = m x` for an arrow from the chart of
`m` to the chart of `n`. Labels `k` then `l` compose as `k * l`.
A conventional forward action arrow uses the inverse label. These are
mathematical orientation choices, not interchangeable notations.
[SheafActionQuotientLabels](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/SquareKit/SheafActionQuotientLabels.lean)
contains the underlying all-stage laws.

The controls test more than constant labels. In
[Examples/SmoothOrdinaryComparison](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/Examples/SmoothOrdinaryComparison.lean),
`signLabel_inverse` identifies the independently defined sign label's inverse
with the existing clutching transition; `varyingOriginArrow_labels` and
`varyingOriginArrow_not_constant` retain different labels on disconnected
components. `empty_inverse_unique` checks the empty base.
`signRefinement_restriction` compares actual restriction functors;
`signRefinementRecovery_commutes` and `signRefinement_arrows_square` compare
canonical recovery and its arrows along the named split refinement.
`nontrivialRecovered_not_chart` preserves a torsor with no global section.
That torsor's doubled-origin sheaf base is not asserted to be an ordinary
manifold or a global chart.

[Examples/SmoothOrdinaryIsotropy](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/Examples/SmoothOrdinaryIsotropy.lean)
adds `ordinary_origin_count` (four arrows), `ordinary_regular_identity`, and
`ordinary_ineffective_distinct`. `ordinary_forward_label` and
`ordinary_forward_derivative` preserve the inverse convention.
`manifold_arrow_recovers` compares the selected manifold realization with
the same embedded ordinary arrow through the principal isomorphisms. It
does not extend the chart-arrow equivalence to every manifold base. The
[ordinary comparison report](ordinary-open-quotient-comparison.md) records
these boundaries and the original acceptance scope.

## Constructive extraction: accept a bounded audit

The newly implemented inverse still uses `labelDefining`, which calls
`openDefining` for an arbitrary open label fiber, and
`ofOrdinaryLocallyConstant`, which selects the unique glued section through
`sheaf_exists_unique`. `ordinaryLabel_injective` selects local refinement
witnesses. These are inspectable implementation choices. They do not prove
that the corresponding mathematical comparison requires arbitrary choice.

Start an audit with this one operation and its immediate dependencies.
Record each declaration's pinned source, transitive Lean axiom report, supplied
data, selector, independence/uniqueness theorem, and proposed replacement.
Separate a construction from supplied principal fiber descriptions and
compatible labels from the wrapper obtaining those descriptions. Preserve
the existing public equivalence and examples as the classical specialization.
The audit must say whether it establishes only a refactoring or also a
constructive theorem in a specified metatheory. The normal proof audit allows
`Classical.choice`, `propext`, and `Quot.sound`; passing it does not certify
constructivity. See [ProofAudit](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/ProofAudit.lean).

Keep four distinct obligations in that report:

1. Finite-arity quotient elimination may replace the representative function
   in [SmoothQuotient](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/SquareKit/SmoothQuotient.lean).
   This is a candidate construction, not a completed port.
2. Unique-output gluing can avoid arbitrary selection when the entire solution
   type is proved proposition-valued with the required universe bounds.
   That proof differs from choosing representatives over an arbitrary cover.
3. A basis with positive apartness/invertibility data differs from negative
   nonzero. Its localization, coverage and comparison with the existing site
   need proofs; changing the predicate alone changes the model.
4. Arbitrary-open defining functions and partitions of unity are analytic
   existence results. Removing a quotient selector does not supply them.
   [SmoothOrdinaryPullbackCover](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/SquareKit/SmoothOrdinaryPullbackCover.lean)
   and [SmoothIdealArbitraryGluing](https://github.com/VladimirMarko/conaled/blob/3c24a1cea327036be137313a6beb326a27354ec5/SquareKit/SmoothIdealArbitraryGluing.lean)
   expose these dependencies.

Proof irrelevance, extensionality, quotient principles and excluded middle
need separate entries. Neither the presence nor absence of `classical` or
`noncomputable` is a declaration-level dependency result. No such full audit
was performed for this assessment.

## Architectural direction and #358–#361

The checkpoint reinforces the [reviewed synthesis](architecture-scaling-study/results.md):
retain independently specified contracts, prove the local laws needed by a
consumer, and preserve the selected maps and values. Admission of constructors
in a model remains additional work. Successful interfaces do not manufacture
a joint higher smooth model or an exact source interpreter.

The feedback changes none of the completed experiments' contracts:

- **#358:** The [scaling trial](dependent-operation-scaling.md) completed both
  author routes at three cumulative scales and repair, with exact snapshot
  replays and separate audits. Both routes reused general laws. The feedback
  supplies another concrete reuse case, not evidence of an asymptotic
  productivity advantage or a reason to mandate the shared interface.
- **#359:** The [higher shared-meaning client](higher-shared-meaning-client.md)
  retains actual target syntax, two substitutions, the dependent tail and
  the selected higher observation. It is a bounded noncomputable realization;
  ordinary geometric descent does not replace its Id/J obligations or turn
  it into a higher smooth model.
- **#360:** The [owned-handle comparison](operational-owned-handle-modes.md)
  keeps independent local protocol and separating-frame contracts. Crisp or
  geometric modalities do not establish resource ownership safety.
- **#361:** The [varying-certificate client](varying-selected-certificates.md)
  uses existing strict solution transport through two non-surjective changes.
  Unique sheaf gluing is not a substitute for selected partial computation.
  The result supplies no reason for a second external transport interface;
  checked internal SDT infrastructure remains separate.

Keep alternative traditions available under their own hypotheses. The
checkpoint's comparison identifies HoTTLean/SynthLean and Brunerie–de Boer as
references for exact interpretation and substitution; BiSikkel and Xu's
ContinuityType for dependent presheaf/sheaf constructions; and cubical
classifier work for universe construction. These are the supplied report's
bounded findings, not a fresh survey or a claim that any provides our smooth
instance. Local-universe presentations are not automatically object-language
universe classifiers. Sound interpretation of the required source is the
nearer target; full initiality asks for more.

The constructive-analysis addendum similarly reports actual agda-unimath
arithmetic/completeness and interval calculus at revision
`75518656f287c203b41cb7f71df46e02b987a084`, TypeTopology cut/limit and modulus
patterns at `dcbc42467539c862370776339911d1b424f80379`, and Cubical 0.9
localization and algebraic-sheaf techniques at
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. Its inventories explicitly retain
foundational/equality adapters and missing multivariable smooth-site work.
Use those records for the external constructive reconstruction; this task
does not re-audit those libraries or select a new conaled foundation.

The [disposition ledger](architecture-scaling-study/disposition.md) also keeps
nominal binding, higher-order probability, institutions/theory publication,
bialgebraic interaction, corelations, resource/separation and SDT distinct.
The geometry feedback does not supersede their capture, correlation,
interaction, ownership or partiality tests. No alternative should be judged
solely by whether it fits the incumbent interface.

## Bounded follow-ups and existing issue updates

These recommendations use the existing issue ownership and the open-issue
inventory inspected on 2026-11-08. They are not tracker writes or claims that
broad parent issues are complete. #32 already includes the proper étale
presentation bridge among its candidate targets; retain that coverage rather
than treating properness as a newly discovered programme.

| Owner | Recommended update and acceptance boundary |
|---|---|
| #363, with #100/#36 consuming its result | Record that the ordinary inverse and its laws are implemented. Link the designated arrow and canonical refinement controls. Do not reopen the same inverse target under a new name. |
| #100/#36 | Retain the stronger general refinement/Čech comparison only when an independently supplied descent-data consumer requires it. Specify its actual functor, arrow action, inverse comparison and coherence; extend ordinary chart comparison to manifold bases through atlas gluing if that is the selected next consumer. |
| #36/#100, coordinated with #290 | Scope the explicit-data/selector audit above around `ordinaryLocallyConstantEquiv`; publish per-declaration evidence and the classical specialization. Stop before a global constructive rewrite. |
| #32/#100 | Retain a concrete C4 external presentation target: object and arrow manifolds, source/target local diffeomorphisms, the actual anchor `(g,x) ↦ (x,g • x)`, compact-preimage properness under a named convention, and comparison retaining quotient arrows/descent. Reuse existing action, stabilizer and derivative results. Finite stabilizers do not prove properness; internal properness and external properness require their own comparison. |
| #289/#290 and #36/#100 | Keep exact source interpretation/substitution and joint constructor/universe admission visible. Selected higher witnesses, ordinary sheaf operations and local presentations do not jointly discharge them. Do not duplicate the external Myers model investigation. |
| #235 and #358–#361 records | Add this assessment as updated consumer evidence, preserving the reviewed outcomes and limitations above. No new scaling or ownership trial follows merely from receipt of the checkpoint. |

A short follow-up prompt for the external author:

> Compare checkpoint 083's ordinary sheaf requirements with conaled revision
> `3c24a1cea327036be137313a6beb326a27354ec5`. Inspect
> `SmoothConstantComparison`, `SmoothOrdinaryQuotient`,
> `SmoothOrdinaryCoverRecovery`, and their ordinary comparison/isotropy
> examples. Check the actual forward maps, inverse laws, restriction,
> multiplication, arrow composition/inversion, inverse-label convention and
> canonical descent recovery. Separate satisfied requirements from general
> manifold-base/Čech comparison and properness still needed. Identify one
> bounded explicit-data extraction that would aid your Agda reconstruction,
> without treating Lean's classical wrappers as necessity results. Report
> exact declarations and assumptions; distinguish source inspection from
> fresh compilation. Do not expand this request into a new Myers model
> investigation or a port.
