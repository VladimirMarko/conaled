# #315 implementation handoff

Candidate: `bb77d67171e6cb610e43149394c8a9b9a0deab3f`. Clean committed tree; corrected candidate acceptance, all four audit regressions and immediate verification passed. Earlier f733 validation is retained below as history; the corrected-candidate section records current acceptance.
Fixed review base: `de2b1987e2f2caaad83ecddedb05c3ccded5bfff`, the approved integration containing #314, #319, #316 and #318. Earlier implementation began at approved #314 `3484ce523bf23524f715a3a2029c290a2d43c4c0`; merging the approved integration did not change the #315 task scope.
Worktree: `/tmp/conaled-314-320/315`; branch `experiment/dependent-judgments-315`.
Full spec: `/tmp/conaled-314-320/specs/315.json`; orchestration instructions and mathematical freeze remain applicable.

## Result and decision

Guarded operation syntax and source derivations have no whole-Model annotation indices. The actual full contextual interpreter proves every admitted guarded rule, with exact chosen J operation values. Source authors construct transport, value-dependent η, and apd_η with its transported source. They inherit both actual frozen substitutions and fresh reconstruction of selected certificates/actions, strict-map preservation, and the demonstrated concrete Type-family coherent comparison.

Proposed adoption is the guarded source boundary for subsequent #317/#320 experiments. Old Typed API retirement remains deferred pending checked translations/client replacement and exact selected-observation recovery. The separate higher-model interpretation gate remains unmet; native Eq and groupoid discrete Id fibers do not pass it. No #107 resumption or #108 theorem selection.

## Navigation for review

- `docs/research/dependent-judgment-freeze.md`: prospective mathematical fragment and author capability, approved before representation implementation.
- `docs/research/dependent-judgment-representation.md`: dated representation decision, failed section route, candidate comparison, exact interpretation/map/coherent scopes, ordinary-author work, extraction boundary and migration obligations.
- `SquareKit/FinitaryTerm.lean`, `CompositionalCoalgebra.lean`, `GuardedTheory.lean`, `GuardedTheory/Extension.lean`: reused finitary core, guarded derivations/soundness/substitution/partial maps, extension interface.
- `Internal/DependentJudgments/{Comprehension,ContextualOperations,StructuralRules,ContextualRules,Theory}.lean`: actual operation semantics and soundness of all admitted rules.
- `{Authoring,DerivedPaths,DerivedCertificates,DerivedReindexing,TransportReindexing,CertificateReindexing,DependentActionReindexing}.lean`: generated author operations and chosen-value substitution proofs. Additional shape/eta/pair/lift modules establish semantic structural lemmas, not new transport/certificate axioms.
- `Internal/PathTransport/InterpretationMaps.lean`, `{ComprehensionMaps,ContextualMaps,TypedMaps,MemoUniformity}.lean`: primitive strict map interface; derived pair/telescope/root/branch maps; preservation restricted to defined source expressions; typed hypothesis transport; inherited selected memo consequences.
- `{Memo,MemoNormalization,MemoReindexing,MemoFreshAction,FrozenContexts,FrozenMemo}.lean`: actual varying certificate section, normalization to direct η, fresh source comparisons, actual Γ/Δ/Θ and σ/τ, exact selected action/source under each/sequence/composite.
- `{NativeTypeModel,CoherentTypePresentations,NativeDerivedComparisons}.lean`: actual full native J, specified unequal dependent family and arbitrary telescope comparisons, selected transport/η/apd comparisons. EtaPresentation is output constructed with proofs, not caller assumption of a result.
- `{DerivedPathSemantics,DerivedGroupoidSemantics}.lean`: exact generic source-to-selected-J bridges and separately scoped path-sensitive groupoid comparison with old concatenation.
- `Examples/{DependentJudgments,GuardedContextualJudgments,CoherentGuardedJudgments,GuardedCommandComparisons,GuardedJudgmentBoundaries,GuardedInternalSetting,GuardedNativeMemo,GuardedGroupoidMemo}.lean`: retained cases described below.
- `GeneratedContexts.lean`: recursively derived empty substitution, without a uniqueness/terminality claim.

## Statement review and EDD

The first pairing case exposed actual dependency: A(n)=Fin(n+1), substitution n↦n+2, selected n, observed 3 in Fin 6. It consumes generated soundness rather than a separate arithmetic proof. The full-J case is arbitrary finite-tail, with branch over the motive pulled back along the complete reflexive root. The public fresh-command case has distinct raw constructors and a generated equality; its coherent finite specialization uses a nonidentity substitution.

The partial-map examples validate the negative boundaries: a noninjective full map collapses mismatched indices, turning malformed syntax valid, so unconditional raw preservation is refuted. Typed decoded families coincide in one valuation and separate as Empty/Unit in another, so soundness rejects reflection. Existing Bool symmetry rejects arbitrary classical selection.

The source memo carries the exact selected η and apd terms. Its higher identity type retains transport in K; it is not weakened to equality of untransported endpoints. Frozen context component equations retain p,p′,h,q,u; Γ→Δ→Θ means the substitutions have direction Δ→Γ and Θ→Δ. Generic derivations and semantics use this same order. Fresh action initially compared only pulled spelling; MemoFreshAction closes that intermediate limitation by comparing the actual varying family and chosen section.

Native coherent cases change context, family, total contexts, two dependent tail binders and motive; source selected 2 maps to some 1. Native memo has another dependent family, selected 3 maps to some 2, and actual varying η/apd comparison. The native final proof-equality steps explicitly use subsingleton native identities. The generic strict map/source results do not depend on those steps.

The groupoid generated memo has exact selected value/certificate/apd evaluation and the first-path observation 3 versus 2. Right-path J concatenation and old left-path J concatenation are identified only within the discrete-identity groupoid instance, not assumed definitionally equal in arbitrary or higher models.

The actual #319 dependent internal setting case supplies Fiber P and Fiber Q over Total P, with Q depending on the first generic value. Source recipes are authored before those semantics; context/type/term comparisons and both substitutions consume #319 theorems. Concrete payload 6 at 2 and reverse-order 2 versus 3 retain order sensitivity.

Raw tree factoring preserved old aliases and laws; existing CompositionalCoalgebra consumers were rebuilt. Interpretation is independent of derivation proof because evaluation reads only syntax. No initiality, arbitrary compatible-section extension, semantic-to-source extraction, higher-model realization, object Sigma or universal migration translator is claimed.

Helper statement reviews: `315-generated-recipes-statement-review.md`, `315-frozen-contexts-handoff.md`, and messages summarized here. Targeted axioms in `315-native-axioms.log` and `315-frozen-contexts-axioms.log` report only propext, Classical.choice, Quot.sound. This host classical footprint belongs to semantic representation and equality tests, not an object choice rule.

## Validation

Focused builds completed for source maps, coherent native model/J, negative boundaries, nested settings, generated memo/reindexing, exact semantic bridges, frozen contexts/memo, native memo and full groupoid memo (962 jobs). Groupoid final log: `315-guarded-groupoid-memo-build.log`; selected-axiom log: `315-guarded-groupoid-memo-axioms.log`.

The first full candidate at e928cf9 failed five existing simp-only proofs after shared bind factoring. Explicitly unfolding FinitaryTerm.bind repaired those proof steps without changing definitions or statements; focused old consumers passed 800 jobs. Retained failure: `315-e928cf9-candidate-failed.log`. The second full candidate d9d994e built individual modules but the aggregate entrypoint exposed a duplicate Model.j_heq from new maps and old ReindexCoherence. The original generic lemma is moved unchanged to ContextualModel and reused from both; the duplicate is deleted. Retained failure: `315-d9d994e-candidate-failed.log`. Both integrity guards reported zero invalidations, so these are source integration failures, not cache incidents. The aggregate regression then passed 10,112 jobs, including the exhaustive proof audit, at the final source tree (`315-aggregate-regression.log`). The committed candidate check and immediate verify both passed on `f733c24d26d67cfb4ca9a57f368bfd371b4d1a8f`.

Final acceptance commands ran under `flock /tmp/conaled-314-320/build.lock` in the private worktree:

- `direnv exec . ./check.sh --candidate HEAD`: PASS, 1,065 modules, 10,110 build jobs, exhaustive audit with exactly propext/Classical.choice/Quot.sound; 23.03 seconds. Pre-build integrity: 3,192 artifacts, zero invalidations. Post-build: zero inconsistent modules. Log `315-candidate-check.log`.
- `direnv exec . ./check.sh --verify-candidate HEAD`: PASS, matching incremental record. Log `315-verify-candidate.log`.
- Exact receipt retained as `315-verification.json` (copy of `.lake/verification.json`).
- Required proof-audit regression command `direnv exec . lake env python3 scripts/test-proof-audit.py`: all four fixtures PASS (`unused-external-axiom`, `private-transitive-axiom`, `private-admission`, `source-unsafe`). Log `315-audit-regressions.log`. Temporary fixtures cleaned up successfully; no source edits.
- Immediate verification repeated after fixtures: PASS, matching the same candidate and incremental receipt. Log `315-verify-after-fixtures.log`.
- Final `git status --short`: empty. No active helper writers or builds remain.

The final snapshot includes the source/runtime-free mathematical examples, source policy and public-entrypoint coverage. No tooling or dependency versions changed. Incremental acceptance is claimed; no fresh-mode acceptance is claimed. The two earlier failures and their corrected integration obligations remain in the logs above.

Independent Spec review of f733: PASS, zero findings. Standards identified sole P3 finding 315-STD-001; its correction and revised candidate are recorded below for reviewer reassessment. No push.

Final helper release: `Examples/GuardedGroupoidMemo.lean` SHA256 `ed917c1c5229f820466481d77283f2045df8112d9510639b93003f95095609f5`. Full generic certificateSection/dependentAction evaluation and each σ/τ/twice equation are retained, as is `dependentActionType_twice_eval`. The concrete `second_identity_is_reflexivity` explicitly records ordinary-groupoid truncation.

## Correction for 315-STD-001 and current acceptance

The sole Standards finding required the experimental API status in module documentation. Commit `bb77d67171e6cb610e43149394c8a9b9a0deab3f` changes only the module doc comment in `SquareKit/Internal/DependentJudgments/Theory.lean`, explicitly marking the interface experimental and linking the scope/migration report. No declarations, imports or proofs changed. Removing that module doc comment leaves byte-identical Lean commands between f733 and bb77; the link resolves. Exact evidence: `315-STD-001-delta.patch` and `315-STD-001-delta-check.log`. Finding status: correction implemented, awaiting independent reviewer disposition.

The fixed review base remains `de2b1987e2f2caaad83ecddedb05c3ccded5bfff`. Current validation, serialized by the shared flock:

- `direnv exec . ./check.sh --candidate HEAD`: PASS on bb77, all 1,065 modules, 10,110 build jobs, exhaustive audit using only propext/Classical.choice/Quot.sound. Total 69.81 seconds. Log `315-corrected-candidate-check.log`.
- `direnv exec . lake env python3 scripts/test-proof-audit.py`: all four fixtures PASS; temporary files cleaned up. Log `315-corrected-audit-regressions.log`.
- Immediate `direnv exec . ./check.sh --verify-candidate HEAD`: PASS, matching bb77 incremental record. Log `315-corrected-verify-candidate.log`.
- Exact current receipt: `315-corrected-verification.json`, copied from `.lake/verification.json`.
- Final `git status --short`: empty. No active builds or helper writes remain. No push.
