# Generated path recipes: source checkpoint and statement review

Scope: helper-owned source recipes and laws in the #315 worktree. This is an implementation handoff, not independent acceptance of #315.

## Construction and assumptions

`DerivedPaths` builds transport from the existing contextual J operation with an empty additional telescope. Its displayed family is arbitrary B over Γ.A. Concatenation specializes that transport to an identity family and eliminates the second path. `DerivedCertificates` builds a value-dependent composition certificate by a second J and builds dependent action by J. The latter explicitly compares transport of the source certificate with the target certificate. Neither certificate is an assumed equality, an endpoint-only replacement, or a primitive source operation.

Added guarded equations identify the structural path/root operations, empty-telescope shapes, substitution pairing, path-substitution pairing, and comprehension eta with their existing model definitions/laws. `Theory.rule_valid` proves them at every admitted Model; no Model field was added to assert a desired recipe theorem. Pair composition and eta use existing comprehension laws. `SourceCongruence.Equal.recipe` is induction on raw syntax and produces source derivations, not semantic equality reflection.

The source `Memo.Parameters` record contains schematic expressions and their source typing derivations, including arbitrary A over Γ and B over Γ.A. It does not quantify over semantic Models. Its certificate family and section are constructed by varying the first path. `Package` records a contextual pair of dependent source judgments; it does not add an object-language Sigma type.

## What the checked statements say

- `Tm.transportSub`, `Tm.concatSub`, `Tm.etaSub`: the selected generated recipes commute with an arbitrary typed object-context substitution. The eta result compares the selected J witness, not merely its endpoints.
- `Tm.apdSub`, `Tm.apdSourceSub`: dependent action and its transported source commute with object reindexing. The target uses the actual pulled-back section and family.
- `Memo.Parameters.value_atPath`, `compositeValue_atPath`, `fiber_atPath`, `certificateType_atPath`: selecting the generic path recovers the direct transport expressions and their dependent identity type.
- `Memo.Parameters.certificate_atPath`: selecting the generic path recovers the direct chosen eta recipe.
- `Memo.Parameters.transportedCertificate_atPath`, `dependentAction_normalized`: the source of dependent action remains transport in the constructed certificate family. Normalization does not replace it by the untransported certificate.
- `Memo.Parameters.value_reindex`, `compositeValue_reindex`, `certificate_reindex`, `fiber_reindex`, `certificateType_reindex`: reindexing the constructed memo agrees judgmentally with reconstructing it from reindexed parameters.
- `Memo.Parameters.dependentAction_reindex`, `dependentActionSource_reindex`: reindexing agrees with the recipe on the actual pulled-back certificate section/family. These statements do **not** yet identify that spelling with `(F.reindex hσ).dependentAction`; reports must retain that distinction.

All these are guarded source derivations. Raw metavariable substitution of a derivation is a separate operation and does not identify either frozen object-context assignment. `Memo`'s `_subComp` claims establish successive versus composite object substitution, but the concrete Γ/Δ/Θ, σ/τ, retained variable and assignment equations belong to the separately constructed `FrozenContexts` layer.

## Validation and remaining integration

`direnv exec . lake build SquareKit.Internal.DependentJudgments.MemoReindexing` passed 834 jobs. Direct `#print axioms` checks for rule soundness, transport/concat/eta/apd naturality, the selected memo normalizations and memo reindexing reported only `propext`, `Classical.choice`, and `Quot.sound`. The source modules contain no `sorry`, `admit`, or new Lean axioms. Build log: `/tmp/maps315-build.log`; audit script: `/tmp/Maps315Axioms.lean`.

The generic semantic bridges are separately checked by the semantic helper. The full generated groupoid integer-action observation, native coherent comparison, and concrete frozen object-substitution assignments are being integrated by their assigned owners. Those checks and the final independent reviews remain part of #315 completion.

Current third-checkpoint files: modified `Authoring.lean`, `DerivedReindexing.lean`, `Theory.lean`; new `ComprehensionEtaRule.lean`, `PathReindexRules.lean`, `SourceCongruence.lean`, `TransportReindexing.lean`, `CertificateReindexing.lean`, `DependentActionReindexing.lean`, `LiftFunctoriality.lean`, `MemoNormalization.lean`, `MemoReindexing.lean`.

## Fresh-action and frozen-assignment completion

The earlier fresh-action limitation is now discharged in `MemoFreshAction.lean`. `certificateSection_reindex` compares the actual selected eta sections under the lifted path substitution; `certificateFamily_reindex` compares the full value-dependent families. The proofs use lift composition, the lift/weakening square, and source identity-family substitution. They add no laws. `dependentAction_fresh` and `transportedCertificate_fresh` then compare with the freshly reconstructed `Parameters` expressions, including the transported source. The selected witness is preserved; no proof irrelevance or equality reflection identifies source certificates.

The new `FrozenMemo.lean` instantiates all seven composition equations at `Signature.sigma_typed` and `Signature.tau_typed`. It also checks reconstruction of the value, chosen certificate, dependent action and transported source at each assignment and through their sequence; dependent types and direct formulas are exposed alongside them. The underlying maps are the constructed context arrows in `FrozenContexts`, rather than assumptions supplied to the frozen result.

Validation: `MemoFreshAction` focused build passed 835 jobs; fresh-family, fresh-section, fresh-action and fresh-transported-source axiom checks reported only the standard three axioms above. Full `FrozenMemo.lean` direct Lean check passed. Its focused dependency build is coordinated with the owner of `FrozenContexts` because that source is still receiving component-assignment equations. Full candidate acceptance remains the main owner's responsibility.

Final helper checkpoint: the focused `FrozenMemo` build passed 837 jobs, rebuilding the completed `FrozenContexts` dependency and then the concrete memo specializations. Log `/tmp/maps315-frozen-build.log`. No source changes remain in progress from this helper.
