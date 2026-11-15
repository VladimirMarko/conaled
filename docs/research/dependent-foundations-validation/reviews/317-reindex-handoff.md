# #317 source Sigma reindexing handoff

Owned files: `SquareKit/Internal/DependentJudgments/Sigma/Reindexing.lean` and `ReindexAuthoring.lean`. Released to the main implementer after the final focused build. No commits or tracker writes by this helper.

## Intended claims and statement review

The initial source theory admitted Capability operations and their comprehension-isomorphism laws but no constructor reindex equations. Its raw metavariable substitution theorem did not establish semantic reindexing of Sigma. The new same-signature theory is an axiom union, with explicit derivation inclusion `Reindexing.retain`; no syntax translation or additional semantic operation is introduced. `forget_model` recovers exactly the original Capability-only interpreter.

The new model-side assumptions are the existing `Stable.sigma_sub` and `Stable.pack_sub` laws. They apply to existing Sigma/pack operations. The source sigmaSub and packSub rules are validated by those laws. Source unpackSub uses derived inverse naturality. Source pairSub uses `Stable.pair_sub`; pairSecond uses the structural section-lift equality. Source splitSub follows from derived inverse naturality and structural substitution composition. branchType uses derived pack naturality to align the motive pullback. These consequences are admitted as semantically validated source rule schemas; they are not claimed to have been derived in the smaller Capability-only source theory.

Guard inversion retains `A : Family Γ`, `B : Family (Γ.A)`, arbitrary substitutions `σ : Δ → Γ`, and, for split, `C : Family (Γ.Σ(A,B))` and `d : Section (Γ.A.B) C[pack]`. The split claim is genuinely dependent: its motive varies over the sum context, and the reconstructed branch has type `C[sumLift][packNew]` by the explicit branchType judgment. The comparison from `Stable.sumMap` to the inherited source lift uses `familyComparison(sigma_sub.symm)`; semantic equality is not assumed to be definitional.

Judgmental equality of source expressions is distinguished from object identity. Full semantic eta remains part of the selected comprehension-isomorphism contract. No beta-only elimination claim or higher-model gate completion is asserted. No final client preservation equation is a model/caller field.

## Checked source uses

`splitReindexDerivation` is a source derivation fixed before choosing an interpretation. `Tm.reindexBranch` reconstructs the branch typing from the original typing and arbitrary σ. `Sub.sumLift` converts the source domain using the admitted formation equality.

`Tm.splitSubComp` composes two arbitrary base substitutions and rebuilds both families, the motive and the branch. Its proof consumes two applications of the public `Tm.splitSub` source theorem. `Tm.splitSubComposite` connects the same twice-rebuilt term to the composite source sum map using the inherited `Tm.subComp` rule. `Tm.pairSubComp` likewise consumes two `Tm.pairReindex` proofs, reconstructing dependent second-component typing using `Tm.pairSecond`.

These source proofs expose the intended interpretation-independent use. The main implementer owns concrete Native examples in `Examples/GuardedSigmaReindexing.lean`, including order-sensitive substitutions, and their subsequent validation.

## Validation

Final focused command (exit 0):

```
direnv exec . lake build SquareKit.Internal.DependentJudgments.Sigma.ReindexAuthoring
```

Log: `/tmp/conaled-314-320/reviews/317-reindex-build.log`. Both new modules compile; their new declarations produce no warnings. The output retains inherited import/module-system warnings. Full guarded candidate acceptance, exhaustive proof audit and regression fixtures remain with the main implementer after all helpers release.

A direct Lean call temporarily reported missing `Reindexing.olean` while the main agent's concurrent Lake build rebuilt its changed ancestors and this module. The main agent confirmed replacement output birth time and a successful explicit Reindexing build in its log. No output corruption or incorrect declaration was observed. The missing-output diagnostic is preserved as `317-reindex-missing-output.log`; compilation resumed after main paused all builds and ancestor edits. This helper then held exclusive focused-build ownership through release.
