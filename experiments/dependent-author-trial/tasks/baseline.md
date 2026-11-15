# Baseline source notation

Use namespace `DependentAuthorTrial.Baseline`. The public entry modules are
`SquareKit.Internal.PathTransport.Authoring` and
`SquareKit.Internal.DependentJudgments.Sigma.Stability`. Every local transitive
import in `public-manifest.json` is permitted. You may read their source and
Lean/Mathlib dependencies. The existing `NamedCaller` and `CongruenceCaller`
examples are disclosed public exposure; their tasks are not the held-out task.

The source API is `SquareKit.Internal.PathTransport.Typed`, with author commands
under `Typed.Authoring`. A raw context has a `CtxCode`, a raw family a `TyCode`,
a raw term a `TmCode`, and a simultaneous substitution a `SubCode`. Source
judgments retain those indices. Use the general APIs, not a specialization to
native equality.

For held-out inputs use arbitrary `hΓ : CtxDeriv Γ γ`, `hA : TyDeriv Γ γ A a`,
`hx : TmDeriv Γ γ A a x ξ`,
`hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T`,
`hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q`, and
`hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π`.
The two arbitrary source substitutions target `Ξ ++ pathCtx Γ A x`, then its
source context. All semantic annotations remain arbitrary indices consistent
with those source derivations; do not postulate extra equalities for the final
answer. The selected result is the generic J expression of your constructed
command. Its branch is the stated reflexivity recipe, with its required source
conversion.

For extension reuse, quantify over an arbitrary full `Typed.Model` and
`DependentJudgments.Sigma.Stable M.toStructuralModel`. The old source is
interpreted by that model's exact reduct, with the selected annotations checked
by the recursive interpreter. Source Sigma does not exist in this arm. Explain
that fact in the outcome and do not add a Sigma source constructor or claim to
have authored a Sigma term. The shared mathematical task is unchanged.
