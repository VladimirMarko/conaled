# Candidate source notation

Use namespace `DependentAuthorTrial.Candidate`. The public entry modules are
`SquareKit.Internal.DependentJudgments.Templates`,
`SquareKit.Internal.DependentJudgments.Sigma.Authoring` and
`SquareKit.Internal.DependentJudgments.Sigma.Stability`. Every local transitive
import in `public-manifest.json` is permitted. You may read their source and
Lean/Mathlib dependencies. Existing command and constructor derivations in those
files are disclosed public exposure; the held-out composite task was selected
after their freeze.

The base source API is `SquareKit.Internal.DependentJudgments.Contextual`,
using `SquareKit.GuardedTheory` derivations. Contexts, families, terms and
substitutions are expressions with guarded source judgments. The generic
command interface retains its selected J recipe. Semantic validity uses the
same full contextual model class as the baseline.

For held-out inputs use arbitrary expressions Γ,A,x,T,Q,p, assumptions Ω,
`hx : Tm (Ω := Ω) Γ A x`,
`hT : Tel (Ω := Ω) n (path A x) T`, and
`hp : Tm (Ω := Ω) (total T) Q p`.
The arbitrary substitutions are `Sub (Ω := Ω) Δ (total T) σ` and
`Sub (Ω := Ω) Θ Δ τ`. Preserve these premises and derive the family information
they imply. Do not assume the final identity certificate or its comparison.
The J motive is `identity Q p p`, with reflexivity of the pulled-back p as its
branch and the required source type conversion.

For extension reuse, quantify over an arbitrary full `PathTransport.Typed.Model`,
`Sigma.Stable M.toStructuralModel`, a semantic assignment ρ and validity of the
original source assumptions Ω. Embed the actual source derivations into the
admitted Sigma theory and establish validity there. Preserve the exact selected
value, family and J certificate by the reduct interpretation. A raw evaluation
equality without validity under these assumptions is insufficient. The task
does not require authoring new Sigma terms.
