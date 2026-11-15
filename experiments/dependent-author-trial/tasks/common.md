# Tasks and acceptance

Work in order: calibration, then held-out. Use a separate immutable checked
source for calibration before proceeding. The held-out task was selected after
the interface freeze. Existing source examples remain public calibration.
All declarations, helpers and the final combined submission use your arm's
namespace. Do not add mathematical assumptions to obtain success.

## Calibration

For an arbitrary admitted generalized J command and one typed substitution of
its base context, construct the source comparison between substituting its
selected result and freshly reconstructing the command's tail, motive and
branch. Retain source typing of the operands. Existing command APIs and worked
examples are permitted. Name the main comparison `calibration`; give separately
named operand derivations if your comparison does not package them.

## Held-out dependent argument

Let x:A in Γ. Let T be any finite dependent telescope over the based path
context of x. Write L for its total context, and r:R→L for the reflexive-root
map with the whole tail retained. Given p:Q in L, construct the selected
certificate

    eta = J(x,T, Id_Q(p,p), refl(p[r])) : Id_Q(p,p) in L.

The branch's type must be converted along identity substitution to
`Id_Q(p,p)[r]`. This specifies the actual selected J recipe and branch. Replacing
eta by reflexivity, by an arbitrary inhabitant, or by native Lean equality is
not accepted. Q and p may depend on the complete path and tail context. There
is no uniqueness-of-identity-proofs or equality-reflection premise.

Given arbitrary typed simultaneous substitutions σ:Δ→L and τ:Θ→Δ, construct
source typings of p[σ][τ] and eta[σ][τ]. Derive source equations comparing each
with substitution along σ∘τ. Derive the family equations for Q and
Id_Q(p,p) as well, and provide the twice-substituted certificate converted to
the composite-substitution family. Retain the selected certificate in all these
statements. Equality of endpoints alone is insufficient.

Instantiate your generic argument at these actual dependent substitutions:

    Δ = L.k:Id_Q(p,p),             σ = weakening
    Θ = Δ.h:Id_{Id_Q(p,p)[σ]}(k,k), τ = weakening.

The second added family depends on the first generic identity witness k.
Construct both substitutions from source context/family derivations and apply
your generic certificate comparison to them. Do not add their typing as new
hypotheses or replace either substitution with identity. The generic task still
quantifies over arbitrary σ and τ, not just these weakenings.

Interpret the value, its selected J certificate and the dependent type
alignment in every full contextual model supplied with the stable Sigma
capability. Source assumptions must be satisfied in that interpretation.
Retain the exact selected value and certificate after the extension. The old
Typed source uses that full model's exact reduct; the guarded source embeds
its typing derivations into the actual admitted Sigma theory and proves
validity there. A raw evaluation equality that also holds on invalid inputs
cannot replace typing/validity. No native-only proof may replace this general
interpretation claim.

## Required submission coverage

Use these names, or document an explicit mapping if your representation needs
several declarations for one item. Helpers are allowed, but they must use only
the frozen public interface and ordinary Lean/Mathlib.

| Declaration | Required content |
|---|---|
| `calibration` | One-step source substituted/fresh comparison and both source operands. |
| `certificateCommand` | The specified arbitrary-tail J command and its branch derivation. |
| `certificate` | Source typing of its exact selected J expression at Id_Q(p,p). |
| `valueTwice`, `certificateTwice` | Actual source derivations after both substitutions. |
| `valueTypeComparison`, `certificateTypeComparison` | Source family equations, preserving the dependent certificate family. |
| `valueComparison`, `certificateComparison` | Source selected-term equations with composite substitution. |
| `certificateAligned` | Twice-substituted certificate converted into the composite family. |
| `firstWeakening`, `witnessVariable`, `secondWeakening` | Constructed actual dependent substitutions and their retained generic witness. |
| `dependentWeakeningCertificate`, `dependentWeakeningComparison` | Checked uses of your generic derivations at those substitutions. |
| `valueValidity`, `certificateValidity` | Correct source interpretations of the selected value and certificate. Typed's checked interpreter equation is sufficient when its return type supplies the semantic section. |
| `certificateTypeValidity` | Interpretation of the dependent type alignment; it may follow by interpreting your source comparison. |
| `extensionSelected`, `extensionValue`, `extensionType` | Exact selected-data and family recovery in the stable extension's reduct. Typed may reuse the same checked interpreter equations with an explicit Stable parameter. |
| `extendedCertificate`, `extendedValidity` | Guarded arm's embedding into Sigma source theory and its interpretation under satisfied original assumptions. In Typed, explain the unchanged-reduct reuse and do not invent a source Sigma rule. |

The coordinator checks statements, hypotheses, recipe selection, source and
semantic conclusions, generic-to-instance connections and all named coverage.
Successful Lean exit alone is insufficient. Exact final source is replayed and
all its mathematical declarations receive the repository's transitive axiom
audit. Prohibited admissions remain failed evidence, never accepted proofs.

The constructor comparison has judgmental eta. This task tests reuse after the
actual extension, not authoring new Sigma terms or beta-only models. It makes
no higher-identity adoption claim. It is distinct from #108's separately gated
theorem. One fresh agent per arm provides observations of these interfaces for
this task, not causal productivity or human-usability evidence.
