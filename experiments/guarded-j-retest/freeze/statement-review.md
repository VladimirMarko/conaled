# Repair statement review

The missing connection was already exhibited by the immutable #320 author and
reference: each instantiated the admitted root-tail rule manually. That source
is the pre-repair evidence; no artificial failing mathematical claim was needed.

| Declaration | Intended claim and checked connection |
|---|---|
| `Tm.rootTail` | Every admitted point and length-n telescope gives the root-tail substitution from the total pulled-back telescope to the original total. Quantifies over arbitrary n, including zero. Its derivation uses exactly the existing rule's two premises. |
| `Tm.reflexivitySub` | Reflexivity of a substituted section inhabits the substituted identity family after judgmental conversion. It takes only a section and valid substitution, not a requested equality. `identityBranch` also checks identity substitution explicitly. |
| `Command.reflexivity` | Selects J at `Id_Q(p,p)` with reflexivity of the root-pulled section as branch. `selected_recipe` checks the exact syntax; `calibration_recipe` independently compares it with the retained author recipe. |
| `twice`, `aligned`, `comparison` | Substitute the actual new command twice, derive the family alignment and term comparison from existing source laws. Θ, σ and τ are arbitrary but valid; the equality is judgmental, not object identity. |
| `dependentWeakening` | Applies `twice` to constructed weakenings whose second family depends on the first generic witness. The underlying inhabited three-binder case and native interpretation remain in the imported #320 cases. |
| `interpreted` | Interprets the aligned source judgment under satisfied source assumptions in an arbitrary full contextual model. Validity includes the selected source type and term. |
| `extensionSelected` | Reuses the existing Sigma theorem by the exact selected recipe, retaining both full substituted typing and equality of the selected evaluation under the reduct. No erased-only result substitutes for it. |

The calibration adds no axioms, source constructors or model assumptions. The
new facade removes the local raw-rule application from this repaired caller.
It does not measure what fresh authors will do. Model coherence, valid source
inputs and interpretation hypotheses remain unchanged. Host expression names
still require qualification inside their corresponding method namespaces;
compilation caught a `rootTail` name collision during preparation. Moving the
new method after existing methods resolves that collision without editing their
statements. A doc-comment placement error was also corrected. These are
preparation failures, not author observations.

The next trial must separate model-builder work, source obligations, host
encoding, preparation and author work. A repaired reference alone establishes
no author-effort improvement, causal productivity effect or human usability.
