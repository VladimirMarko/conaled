# Direct author report

Completed H1 followed by H2 within the supplied budget. Both final submissions passed the mandated runner. No compiler sessions remain active from this attempt. No delegation, external sources, CLI, mutable author imports, added axioms, or sorry were used.

## Final files and retained attempts

- `SubmissionH1.lean`: final H1; passed its first full submission check (round 001).
- `SubmissionH2.lean`: final H2; passed its second full submission check (round 003).
- `SubmissionH2.attempt1.lean`: retained failed first H2 submission (round 002); not a final submission.
- `AUTHOR_REPORT.md`: this report.

The runner additionally retains exact source snapshots and diagnostics. Its state records three actual Lean feedback invocations total: one H1 check and two H2 checks. H1 first-attempt success: yes. H2 first-attempt success: no. These are measured check outcomes, pending independent replay and checklist review.

## Declaration-to-checklist mapping

Declarations in H1 are under `Tasks462.H1.Direct`.

1. `extension` proves the supplied map's extension condition. `fullTarget` invokes the native `selectedExtension` route. `full_code`, `full_witness`, `full_represents`, and `full_represents_none` establish the selected code, witness, universal target representation, and explicit omitted-input instance.
2. `not_surjective` refutes surjectivity by the missing `none` preimage.
3. `ImageDomain` and `imageTarget` use the native `selectedImage` route. `image_code` compares the projected selected code; `image_witness` compares witnesses. `image_represents` is quantified over the image subtype, and `image_excludes_none` states its restriction. No equality of input domains is claimed.
4. `true_fails` refutes the full proposed representation obligation by its instance at `false`.

Declarations in H2 are under `Tasks462.H2.Direct`.

1. `productHom` and `finalHom` package the supplied functions with checked zero and addition laws. `composedHom` composes through `Nat × Nat`; `composed_value` computes the composite.
2. `nativeExec` uses the supplied compiled seed and visit-charged transition. `productSeed`, `productStep`, and `productExec` have actual product-valued observations. `finalSeed`, `finalStep`, and `finalExec` reweight that intermediate execution. `product_transport` and `final_transport` apply `InterpretationAssistance.seeded_reweight` to each stage; `composed_transport` connects the original seed/bind/run to the final executor through both stages. `native_connection` identifies the original executor with the real compiled `total`.
3. `ordinary_result` and `original_counted_result` retain the native ordinary and counted compilation results. `native_result` connects those counts to the executor. `source_execution` states the native `Executes` relation for `addBody`, the evaluated seed and `total`, and exactly `xs.length` visits. `source_sum_visits` specializes the result to `xs.sum` and initial accumulator zero.
4. `product_result` computes the intermediate observation. `final_result` obtains `(xs.sum, 7*(1+2*xs.length))` from composition and execution transport. `empty_case` and `two_case` check `(0,7)` and `(3,35)` explicitly.
5. `shifted_not_zero` rejects the zero law. `shifted_no_certificate` refutes existence of an additive homomorphism with exactly this underlying function. This does not question the ordinary function's definability or rule out other resource interpretations.

## Sources and manual obligations

Read only the supplied task/setup and the permitted native source files: diagonal construction/coverage, recursive compilation, resource measured/fold/workload APIs, list-fold compiler, and interpretation assistance. Reused native declarations include `selectedExtension`, `selectedImage`, `total_compiled`, `total_counted`, `total_meaning`, `iterate_executes`, and `seeded_reweight`. The supplied recursive-compilation examples informed the source execution and real transition connections; no external public examples were consulted.

Manual work consisted of selecting and composing those APIs, supplying additive certificates, stating the full checklist obligations, establishing definitional connections to the supplied compilation, and proving the arithmetic and negative certificates. The counts describe modeled primitive and visit charges, not CPU time or runtime cost. Statement review checked that H1 retains the supplied functions and distinguishes the two domains, and H2 quantifies over arbitrary integer lists with the original compilation preserved before observation reweighting.

No generated applications or assistance CLI calls were used. All work was native Lean from the outset, so there was no change to a fallback route and no claim of assistance benefit.

## Diagnostics and remaining work

Round 002 reported one rewrite failure in `final_result`: the target displayed the defined `finalExec`, while `composed_transport` exposed its seed/bind/run expression. Adding a `change` statement to expose that definition repaired the proof; round 003 passed. This diagnostic was useful for a syntactic proof repair, not a change in mathematics.

Subjectively, the supplied native APIs made the mathematical obligations straightforward; this is an author impression rather than a measured comparative outcome. No unresolved checklist items are known. Independent replay and review remain the coordinator's responsibility.
