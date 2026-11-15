# Actual emitted-family statement review (#135)

The final endpoint is `EmittedAcceptance.accepted`: the actual pure verified
checker at fuel 32, no Nat-operation pins, exact `EmittedEnvironment.declarations`
and exact `EmittedEnvironment.environment`. The preserved canonical family and
native helper translation are unchanged. And/Exists reviews remain in the prior
checkpoint directories; their scope is not silently extended by their old runs.

| Claims | Statement review |
|---|---|
| `fold_cons`, `fold_append` | Sequence actual Except fold successes with explicit start/intermediate/end states. No state projection or Boolean success is substituted. |
| Every `NativeHelperN.decl_eq`, `cv_eq`, `value_eq`, and definition `hint_eq` | Proof-producing normalizations identify the actual helper at index N, its full constant, body and original reducibility hint. The exact nine-element list equality later discharges the possibility of the fallback declaration. |
| Every helper `inferred_eq`, `u_eq`, `infer_ok`, `sort_ok` | Infer the declared type in the exact predecessor environment at verified fuel 32. `infer_ok` establishes that the normalized result is a successful sort; default extraction alone supplies no proof. |
| Every helper `valInferred_eq`, `valInfer_ok`, `equalResult_eq`, `equal_ok` | Infer the actual body, then check its type against the declared type in the same environment/mode/fuel. The success and true-result equations are explicit. |
| Every helper `constant_ok`, `value_ok`, `accepted` | Prove name, universe, closure, resolution, sort and value guards through the upstream fact assemblers, then the actual `checkDecl` transition. Helpers 0,6,7 remain definitions with original hints; the others remain theorems. Definition-name fast paths are explicitly excluded by checked guards. |
| `EmittedForwardAcceptance`, `EmittedBackwardAcceptance` claims | The same checked stages apply to the two actual `graphDeclarations`, not the older handwritten family. Their native z,x telescope and helper-bearing bodies are preserved. The backward step follows the accepted forward step. |
| `helper_list`, `helpers`, `graph_list`, `graph` | Equality of the full actual lists and their complete folds in dependency order. No selected-name-only claim replaces acceptance. |
| `environment_eq`, `accepted` | Full final environment equality includes records, order, stored body/hint fields for definitions, recursor metadata/rules and both projection tables. The final fold starts from Env.empty via the proved primitive stream. |
| `AcceptedEmission.model_exists`, `model` | Apply upstream pure soundness and model conversion to the closed acceptance theorem. `[SetTheory V]` stays explicit. Choice selects an existing model; it does not assert a new global axiom or SetTheory instance. |
| `source_comparison`, `emission_comparison` | Specialize the existing general source/formula/code translation results to that model and derive primitive laws from its records. Interpretation laws, encoding, assignment compatibility and denotation premises remain visible. The general theorem does not claim checker acceptance of arbitrary additional declarations. |
| `EmittedApplications.closed_graph` | Uses Model.mem through the existing actual-record `EmittedClosed.closedTruth`, with denotations built from the admitted formula interpretation. No hypothetical model/acceptance premise remains; carrier/function memberships and SetTheory remain. |
| `three_step` | Reuses the accepted graph comparison twice with a composed function whose Pi membership is proved. This tests semantic composition rather than defining another target interface. |
| Concrete examples | Natural-number graph specialization and native typing/denotation use the same producer declaration. They are checked theorems, distinct from relative models requiring SetTheory. |
| `wrong_parameters` | Actual Exists declaration with parameter count1 returns the explicit mismatch error in the real post-And environment. |
| `missing_tables` | The full accepted-family checker cannot return the final environment with tables deleted. This is an output-contract inequality, not an input rejection. |
| `wrongDirection_eq`, `direction_mismatch` | The actual forward body's inferred type fails verified fuel32 definitional equality against the actual backward statement. |
| Negative `badCv_eq`, `inferred_eq`, `u_eq`, `infer_ok`, `sort_ok`, `constant_ok` | The mutated declaration remains a well-formed constant in the forward predecessor environment; rejection is not caused by malformed headers or missing dependencies. |
| `thm_mismatch`, `value_rejected`, `wrong_direction` | Explicit successful guards and body inference followed by false type equality produce an actual theorem mismatch error. The final checkDecl rejection concerns the actual forward body under the backward type. |

`checked_normal_form` produces safe data definitions and kernel-checked equations
using cbv proof generation and checked declaration insertion; `measured_theorem`
also inserts checked proofs. Both reject sorry-bearing terms. Module audits reject
forbidden axioms. No unchecked evaluation is a theorem premise. Timing/size fields
retain their documented meanings; shared expression tree counts are not byte or
allocation measurements.

All new final modules passed their focused checks and permitted-axiom audits.
Those runs reuse prepared private upstream/native outputs. Fresh exhaustive
closure validation and independent final Standards, Spec and originator review
are separate obligations. The public runner and its audit controls are supplied
by the coordinator and reviewed separately.

Cached full-family acceptance remains unproved and owned by
[#417](https://github.com/VladimirMarko/conaled/issues/417). The pure-route model
result supplies no cached equation. No #107/#108 independent-author gate was
selected, repaired or bypassed.
