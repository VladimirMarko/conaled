# And installer checkpoint statement review (#135)

The target is actual pure `checkDecl` acceptance at verified mode, fuel 32,
empty pin list and the preserved equality environment. The result is exactly
`AndInstallation.andEnv`, including all constants and tables. No acceptance
premise, lookup-equivalence assumption, replacement handwritten graph family,
native oracle or new semantic assumption appears in the closed target.

| Claims | Statement review |
|---|---|
| `AcceptanceMeasurement` commands | Elaborated proofs and proof-producing normalizations enter synchronous checked declarations. Both commands reject sorry-bearing terms; current-module audit covers generated safe roots. Normal forms export original-expression equality, not just a computed default. |
| `AndInstallationTail.q_eq`, `ctorEnv_eq` | Identify the complete pass record and actual constructor insertion, without erasing state fields. |
| `idx_ok`, `pins` | Actual index-sort and recursor-pin operations; the singleton index-sort list is exactly `[[]]`. |
| `AndRecursorType.recCv_eq`, `inferred_eq`, `u_eq` | Freeze the first actual stream recursor and its actual fixed-fuel inference result; `infer_ok` proves it is a successful sort, so default extraction does not assume success. |
| `sort_ok`, `constant_ok`, `stream_ok` | Sort normalization uses the upstream fixed-fuel sort equation. All constant guards are proved; the singleton stream check invokes that checked constant. |
| `AndRecursorStages` equations | Actual class NF/constructor results, former types and prefix; each success equation establishes the normal form is successful, including values extracted by `getD`. The complete class and constructor records are retained. |
| `classConstOk_of_facts` | Explicit lookup, name, closure, universe, resolution, inference and sort premises assemble the existing operation. It asserts no environment well-formedness or semantic soundness. |
| `AndGeneratedType` equations | Infer and sort the generated type in the constructor environment, compare it to the actual stream type with verified fuel 32, and check its full constant record. Record/member/index guards precede actual `classRecTyOk` and list composition. |
| `AndGeneratedRules` equations | Exact `classFeR` output and actual `classRecsRulesOk`, including the generated rule telescope checks. The returned complete records are preserved. |
| `genRec_of_facts`, `rec_ok` | All generator stages and guards are premises of a generic Except composition, then discharged by concrete equations. The original nested bit, parameters, table, read state, classes, stream and former constants remain arguments. |
| `tail_of_facts`, `tail_ok` | Preserve constructor and recursor environment insertion equations and actual full projection-table check. |
| `block_of_facts`, `block_ok` | Retain uniqueness checks, actual raw-recursion flag and complete pass output. |
| `tables_ok`, `accepted` | Exact predicted records and table, followed by actual declaration dispatch; no weakening to agreement on selected names. |

The positivity root was audited before extending through this installer. Every
new formal module passes its current-module permitted-axiom audit. The checkpoint
uses inherited dependency outputs; the measured source hashes do not constitute
a fresh upstream/native closure receipt. Those checks and independent review
remain obligations of final #135 acceptance.

No claim here proves Exists installation, helper acceptance, canonical emitted
family acceptance, a model, or cached-checker acceptance. The latter is separately
owned by [#417](https://github.com/VladimirMarko/conaled/issues/417).
