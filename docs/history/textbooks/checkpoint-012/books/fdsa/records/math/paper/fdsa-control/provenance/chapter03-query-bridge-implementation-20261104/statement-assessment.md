# Bounded read-plan/read-all source statement assessment

Status: implementation author's exhaustive **source** assessment only. No Lean/Lake command, printed-type output, kernel pass, full check, axiom audit, or independent review is claimed. The accompanying 27/95 explicit-@ inputs use the existing six-option printer profile; root must execute and inspect them at the candidate. The private helper's generated internal name must be obtained from elaboration, not guessed.

## Quantifier domains and nonvacuity

All generic declarations quantify `n : Nat`, `α : Type u`, and `β : Type v` as present in their exact source headers; no positivity, injectivity, distinctness, order, decidable equality, or `Inhabited` premise is imposed. The supplied `compute : List α → β` is a fixed pure function. Because `[] : List α` always exists, supplying compute entails an output even if α is empty. An input at n=0 exists for any α; at n>0 the source statements apply to actual supplied inputs and do not invent an inhabitant of an empty α.

`readPlan` takes the plan, computation, and transcript only. The hidden input is used solely by the pre-existing `Runs.query` transition and by theorem specifications. The operation and its instantiation are fixed before the universally quantified input. This module supplies no input-indexed advice, answer oracle, or additional access mechanism. The eventual actual-selector instantiation must likewise use a fixed computation of observed values.

The private induction constructs an actual run for each prefix and remaining list. The public `readPlan_run` and `readAll_run` specialize this to empty history, so later run-conditional claims are accompanied by explicit witnesses. Arbitrary malformed histories are only covered by raw operation equations; no empty-history execution theorem assumes them reachable. Every-run theorems use the inherited `Runs.deterministic` on an actual constructed run.

The tariff `c : Nat` includes zero. These equalities count each query occurrence; a repeated coordinate is charged repeatedly. They establish no positive lower bound unless a separate positive-tariff premise is used. They charge acquisition only, not lookup, transcript operations, the pure final computation, physical time, or memory.

## Every new public declaration

Namespace below is `Applications.Selection.CoordinateQueries` for the first 16 entries and `Examples.CoordinateReadAll` for the remaining 11. Exact source binders and conclusions are retained in `source-statements.txt` and `declaration-inventory.json`.

| Declaration | Scope, premises, conclusion, and nonvacuity assessment |
| --- | --- |
| readPlan | All finite valid-coordinate plans, fixed pure compute; queries at transcript length or computes reversed recorded answers. No hidden-input argument. |
| readPlan_query | Arbitrary history and index; the explicit `some i` lookup premise implies a query decision. It is an operation law, not reachability. |
| readPlan_done | Arbitrary history; the explicit `none` lookup premise implies compute on recorded chronological answers. It is an operation law, not correctness for forged history. |
| readPlan_run | All plans/inputs/compute; constructs exact empty-history Runs, trace with every plan occurrence, and compute on observed values. No termination premise. |
| readPlan_total | All plans/compute; packages the preceding concrete execution for every input. |
| readPlan_run_iff | All trace/value candidates; forward follows deterministic agreement, reverse supplies actual execution at exact trace/output. |
| readPlan_length | Actual empty-history run; trace length equals plan length including duplicates; witnessed by readPlan_run. |
| readPlan_work | Actual run and all natural c; exact constant per-occurrence tariff c times plan length. |
| readAll | All n; fixes the plan to finRange n, independently of input. |
| readAll_run | Every input/compute; constructs exact ofFn observation trace and output compute(ofFn input), including n=0. |
| readAll_total | Every n/compute; packages actual readAll_run without a correctness or complexity premise. |
| readAll_run_iff | Every trace/value; actual run iff exact observed coordinate/value trace and exact final result. |
| readAll_coordinates | Actual run; projection to coordinates equals finRange n, hence the stated order/coverage even with duplicate payloads. |
| readAll_length | Actual run; exact n query occurrences, including zero. |
| readAll_work | Actual run, arbitrary natural c; exact c*n acquisition charge; no compute-cost bound. |
| readAll_correct | Arbitrary spec and a length-n correctness premise for compute; transfers that premise to observed values/output. It assumes the pure value specification and does not construct or measure selection. |
| empty_run | Any payload type and compute, explicit empty-coordinate input; actual run has no observations and returns compute []. |
| empty_every_run | Every terminating empty run and c; determinism gives empty trace, compute [], zero work. empty_run witnesses premise. |
| full_read_exists | Every input, n, compute and c; existential actual run jointly satisfies coordinates/output/length/tariff. No premise merely postulates a run. |
| full_read_every_run | Arbitrary actual full run and c; jointly exact trace/output/n/c*n; full_read_exists witnesses every input. |
| observed_sum | Natural payloads, all n/input and actual run; directly invokes the conditional correctness transfer with a proved reflexive sum specification. No selection claim. |
| concrete_full_read | Closed input [8,3,5]; actual three-coordinate run with chronological payloads [8,3,5] and output 16. Closed observation and sum identities use kernel `decide +kernel`. |
| duplicate_full_read | Closed input [4,4,4]; actual three-coordinate run and output 12. Duplicate values do not erase coordinate observations. |
| duplicate_every_charge | Every actual run for duplicate input; output 12, length 3, tariff 2 gives work 6. The preceding run witnesses it. |
| repeated_plan_run | All inputs Fin 2→α and fixed compute; plan [0,1,0] constructs three occurrences and computes [input0,input1,input0]. |
| repeated_plan_every_charge | Every actual repeated-plan run and c; exact repeated result, length 3, work c*3. No unique-coordinate reduction. |
| supplied_history_values | Closed equation on supplied history [(0,99),(1,7)] with exhausted [0,1] plan; returns chronological [7,99]. No Runs/reachability/correctness proposition is made. |

## Complete private-helper inventory

There is exactly one newly authored private declaration: `readPlan_run_from`, source-local in Applications.Selection.CoordinateQueries. It quantifies every actual input, fixed compute, arbitrary prefix and remaining plans. Initial history is *defined* by actual input answers for the prefix and reversed; it constructs the remaining chronological trace and final compute on prefix++remaining. Induction on remaining generalizes prefix; the step uses the successor prefix prefix++[i]. It does not assume an oracle or completion. No other private declarations are introduced by these two source files. The four preserved inherited files retain their existing two private helpers, for three authored private declarations across the query branch.

## Connected case coverage and exclusions

The design's independently expected n=0, arbitrary full read, concrete [8,3,5], duplicate [4,4,4], repeated [0,1,0], and malformed-history equation cases are all represented above. Both actual existence and every terminating run are connected to the same API. No malformed history is used to discharge an actual correctness theorem.

C03-083 remains open. This is preparation for the actual measured median-of-medians selector: acquisition will construct its list from observations; the actual selector must consume that list; its measured source-call count, recurrence proof and tariff relation must then be proved. No generic coversQueries premise, unrelated value-correct selector, assumed linear bound, recurrence import, or other author's source is included here. None of the 83 Chapter 3 obligations receives acceptance credit from this uncompiled handoff.

## Required root gates

Focus on Applications.Selection.CoordinateReadAll and Examples.CoordinateReadAll, then run the prepared explicit-@ inspection under the required native profile. Root owns all compilation, verification repairs, full check/audit, printed-type assessment, aggregate import integration when appropriate, independent Standards/Spec review, and immediate verification. Existing four modules are source-identical; earlier focused results are preserved but are not a pass for these two new modules. Toolchain, dependency pins, project options and aggregate files were not changed. Only Nix remains waived.
