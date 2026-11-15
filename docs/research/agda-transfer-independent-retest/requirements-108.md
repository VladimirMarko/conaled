## Current scheduling decision, 2026-11-09

The owner has resumed #107. Its pause allowed time to develop better abstractions/infrastructure and to investigate whether a future frontend could avoid hand-transcribing Agda proofs through a Lean DSL. Resume the bounded structural comparison using subsequent evidence; do not assume the old encoding is the final frontend or that a new surface automatically solves semantic obligations. Existing mathematical acceptance and the scope decision for a substantially wider redesign remain.

#108 still requires a reviewed #107 freeze, an unexposed author, a fresh theorem, a prospective budget and an archive before feedback. These are experimental safeguards, not a blanket freeze on related development.

#103 is split into #433 (technical smooth interpretation) and #434 (authoring-evidence and investment assessment). Technical work depends on actual missing constructions, not #102 closure or a favorable #108 outcome. Identify any specific required #107 operation before adding a dependency. #434 consumes #108's report, including a negative or inconclusive result, and may finish without a favorable result. Both obligations remain tracked under #103.

Ordinary scheduling preferences are priorities, not blockers. #117 protocol preparation can proceed while execution waits for suitable surfaces. #195 Phase 1 is available; only its Lean migration retains the interaction-contract prerequisite. #418 is eligible for scheduling as a bounded diagnostic task, without restarting a broad wave automatically.

This decision supersedes older pause and blanket smooth-entry language below. Historical experiment evidence and technical acceptance criteria remain intact.

Part of #102, under #100 toward #36. Follow-up to #106 and interface-repair #107. The user approved one bounded repair/retest iteration. This issue owns one new independent transfer experiment, its evaluation and the decision supplied to #103.

## Outcome

Test whether the repaired, frozen interface supports another extant Agda proof without exposing the bookkeeping that exhausted #106's author budget. A documented negative or inconclusive result is acceptable completion of the experiment. Success on one small theorem does not establish library-wide portability or a controlled productivity improvement.

The immutable prior baseline is `docs/research/agda-transfer-independent-baseline/` at `429c7cc`. Preserve it and keep framework repairs, assisted associativity work, this new baseline and evaluator work separate.

## Mandatory independence and phase boundaries

- Use a new author who has not implemented or reviewed the framework, either port, the repair, or the earlier baseline/evaluation. The previous independent author must not perform this retest. For agents, create a genuinely new session with `fork_turns="none"` or the platform equivalent; a context reset of an exposed implementer is insufficient. The orchestrator must not perform the proof itself.
- Supply only the task and exact reviewed frozen public handoff/source. Record launch provenance, commit, allowed and actual inputs. Public repository examples and pinned upstream sources are allowed; private conversations, scratch work, hidden helpers and implementer solution plans are not. Keep an isolated checkout and audit that the frozen API remains unchanged.
- After the repair is frozen, the independent author selects a different extant theorem whose declaration dependencies fit the supported fragment. Exclude `tr-concat`, `assoc`, renamed copies and reflexive restatements of those regression cases. Framework/repair authors must not select or pre-port the candidate. Record exact upstream revision/license/declaration, dependency closure, intended source conclusion and semantic applications before proof work. If no suitable candidate exists, report that outcome.
- Obtain a separate solution-free scope check, then freeze the candidate and protocol before constructing a Lean proof. The reviewer may assess scope and measurement but must supply no motive, proof plan, theorem-specific helper or tactic advice. The public upstream argument is an allowed author input.
- Use a prospective 40-cycle cap, retaining #106's definition of a cycle and categories; record logically grouped edits and every check separately. Include investigation, translation, helper writing, debugging and applications. Record a ten-cycle checkpoint without resetting the budget. Permit at most two full fresh validation invocations after a successful construction; corrections still count toward the cap. Stop earlier on success, a demonstrated unsupported requirement, contamination or user instruction. Do not extend the budget, weaken/switch the theorem, alter the API or seek coaching to force success.
- Archive the attempted caller, failures, exact diagnostics, commands, effort categories, statement review and report with hashes before any feedback, repair, direct-Lean comparison or assisted retry. Keep failed scratch outside the production import closure. Contaminated attempts cannot count: replace the author with an unexposed author and replace the theorem if a supplied solution leaked. Assisted retries remain separate and never replace the independent baseline.

## Evidence and evaluation

- Record declaration/proof-step correspondence and whether the Agda argument is preserved. A direct semantic theorem cannot substitute for a generated source derivation. A successful port must include applications of that same derivation through soundness, EDD/statement review, full fresh validation and exhaustive axiom audit at normal production limits.
- Identify unchanged reuse, proof-local helpers, remaining casts/substitution obligations and missing APIs. Separate repair cost from incremental author effort and evaluator work. Preserve failed commands and actual observable measurements. Cycle grouping and theorem difficulty limit comparisons with #106; do not turn counts, final line lengths or machine wait time into invented person-time or causal savings.
- An evaluator distinct from framework/repair implementers and the proof author checks provenance, frozen API, budget, archive and correctness claims. After archival, compare the ordinary direct-Lean result and the demonstrated versus prospective benefit of source reuse across models. Retain that comparison separately.
- Recommend continuing bounded selective porting, a further explicitly scoped interface experiment, or reconsidering the route. Explain uncertainty and whether the particular friction observed in #106 recurred. No automatic third repair/port cycle or broad library port follows.
- Preserve the new evidence in the repository, complete independent Standards/Spec review of the delivery and originator review where retained context permits, and commit the reviewed result. Publish the report on #102/#100 and record the resulting decision on #103. A positive evaluated result permits reconciling the implemented interface with #99 under #103's existing gate; a negative/inconclusive route change needs an explicit decision. Do not waive #103's smooth-model obligations or substitute a second source language.

## Completion gate

The distinct-author archived baseline and independent evaluation are mandatory. An assisted completion of assoc in the repair issue, a new session run by an already exposed author, a successful target proof alone or a narrative usability claim cannot close this issue. This scope authorizes one new theorem experiment and assessment, not ongoing implementation of #103 or an unbounded test campaign.

Blocked by: #107, including its reviewed frozen handoff.

## Coordination with later language experiments, approved 2026-10-25

The distinct-author protocol, prospective 40-cycle cap, archive-before-feedback requirement and #107 freeze prerequisite remain unchanged. New work in #115–#117 and #140/#141/#147 supplies public examples and design evidence, not a completed repair or an independent retest.

- At the reviewed freeze, record an inventory of public proof helpers, examples, corpus declarations and surface/checking capabilities available to the author. Identify material changes from #106's frozen interface, separating repair work from capabilities added by other developments. All allowed inputs must be pinned to the frozen snapshot or exact external revisions; no moving helper library may enter the attempt.
- Keep #115's declaration inspection, #116's translation corpus and #117's matched authoring benchmark separate from this test. Before proof construction, the solution-free scope check must establish that the selected candidate has not already been translated or equipped with theorem-specific preparation in those experiments or the repair work. The author still selects the candidate after the freeze. A named theorem on an exclusion list is not enough: inspect equivalent statements, prepared specializations and solution exposure without passing proof guidance to the author.
- Record the candidate author's participation and actual prior exposure to those related experiments. An author who has already attempted, reviewed or received a prepared solution for the selected candidate is not independent for it, even if the work occurred under another issue number. Existing broader role exclusions still apply. Public generic examples remain permitted inputs and must be declared; their existence alone is not contamination. Apply the existing author/candidate replacement rule when contamination is found.
- Evaluate success against the declared frozen fragment. A new ordinary target theorem, semantic route fixture, paper surface design or checked proof in another calculus does not substitute for the selected generated source derivation and its interpretation. Explain whether easier authoring came from reusable abstraction, added generic library capabilities or a changed mathematical task; do not infer causal savings merely by comparing completion with #106.

Do not add a general Agda importer, a completed slean/Agda-like surface or execution of #117 as a prerequisite. This remains one bounded independent test of the repaired identity-fragment interface. If the expanded public corpus leaves no suitable unprepared candidate, record that outcome under the existing protocol rather than weakening independence or starting an unbounded search/port campaign. #103 remains gated on the evaluated result.
