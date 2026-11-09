# A prospective total-effort trial for dependent conversion

Protocol for [#429](https://github.com/VladimirMarko/conaled/issues/429), based
on local source at `a95a5ef`. No trial has run and no productivity result is
claimed. This prepares a bounded pilot around #423's optional converter. It
neither chooses a universal proof language nor requires every setting to have
decidable equality. Mathematical correctness and total author effort receive
separate conclusions.

## Common mathematical contract and available baseline

Both routes must construct existing `DepEq`/`FuncEq` derivations for the same
well-typed open terms, retaining their context and family index. The current
[grammar](../../SquareKit/Internal/DependentFunctions.lean) has base-domain
functions into primitive family fibers, with `Ctx`, `Dep`, `Func`, `Ren`, `Sub`
and typed substitution. It is not arbitrary dependent Pi syntax. In particular,
a family result cannot itself be a function. Do not use nested higher-order
function types as a supposed scale axis of this pilot.

The existing embedded-interface baseline is
[DependentFunctionEquality.lean](../../SquareKit/Internal/DependentFunctionEquality.lean):
`DepEq.beta`, `FuncEq.eta`, congruence and symmetry/transitivity, the typed
`.sub` rules, `substituted_beta`, `substituted_eta`, and `eta_type`. Both routes
may reuse these and all frozen public generic renaming/substitution laws. The
converter route additionally receives the reviewed #423 public service returning
those derivations, with its soundness, completeness and termination contract.
It may fall back to direct helpers, but must record each fallback. The direct
route may define general helper lemmas; their discovery, proof and maintenance
are charged rather than prohibited to manufacture a converter advantage.

The primary evidence for this choice is the actual grammar and equality source,
not an assumed cost advantage of normalization. The
[open-normalization assessment](open-term-normalization.md) and
[authoring assessment](typed-nbe-and-authoring.md) document the distinct
Sterling–Angiuli theorem and historical assistant examples. Their broader
calculi and author reports are not controlled measurements for this grammar.
This protocol tests a local hypothesis: whether selecting fewer individual
conversion steps repays the service's setup and repair costs as reuse grows.

## Tasks and independent scale dimensions

A preparer must materialize and independently check the following proposed
fixtures before freezing the trial. The descriptions are not executable
frontends or completed Lean fixtures. Use the same generated terms and expected
derivations for both routes, varying names only to preserve independence.

| Phase | Frozen mathematical task and observation |
|---|---|
| Initial proof | An open function variable with a genuinely varying result-family index. Eta-expand, beta-apply, and compare after two nonidentity typed substitutions and weakening. Return a source equality at the shared index, not equality of a few evaluations. |
| Composition scale | Repeat an admitted eta/beta expansion recipe at lengths 1, 4 and 8, keeping context width and substitution depth fixed. The preparer checks that each term is in the existing grammar. |
| Context scale | Use contexts with 2, 4 and 8 base variables and additional selected function/family variables, holding the conversion recipe fixed. Move the observed variable through weakenings without changing its identity. |
| Substitution scale | Compose 1, 2 and 4 nonidentity typed substitutions, holding the context size and redex recipe fixed. Preserve the changed dependent result index. |
| Legitimate repair | Replace a formerly constant substitution by one depending on another free base variable. Both routes must update formation/index evidence and preserve the intended theorem. Do not repair by weakening the specification or closing all free variables. |
| Invalid equality control | Replace the selected free function variable by a different variable of the same result type. A fixture-specific separating interpretation certifies that the equation is not derivable; evaluating both variables identically is insufficient. Also present a mismatched surviving result index and require formation rejection. |
| Held-out maintenance | A separately prepared weakening/substitution variant using the same supported rules. Reuse the route's earlier helper/library code and record what must change. It is unrelated to #108's unprepared theorem. |

Use one factor at a time; do not infer which dimension helped from a combined
increase. Report generated source nodes, maximum redex nesting, context widths,
substitution count and caller-written code separately. These proposed small
sizes bound a pilot, not a claim about industrial scale. Preflight may reduce
sizes before freeze if the grammar or environment cannot support them; retain
the abandoned fixture and reason. After freeze, an unsupported case is a result.

The negative free-variable case needs its checked separating interpretation
before execution. A checker saying “unknown” is not a proof of inequivalence;
a returned derivation of that invalid equation is a correctness failure. The
index mismatch is a formation test, not a second beta-eta incompleteness test.
For valid cases require selected source derivations and their family indices;
this fragment does not encode all higher identity witnesses. Neither route may
substitute proof irrelevance or semantic equality reflection for the source
contract. #401's richer witness obligation remains independently owned.

## Freeze and exposure controls

Execution prerequisites are a reviewed #423 service, checked fixtures and
negative controls, and a reproducible embedded baseline. The baseline can be
prepared without #115 or any new surface. A prerequisite failure blocks the
matched execution, not converter development or alternative exploration.

Before the first author receives a task, commit a trial manifest containing:

- Exact conaled/Lean/dependency revisions, generated fixtures and expected
  boundaries, public API/documentation bundle, hardware and command templates.
- Available tools, check commands, warm/cold cache policy, allowed generic laws,
  assistance policy and list of information withheld from authors.
- Actual model identifier/version and configuration, context limits, token and
  wall budgets, assignment procedure and author-session identifiers. Record
  unavailable metadata explicitly; do not invent a model version or active-time
  measurement. A model/configuration change starts a separately labeled cohort.
- Sealed repair and maintenance fixtures, phase release conditions, outcome
  rubric and stop rules. Neither author group sees the other group's attempts.

Use three fresh agent sessions per route, with identical recorded configuration
and disjoint contexts. Randomly assign the six sessions to routes before task
exposure and record the seed/procedure. Fresh sessions are independent exposure,
not independent model populations. Preparers, converter authors and reviewers
who have seen solutions cannot serve as those authors. Release the same initial
and scale tasks to each author; reveal repair and maintenance only at their
phases. Do not reuse any candidate for #108's protected fresh theorem.

Freeze interfaces for the experiment rather than stopping unrelated library
work. Correctness defects discovered during execution stop the affected cohort:
archive the failure, fix under the normal workflow and use a newly frozen cohort.
Do not replace its failed attempts with the successful rerun. Uniformly answer
only environment/protocol questions during execution; mathematical assistance
ends unassisted status and must be logged and assessed separately.

## Prospective budget and stopping rules

These are proposed pilot ceilings, not measured estimates or authorization for
external spending. Reserve up to six author sessions, each with 75 minutes of
wall time and 24,000 model tokens: 15 minutes for discovery/setup/admission,
20 for initial proof, 20 for scale cases, 10 for repair and 10 for maintenance
and rejection. Release a phase early if its previous tasks finish; keep the
whole-session ceiling. Record phase overruns rather than silently borrowing
unlimited time. Six ceilings total 7.5 author-hours and 144,000 model tokens;
parallel execution does not reduce the aggregate allowance.

Allow up to four active preparer-hours to create/check fixtures and the frozen
bundle, and four reviewer-hours for statement review, outcomes and synthesis.
These exclude #423's already incurred implementation effort, which must still
be inventoried separately. If preparation exceeds its ceiling, publish the
missing prerequisite and revised estimate before scheduling authors. Do not
spend the author budget on implementing a frontend or repairing the converter.
Stop at the first of time/token limit, completed phases, environment failure,
or correctness failure. Retain partial proofs and classify them explicitly.
Tool checks are observed costs, not artificially capped privileges for one
route. Apply equal environment limits to both groups.

The scheduler must fill the exact model/configuration and confirm available
session resources before executing this plan. No paid API purchase is authorized.
If execution needs such spending, or a different resource allocation requires
the owner, record that decision as blocked until answered. Missing construction
prerequisites are technical blockers. #429 does not require a preference about
NbE versus structural normalization; #423 decides from its proved contract.

## Cost ledger and interpretation

Keep timestamped commands, outcomes and generated artifacts per phase, with a
shared setup ledger. Separate existing reusable infrastructure from new trial
setup and author-created helpers. Count model admission even when it consists
of reusing a supplied package; state what the package's producer had to prove.
A shared package should be charged once for the total-cost comparison, not
hidden or charged again to every small instance.

| Quantity | Recording and limitation |
|---|---|
| Elapsed time | Monotonic phase start/end and tool durations; report waits and infrastructure failures separately. Shared hardware contention makes cross-author timing noisy. |
| Active work | Human logged work intervals where available; for agents report tool/model intervals and tokens separately. Wall time minus tool time is not a reliable measure of reasoning effort. Missing active-time telemetry stays missing. |
| Checks and repairs | Compile/audit invocations, diagnostics, changed submissions, first and eventual checked completion, assistance, semantic versus syntax errors. Cached checks remain invocations; record cache policy. |
| Artifact size | Caller lines and syntax nodes, helper/library additions, generated terms and receipts separately. Minified spelling or moved helper code is not a productivity result. |
| Review and maintenance | Reviewer time, findings, fixes, held-out repair burden and touched dependencies. Longer-term maintenance remains unmeasured by this pilot. |
| Upfront cost | #423 implementation/review records if available; trial setup and model admission costs. Unavailable historical labor cannot be reconstructed from commit timestamps. |

Report each author and each scale dimension, including timeouts and failures.
Summarize completion rates and distributions descriptively; six sessions do not
establish a general advantage or causal scaling law. Show incremental work
alongside total work. For a hypothetical reuse count N, an amortization scenario
may display `setup + N × observed incremental cost` with its assumptions; do
not turn extrapolation beyond the fixtures into measured evidence.

An adoption recommendation requires correct derivations and a useful reduction
in observed recurring work after setup/repair costs are disclosed. Equal or
better direct-helper performance is a valid outcome. A useful optional converter
can remain available without a productivity claim. Conversely, lower author
cost does not excuse a weaker equality contract, dropped indices or failed
negative controls.

## Source, surface and neighboring obligations

[#115](https://github.com/VladimirMarko/conaled/issues/115) owns inspection of
Agda completed declarations, including types, bodies, levels, options, opaque
boundaries and dependencies. It must determine retained versus erased source
information before an importer can supply comparable terms. This pilot instead
starts from existing scoped Lean data; it makes no lossless Agda export claim.

[#116](https://github.com/VladimirMarko/conaled/issues/116) owns surface designs
and their elaboration contracts. It can use this same grammar and equality
boundary while recording notation, inference and mathematical changes. Paper
syntax is source-review evidence only. [#117](https://github.com/VladimirMarko/conaled/issues/117)
may reuse the ledger, independence controls and repair tasks when executable
surfaces exist, with equal assumptions and helper capabilities. It needs a new
frozen comparison; this converter trial cannot establish a surface advantage.

[#25](https://github.com/VladimirMarko/conaled/issues/25) still owns its three
matched Felix/Lean categorical tasks. Reuse its separation of setup, composition
and caller obligations, without replacing those tasks by this narrower equality
trial. #195 owns reusable measurement tooling; missing sophisticated tooling
does not require inventing telemetry instead of recording manual receipts.

#107 is resumed and can use new abstractions or frontends when justified. This
protocol does not require its present Lean DSL to be the final author surface.
#108 retains its reviewed freeze and independent theorem. #433's technical
smooth-model work is not gated by a favorable result here or in #434. The
[monodromy path assessment](monodromy-consumer-path.md) and #435's finite-action
construction test mathematical reuse; their success alone does not measure the
authoring costs this pilot is intended to expose.
