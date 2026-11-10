# PetaBricks and policy-directed realization choice

Assessment date: 2026-11-09. Local source baseline:
`2f89f8651843797822efbb7da038311ab3d9f04d`.
This is a research assessment and proposed design, not an implementation or
capability-parity claim. No architecture decision is made here.

## Assessment

The proposed separation fits the repository: supply several realizations of a
semantic contract, expose permitted choices, and select using a policy informed
by observations. The qualification is that PetaBricks exposes choices within
algorithms, including recursive subproblems, rather than only dispatching among
complete programs. Its [project description](https://projects.csail.mit.edu/petabricks/)
also includes parallelization, data distribution, blocking, parameters and
accuracy. A family of complete implementations can encode these possibilities,
but compositional descriptions avoid requiring authors to enumerate every mix.

The remaining work is substantial engineering and some reusable semantic
contracts. The sources examined do not establish an architectural obstruction,
or establish that the present compiler already supplies PetaBricks facilities.

## What PetaBricks adds

Transforms contain rules over data regions, with dependency and applicability
information used to construct schedules. Recursive calls can choose algorithms
again, yielding hybrids. Original tuning runs at compilation or installation;
a saved configuration can guide execution or compiler specialization. Its
bottom-up tuning heuristic assumes smaller subproblems can be optimized
independently. Cross-implementation consistency tests do not prove correctness.
See the [original paper, sections 2–3](https://people.csail.mit.edu/jansel/papers/2009pldi-petabricks.pdf).

The later [SiblingRivalry work](https://dspace.mit.edu/entities/publication/ef9e2803-967a-4980-968a-dc1b9629812b)
adds online adaptation by racing known and experimental configurations on
separate portions of the available cores. The
[variable-accuracy extension, section III](https://groups.csail.mit.edu/commit/papers/2011/ansel-cgo11-pbaccuracy.pdf)
distinguishes statistical training evidence, runtime checking, and mathematical
guarantees. The [input-sensitive tuning paper](https://commit.csail.mit.edu/papers/2015/yding-pldi15-pbinput.pdf)
includes learned input grouping and feature selection, accounting for feature
extraction costs.

Design inference: monitoring, selection, and policy improvement should remain
separate. A fixed or offline-trained policy needs no continuous tracing.
Observing only the selected branch does not reveal how alternatives would have
performed; learning may require explicit exploration with a resource budget.

## Existing local support

| Requirement | Inspected local evidence | Scope |
|---|---|---|
| Multiple correct algorithm recipes | [ScanPlan](../../Applications/Parallel/ScanPlan.lean), `Scanner.product`, `Scanner.compose` and `ScanPlan.correct` | Constructors compose implementations and their independent sequential-specification proofs. Recipes retain algorithm distinctions erased by flattening. |
| Separate behavior and observations | [Measured](../../Applications/Resources/Measured.lean), `bind_erases`, `erasureSquare`, `reweight_bind` | Value/observation pairs with ordered additive composition. This is not a wall-clock profiler or a general parallel timing algebra. |
| Admissibility and objectives | [Optimization.Basic](../../Applications/Optimization/Basic.lean), `minimizers`, `pareto`, `Attained` | Ordinary sets and objective functions. The general classical selector is noncomputable; it is not an autotuner. |
| Realization contracts for selection | [Optimization.Relations](../../Applications/Optimization/Relations.lean), `selectionSquare`, `boundSquare` | Indexed feasible/optimal or bounded selections, conditional on supplied realization proofs. |
| Concrete policy-dependent selection | [ScanSearch](../../Applications/Parallel/ScanSearch.lean), `selected_work`, `selected_weighted`, `selected_deadline` | Executable finite search and certified selections over a declared bounded grammar. Depth is measured circuit arrival, not an actual machine deadline. |
| Target-dependent interpretation | [Compiler](../../Compiler.lean), `Target`, `compile`, `Sound` | Compilation into supplied operations with separate semantic obligations. This interface does not itself construct a profiler, scheduler or adaptive optimizer. |

The [scan research record](scan-fft-optimality.md) documents current measured
circuits and search, beyond the original scope of ADR 0005. In particular,
`ScanSearch` measures supported continuations before pruning. Existing examples
show why equal aggregate work/depth does not make two plans interchangeable in
a larger timing context. These capabilities give a useful starting experiment;
they do not constitute PetaBricks runtime parity.

## Proposed interface and obligations

Describe the feature as **policy-directed choice among admissible realizations**.
Use the existing glossary meaning of realization, including relational and
approximation contracts. Keep these roles separate:

- A specification states the allowed observations of the result or execution.
- Realizations supply implementations, applicability conditions, and evidence
  for that specification. Composition rules describe legal combined plans.
- A policy expresses objectives, constraints, and a selection strategy.
- An observation mechanism records execution evidence with its workload and
  target context. A tuner uses that evidence to revise later selections.

For a simple total, pure, exact case, the intended law is elementary: if every
admissible realization computes the same specification on its valid inputs,
then any total selector returning an admissible realization preserves that
specification. This is a paper-level argument, not a new checked theorem.
Selection need not be optimal for functional correctness. A heuristic can
propose an index that is validated against an executable admissibility check
or restricted to a certified catalog. Empty feasible sets require a specified
failure or an available admissible fallback.

The general form needs stronger contracts at the places where behavior varies:

- **Recursive choice:** selecting at each recursive call requires a common
  progress argument or another appropriate termination/productivity contract.
  Correct complete implementations alone do not prove arbitrary interleavings
  of their internal steps correct or terminating.
- **Parallel plans:** dependency, mutation and synchronization legality must
  survive scheduling and data-layout changes. A shared result type is insufficient.
- **Approximation:** choose against an error relation and compose local error
  budgets into the requested whole-program guarantee. Exact equality would
  exclude useful approximate realizations; sampled quality alone is not a
  universal error proof.
- **Stateful switching:** choosing before a call differs from replacing a running
  realization. The latter needs a state correspondence and a valid transfer.
- **Observation and cost:** preserve the specified functional/effect behavior
  under instrumentation and charge monitoring, selection and conversion costs.
  A model objective and an empirical performance estimate have different evidence.

A hypothetical separating example uses states {0, 1, done}. Machine A steps
0 to 1 to done; machine B steps 1 to 0 to done. Each terminates from every state,
but alternating A at 0 and B at 1 loops forever.
Thus per-realization termination is insufficient for unrestricted mid-execution
switching. For optimization, the repository already has concrete counterexamples
to pruning by aggregate work/depth; reuse those instead of assuming local cost
rankings survive composition.

The compiler can expose choices and specialize selected plans; an interpreter
or runtime can retain choices requiring live context. Resolve stable decisions
earlier when useful. There is no need to require monitoring on every execution,
or to add this facility to every backend. The public interface should hide
profiling and search machinery behind execution under a declared policy, while
retaining explicit semantic and resource contracts.

## Discriminating next experiment

Extend the existing scan example with selection among certified plans under a
caller policy, then compare fixed selection with observation-informed selection
on an executable target. Include both whole-plan selection and nested choices.
Retain the checked continuation counterexample: a locally discarded plan must
remain available when needed for a feasible completion. Account for selector
and instrumentation overhead separately from the existing circuit model.

This would test the proposed seam using present proofs and two different
selection strategies. It would not establish numerical accuracy tuning,
automatic dependence analysis or general parallel scheduling; those require
separate examples. No implementation or tracker change is part of this assessment.
