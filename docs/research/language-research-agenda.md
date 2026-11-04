# Language research after the external comparisons

The project owner approved the following issue graph after #280's discovery
assessment and #286/#287's paper comparisons. This records research ownership
and the next experiments; it does not select a universal language foundation.
GitHub issues own acceptance criteria and live status. The existing programme
[#235](https://github.com/VladimirMarko/conaled/issues/235) coordinates these
children with #36 and #200.

## Three sustained directions

| Parent | Initial work | Boundary |
| --- | --- | --- |
| [#288: compositional theory extensions](https://github.com/VladimirMarko/conaled/issues/288) | [#291: all-model representation extensions and dependent witness descent](https://github.com/VladimirMarko/conaled/issues/291); coordinate existing [#262](https://github.com/VladimirMarko/conaled/issues/262) | A selected-client compatibility theorem, expansion of every admitted model, consequence reflection and recovery of selected data are different claims. |
| [#289: dependent semantics and coherence](https://github.com/VladimirMarko/conaled/issues/289) | [#292: local-universes applicability](https://github.com/VladimirMarko/conaled/issues/292) | Test exact model and substitution hypotheses. This does not expand #107's repair or choose #108's fresh theorem. |
| [#290: reusable theories and proof transport](https://github.com/VladimirMarko/conaled/issues/290) | [#293: proof-requirement discovery trial](https://github.com/VladimirMarko/conaled/issues/293), [#294: theory-network comparison](https://github.com/VladimirMarko/conaled/issues/294) | Proof discovery, theory publication, encoding adequacy and interpretation require separate evidence. No general importer is presumed. |

These are research directions with first milestones, not module boundaries.
The initial children are independently executable; their scheduling order is
not a dependency graph. #291 must select its consumer before designing the
reusable interface. #293 must freeze its support, tasks and trial protocol
before dispatch. #292 may find that a replacement semantics does not repair the
source judgment in question. Such a result constrains the proposed architecture
without weakening that judgment.

Each parent requires a synthesis and integration decision beyond its children's
individual results. Research may propose a replacement architecture even when
it cannot immediately fit the current library. Implementation proposals must
then account for retained concrete capabilities and migration costs.

## Lower-priority investigations

These bounded studies make the deferred leads actionable. Their priority is
provisional; it does not mean their mathematics has been rejected. New
sustained programmes can follow evidence from these studies without duplicating
existing owners now.

| Study | Coordination | Reason to promote |
| --- | --- | --- |
| [#295: relational proof transfer](https://github.com/VladimirMarko/conaled/issues/295) | #290; reuse #210 | A client needs argument reuse across a relation that is not an isomorphism. |
| [#296: effectful proof realizers](https://github.com/VladimirMarko/conaled/issues/296) | #235/#196/#200 | Changing effects must retain a returned witness and explicit interaction laws. |
| [#297: modal contexts and higher identity](https://github.com/VladimirMarko/conaled/issues/297) | #289/#36/#102/#107 | Context access or identity data exposes an interface mismatch. |
| [#298: higher-order probability models](https://github.com/VladimirMarko/conaled/issues/298) | #235/#36; reuse #199/#285 | Arbitrary admitted random functions are required beyond a fixed closure representation. |
| [#299: quantitative and ordered observations](https://github.com/VladimirMarko/conaled/issues/299) | #235/#174/#193 | Error or precision must compose under an explicit order or metric. |
| [#300: open-system wiring](https://github.com/VladimirMarko/conaled/issues/300) | #235/#27/#36 | Permitted wiring, feedback or hierarchical decomposition needs a richer composition contract. |
| [#301: omitted semantic traditions](https://github.com/VladimirMarko/conaled/issues/301) | #235 | A competing foundation could overturn assumptions used to rank the current candidates. |

#301 covers synthetic domain theory, nominal binding, proof-theoretic semantics,
classical realizability, rewriting-based logical frameworks and broader
categorical systems theory. It must inspect primary technical sources and
propose at most two deeper follow-ups, retaining explicit reasons to defer
other leads. It does not declare the literature search exhaustive. #298 and
#299 keep probability and approximation separate; #297 keeps context access
and higher identity as separate comparisons.

The source assessments and their limits remain in the
[external discovery report](external-discovery-assessment.md),
[foundations comparison](external-language-foundations.md), and
[computation comparison](external-computational-semantics.md).

## Author trials alongside architectural research

A trial freezes the interface being measured, not the project's design. Keep
the mathematical task, reference contract, public inputs, author exposure,
budget, attempts, assistance and diagnostics. This lets later changes be
compared with a durable baseline. A redesign does not retroactively invalidate
what an earlier trial established under its recorded conditions.

Trials can expose missing abstractions and thus enlarge the design space.
Distinguish that evidence from mathematical limitations or a ranking of all
possible interfaces. After an interface change, rerun affected tasks and include
fresh held-out tasks and unexposed authors where needed; do not optimize only
for published solutions. Separate preparation and repair costs from measured
author work. These bounded agent trials do not establish general human usability
or causal productivity gains.

At issue creation, #278, #279 and #285 were already completed in local master
at `2556ead64c4846ab2aec80bf0132113bb7c365ad`. Reuse their
[constructor/observer result](constructor-observer-composition.md),
[author-trial evidence](construction-observation-author-trials.md), and
[higher-order comparison](higher-order-extensional-comparison.md).
They are not queued again. #249 also remains completed evidence.

The open [#108 retest](https://github.com/VladimirMarko/conaled/issues/108)
requires #107's reviewed frozen handoff and retains its independent theorem
selection. The open [#117 surface comparison](https://github.com/VladimirMarko/conaled/issues/117)
requires #116's surface-design outcome and executable comparison readiness.
#293 tests discovering requirements, a different task from either of those or
#279. It can use a provenance-recorded dependency ledger; that measures the
assistance actually supplied, not an unimplemented extraction tool.

Creating this graph does not start the studies, reopen completed issues,
resume #107's paused work, activate #260 or make a custom frontend a prerequisite.
