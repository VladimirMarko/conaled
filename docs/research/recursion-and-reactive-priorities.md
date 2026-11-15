# Recursion and FRP-adjacent priorities

Ownership update: #193 is closed and supplies completed measured-execution
evidence. Historical assignments to #193 below are not an active work queue;
use the [current residual-owner map](workstream-status-reconciliation.md) for
new resource, runtime and error-comparison work.

Research and prioritization, 2026-10-28. Local baseline:
`f06787b2b47ad138e39ebce4674f7941299ba690`. This note recommends future work;
it adds no formal capability or implementation commitment. “FRP-adjacent” means
feedback, state, observation, partial information and reactive progress.

**Prioritize reusable recursion and corecursion laws, exercised first on
initialized causal feedback. Develop indexed and dependent interpretation
transport alongside them.** These directions connect recurring mathematical
constructions across settings; their value is broader than adding another
individual logic. The next tractable experiment and the most expressive
long-term framework need not be the same project.

## Ranked agenda

| Rank | Mathematical reach | Next useful evidence and ownership |
|---|---|---|
| 1 | (Co)induction, iteration and feedback: factor recursive definitions from their bodies; reuse uniqueness, fusion, bisimulation and decomposition laws. | An initialized discrete feedback operator transported between stream and state realizations, followed by a bounded recursive compiler extension. [#109](https://github.com/VladimirMarko/conaled/issues/109) owns compilation; [#27](https://github.com/VladimirMarko/conaled/issues/27) owns FRP feedback/runtime scope. |
| 2 | Higher-order relational and dependent interpretation: carry one construction across representations while retaining witnesses, indices and admissible reasoning. | Transport the feedback experiment's state relation and finite-observation certificate through a second representation. Reuse existing logical relations and indexed contracts; [#36](https://github.com/VladimirMarko/conaled/issues/36) owns language/model integration. |
| 3 | Open-system composition: combine component guarantees with explicit environmental assumptions, including partial knowledge and progress. | Connect feedback observations to the existing frontier/demand model; expose source advancement and processing obligations. [#31](https://github.com/VladimirMarko/conaled/issues/31), [#193](https://github.com/VladimirMarko/conaled/issues/193) and [#196](https://github.com/VladimirMarko/conaled/issues/196) retain engine, resource and interaction ownership. |
| 4 | Multimodal dependent reasoning: make changes of phase, time, information and mathematical setting composable. | Select interacting modalities only when the preceding consumers demonstrate the required maps and laws. This is a high-potential language direction under #36/[#200](https://github.com/VladimirMarko/conaled/issues/200), not a prerequisite for feedback. |

This ordering measures expected reuse of constructions and proofs. It does not
rank subjects by prestige or treat a small implementation as the architectural
ceiling. Open-system games could later distinguish controllable choices from
hostile environments, but the present delivery theorems do not synthesize a
winning strategy; begin with explicit assumption/guarantee contracts. The existing
[relation transport](../../SquareKit/RelationTransport.lean) already supplies the
image/requirement Galois connection and both composition laws. Ordered predicate
transformers and future fixed-point arguments should reuse this boundary.

## Recursion separates along more than recursion schemes

**Initial algebras and final coalgebras separate shape from computation.** An
algebra `F A → A` consumes one layer; initiality determines its fold. Dually,
`S → F S` describes transitions, and finality determines observable behavior.
The reusable results are uniqueness, fold fusion and coinductive comparison,
not just convenient recursive syntax. For streams, coalgebraic state can remain
hidden while observations determine equivalence. [Jacobs–Rutten,
*A Tutorial on (Co)Algebras and (Co)Induction*](https://www.cs.ru.nl/B.Jacobs/PAPERS/JR.pdf)
develops these definition and proof principles.

Catamorphisms, anamorphisms and hylomorphisms expose patterns that can be
optimized algebraically. Their validity still depends on the ambient semantics:
an unfold into a total finite datatype needs termination, whereas an unfold
into a final stream object has different obligations. The original
[Meijer–Fokkinga–Paterson calculus](https://ris.utwente.nl/ws/files/6142049/meijer91functional.pdf)
uses lazy/domain semantics; importing its equations into total Lean requires
checking those assumptions. Well-founded recursion also separates a decreasing
relation and its evidence from the recursive body. It need not coincide with
syntactic descent through the input datatype.

**General iteration separates solutions from termination.** A chosen operation
solving recursive equations is additional target structure. Domain semantics
can interpret nontermination by bottom; monotone maps on complete lattices have
least fixed points. The standard theorem expressing them as the supremum
of countably many finite iterates assumes suitable continuity. The pinned Mathlib implementation distinguishes
`OrderHom.lfp`, `map_lfp` and `lfp_eq_sSup_iterate`, the last requiring
`ωScottContinuous`. These are mathematical existence/equality results, not an
executable decision procedure for termination.
[FixedPoints.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/FixedPoints.lean).

A transport must preserve the chosen solution. For least-fixed-point transport,
a commuting square alone is insufficient; bottom and suitable chain-supremum
preservation provide a useful stronger route. Other settings need their own
hypotheses. An unrestricted total `fix : (A → A) → A` satisfying its equation
cannot be available for every Lean type: Boolean negation is a counterexample.
Keep compiler termination, termination of the represented program, and
convergence of an approximation process separate.

**Guarded recursion separates recursive dependency from present availability.**
A later modality permits a fixed point of `later A → A` in appropriate models.
[Birkedal et al., *Synthetic Guarded Domain Theory*](https://arxiv.org/pdf/1208.3596)
construct a model supporting guarded recursive terms, types and relations.
This can make higher-order recursive invariants compositional, beyond a list
of first-order recursion schemes. It does not make arbitrary waiting terminate.

**Feedback and fixed points can be two presentations of shared laws.**
[Milius–Litak, *Guard Your Daggers and Traces*, §§2–3](https://www8.cs.fau.de/ext/milius/publications/files/ml_fics13.pdf)
work with finite products and a pointed delay endofunctor. Their guarded
Conway operators correspond to guarded trace operators; associated laws
include decomposition of mutually recursive systems. Thus one can separate
recursive wiring, the body, delay discipline and equational theory. This is
stronger than naming folds, but does not identify every operational loop with
a categorical trace. The selected model must satisfy the laws.

Felix already reflects this distinction: its pinned
[`Traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L151-L160)
requires a separate `WF f` argument. That abstract predicate is not itself an
FRP scheduler or a proof that a particular feedback dependency is admissible.
Elliott's [*Compiling to Categories*, §12](https://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf)
leaves recursive compilation as a direction to investigate, not a completed
construction available to import.

## What FRP adds to the problem

Elliott's [*Push-Pull Functional Reactive Programming*](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf)
starts from compositional behavior/event meanings and relates demand-driven
and data-driven realization to them. That supports keeping denotation,
knowledge and execution distinct. The local [specification](../../Applications/FRP/Spec.lean)
contains real-time behaviors and ordered event batches; it is not synonymous
with discrete synchronous streams. [Frontiers](../../Applications/FRP/Frontier.lean)
certify completed history, including known silence. Unknown information is
not an empty batch.

[Trace](../../Applications/FRP/Trace.lean) and
[Demand](../../Applications/FRP/Demand.lean) already prove observation and
conditional delivery properties. The latter remains a history-indexed model;
#31 specifies a future retained-state command interface. Meanwhile
[Progress.Processors](../../Applications/Progress/Processors.lean) already has
Mealy machines, stream/list agreement, finite delivery and relational squares;
[Progress.Streams](../../Applications/Progress/Streams.lean) has coalgebra
unfolding and transport. Rebuilding these would add little. Neither provides
the requested source-level recursive compiler or a general feedback calculus.

Discrete initialized delay is a useful first discipline. For dense time,
“depends only on earlier times” can permit infinitely descending dependencies
within a bounded interval. #27 therefore requires initialized history and an
appropriate well-founded argument, for example a positive delay from an origin.
Do not silently claim that a processing tick supplies a physical-time delay.

Guarded productivity also does not imply fair source delivery. In
[Lively RaTT](https://arxiv.org/abs/2003.03170v2), separating temporal next from
the guarded modality is essential to retaining inductive until's liveness
meaning. Locally, preserve [explicit finite certificates](../../SquareKit/Temporal/Finite.lean)
and the independent source/processing premises; a feedback proof cannot
manufacture a response from a stalled source.

## Two bounded experiments

**First: a compositional feedback boundary, not another scan theorem.** Start
with a total step `f : A × S → B × S` and initial `s₀`. Define the stream solution
by `s(n+1) = (f (a(n),s(n))).2` and `b(n) = (f (a(n),s(n))).1`.
Expose initialized feedback as a constructor, with interpretation into existing
Mealy execution. Prove solution uniqueness, prefix causality, and preservation
under a relation between states whose step condition preserves outputs and
successor states. Reuse `mealy_delivery` and `unfold_transport` where their
hypotheses fit; add the genuinely missing relational/feedback comparison.

Exercise two coupled accumulators in joint-state and sequentially factored
realizations, with an explicit one-tick delay breaking the cycle. The acceptance
result is agreement of every finite output prefix and transported initial-state
obligations. Reject an instantaneous Boolean-negation loop and distinguish
missing initialization from a valid initialized solution. A complete Conway
law suite, dense-time feedback and graph scheduling remain separate decisions.
An FRP adapter should consume explicitly completed batches and state how they
become ticks; duplicates, ordering and empty batches must survive. Do not make
that adapter depend on an unimplemented #31 engine.

**Second: recursive compilation with a useful independent interpretation.**
Under #109, select finite list folding or a well-founded traversal, represent
its recursive body compositionally, and prove its translation without recursive
inlining. Compare ordinary evaluation with an instrumented interpretation that
retains the same value plus an explicit operation count. Supply fold/iteration
preservation once, then reuse it for a second client. Reuse existing algorithm
consumers, such as [bracketing](../../Applications/Bracketing/Recursive.lean),
rather than assuming the older #109 remark that ADWH has not been inspected
still describes this checkout. Its indexed traversal may require a later,
richer fragment than the first list example. General partial iteration remains
an additional semantic capability, not a hidden promise of this total fragment.

## Higher-order and modal follow-through

The existing [STLC logical relation](../../SquareKit/STLCRelations.lean) already
handles arrows by quantifying over related arguments; dependent witness
transport and temporal relations are also present. Extend those consumers
rather than rebuild their foundations. The payoff is one recursive client
correct in multiple settings, with index changes and additional principles
visible in its contract.

[Multimodal dependent type theory](https://www.danielgratzer.com/papers/journal-multimodal-dependent-type-theory.pdf)
parameterizes reasoning by modes, modalities and transformations, including
instances for guarded recursion and cohesion. It is a credible long-term
organization for these interactions. Prioritize it by asking whether one
argument can transport across a concrete pair of settings with less duplicated
proof work. First identify which operations commute with reindexing or delay;
do not postulate a universal mode theory to conceal missing preservation laws.
Track these choices under #200/#36, retain
[#145](https://github.com/VladimirMarko/conaled/issues/145)/[#146](https://github.com/VladimirMarko/conaled/issues/146)'s codata/progress results,
and leave measured history/resource bounds to #193. None of the proposed
experiments alone establishes a lazy runtime, fairness or a performance gain.
