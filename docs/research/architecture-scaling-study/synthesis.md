# Interim comparison of architecture and scaling alternatives

The [completed comparison results](results.md) record the executed successors,
the finite author trial and current residual owners. The planning and interim
statements below retain their historical scope.

The [final disposition](disposition.md) supersedes this report’s pending #362
scheduling and assigns the bounded follow-ups. This report retains the evidence
and recommendations at its publication checkpoint; the original independent
assessments remain unchanged.

Historical interim report: the incoming evidence has now arrived and is assessed
in the [orbifold synthesis](orbifold-synthesis.md). The pending-report statements
below describe the earlier assessment, not the current input status.

This is the interim result for [#362](https://github.com/VladimirMarko/conaled/issues/362),
against repository baseline `5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`.
The independent Agda/orbifold library comparison announced by the owner has not
arrived. Final architectural recommendations and release of #358–#361 remain
pending that evidence or an explicit owner change of scope. No implementation,
new formalization, migration, or scaling experiment was performed for this study.

The evidence supports reopening the choice of dependent semantic foundation and
extension composition machinery before expanding the current interfaces. It
does not yet establish a replacement. Existing checked results remain useful
regression requirements for any candidate, including one that changes the core
representation.

## Findings and disagreements

The preserved assessments are [foundations](foundations-initial.md),
[implementation and scaling](scaling-initial.md), and
[alternatives](alternatives-initial.md). Each received the same [brief](brief.md)
in fresh context and completed its initial report without seeing the others.
The coordinator read all three before synthesis. There was no subsequent
cross-exposure among those authors. This is independence of assessment, not
model diversity; agreement is not a vote establishing mathematical correctness.

All three identify a gap between a composition theorem for a fixed interface and
evidence that the interface reduces work across many mathematical settings.
The #357 author trial establishes that both routes were usable for its extension.
The native route already uses reusable library machinery. Neither elapsed time
nor source length in that trial measures scaling in settings, interactions,
model construction, or maintenance.

Their priorities differ. The foundations assessment puts weak comprehension and
coherence first. The alternatives assessment puts interaction between theories
and relational hiding first. The scaling assessment proposes comparing both
model coherence and relational composition before further client machinery.
These priorities concern different recurring costs. They can be tested against
separate semantic requirements without choosing one foundation in advance.

Two existing results qualify the proposed tests. The
[all-model representation extension study](../all-model-representation-extensions.md)
already derives bounded expansion, comparison, and selected dependent descent
across set models. The [joint conversion study](../joint-conversion-extensions.md)
already has joint conversion results and a failure control for separately
admitted extensions. Consequently, a new tiny incompatible-extension example
would calibrate a comparison contract; it would not establish a newly discovered
incumbent defect. The useful question is whether another formulation derives
interaction and maintenance obligations more generally or with less repeated
work than these existing bounded constructions.

## Alternatives with distinct potential benefits

The following are research candidates, not adopted interfaces. The individual
reports record theorem hypotheses and source versions in greater detail.

| Candidate | Potential architectural benefit | Boundary that must be tested |
|---|---|---|
| Weak comprehension followed by local-universes coherence | Derive strict substitution behavior from weaker semantic structure | The local-universes theorem needs a full comprehension category satisfying LF and appropriate weakly stable constructors; selected eliminators and comparisons between separately strictified models need additional analysis. |
| Algebraic sums and tensors; distributive laws | State extension interaction explicitly and derive composition where its laws hold | Sum and tensor impose different interactions; fixed algebraic settings do not automatically cover dependent or higher identity data. |
| Decorated corelations and relational black boxing | Derive composition while hiding internal state and retaining boundary behavior | Structural hypotheses and the observation being preserved matter; existential possibilities alone do not retain selected witnesses or solution multiplicity. |
| Univalent categorical internal languages | Make equivalence of presentations part of the foundation | Results for categories with set-valued homs do not by themselves settle arbitrary higher coherence, or justify changing the host. |
| Nominal binding and higher-order probability | Expose binding maintenance and correlations that recent arithmetic clients do not exercise | These are different tests of representation and semantic coverage, not interchangeable complete architectures. |

The primary sources supporting these opportunities include
[Lumsdaine–Warren, local universes](https://arxiv.org/abs/1411.1736),
[Ahrens–Lumsdaine–North, comprehension frameworks](https://arxiv.org/abs/2412.19946),
[Hyland–Plotkin–Power, combinations of effects](https://www.dpmms.cam.ac.uk/~jmeh1/Research/Publications/2006/hpp06.pdf),
[Bonsangue–Hansen–Kurz–Rot, distributive laws and equations](https://arxiv.org/abs/1503.02447),
[Fong–Sarazola, black box functors](https://arxiv.org/abs/1812.03601), and
[Ahrens–Kapulkin–Shulman, univalent categories](https://arxiv.org/abs/1303.0584).
These supply mathematical precedents, not newly checked conaled results.

## Two proposed comparisons before implementation

First, use a selected higher witness with nontrivial dependent action, two
changes of context, and two equivalent but nonidentical presentations. Compare
a direct strict model with weak semantic structure plus coherence, keeping a
native internal-language formulation eligible. Require the selected comparison
and its action to survive. Add an ineffective action case: different isotropy
arrows can act identically, so equality of actions alone cannot certify retention
of the chosen arrow. A common abstract transport argument should specialize to
both an extensional and a higher setting; it must not assert the same nontrivial
action in both.

Second, specify a small interacting theory and an open constraint system by
independent meanings. Distinguish separate admissibility, a sum of theories,
and additional mixed laws. Compare a construction of compatible joint models
and a justified rejection against the existing bounded extension machinery.
For the open system, specify all boundary assignments extendable to an internal
solution and composition by existentially joining internal boundaries. Include
inconsistent systems, multiple internal solutions, and renaming. Test whether
a proposed observation factors through this relation. A client that counts
solutions or selects one needs a richer contract; discarding that information
cannot count as satisfying its specification.

Neither comparison has been run. Their purpose is to expose where a formulation
derives obligations and where it transfers them to model authors. A successful
adapter alone does not answer that question. Binding and correlated probability
remain additional coverage probes if the incoming report or these comparisons
leave their costs unresolved. The alternatives assessment gives concrete tests
for each rather than treating omission as evidence of impossibility.

## Scaling evidence to collect

Separate framework setup, model setup, operation-by-setting obligations,
interpretation edges, mixed extension laws, client work, checking cost, and
maintenance. Vary construction size N, primitive count P, settings S, actual
comparison edges E, and actual interactions I. This is an accounting plan, not
an asymptotic complexity theorem. Do not assume every operation needs a new
proof in every setting, or that every pair of extensions interacts; a generic
model construction may derive many of those cases.

Measure changes to a primitive, a model presentation, and an observation as
well as adding more syntax. Include elaboration time and memory, failures,
helper preparation, and repeated author interventions. Universal theorems over
N do not establish predictable checking costs or maintenance effort. Use matched
semantic tasks and several held-out changes before drawing agent-productivity
conclusions. A candidate may win by removing obligations even if its initial
example is longer. A failed candidate should retain a precise record of which
requirement or cost defeated it.

## Incoming orbifold comparison

The user's report of a completed Agda development in the setting of
[Myers' paper](https://arxiv.org/abs/2205.15887) is distinct from the archived
Agda checkpoints and the historical standalone Lean formalization. We have not
audited the new artifact and do not infer the incoming report's library ranking.

On arrival, record its revision, compared library revisions, and representative
statements. Separate internal synthetic derivation, validity of a concrete model,
comparison with classical presentations retaining isotropy, and executable
realization. Identify whether each reported gap is foundational, semantic, API,
maturity, documentation, or artifact compatibility. A theorem conditional on
the synthetic setting is a legitimate result; it does not automatically provide
a classical comparison or a concrete model of that setting.

Use a matched requirement from that report to challenge the proposed comparisons
above. The report may change their order, add a candidate, or show that the most
useful work belongs in another system with a separately justified connection to
conaled. No import, migration, or contact with the external session is part of
this publication.

## Consequences for the pending work

| Work | Provisional consequence, subject to incoming evidence |
|---|---|
| #358, authoring and scaling | Compare formulations and model-building costs before expanding the incumbent local-operator API. Retain the matched maintenance study. |
| #359, selected higher shared meaning | Keep the semantic requirement; allow the foundation and representation to change. Preserve witnesses even when their actions coincide. |
| #360, resource modes | Compare the independent operational contract with alternative interaction or separation machinery; do not assume modes are the necessary organizing interface. |
| #361, selected partial solutions | Keep selected-solution behavior distinct from existential relational hiding. Let model construction and the external consumer inform the test. |

All four remain blocked by #362. Preserve current checked code as evidence;
revise the evaluation method now; investigate the alternatives without requiring
incumbent-shaped adapters. Adoption, replacement, further implementation, and
closure of #362 await reconciliation with the incoming report. Existing #310
work remains separate; #107 stays paused, #108 unselected, and #260 inactive.
