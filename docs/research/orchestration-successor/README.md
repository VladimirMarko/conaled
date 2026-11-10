# Orchestration successor handoff

This handoff transfers the preservation and dependent-semantics workstream
from session `01a1aa09-57ab-73d2-8e9d-eed6188f19c6` to a fresh orchestrator.
The owner requested completion of the running increments, a merge to `master`,
appropriate follow-up issues, and a new session before further implementation.
The successor's initial turn should read this handoff and acknowledge readiness.
Wait for the owner's continuation instruction before scheduling more work.

## Start here

1. Read the repository's current `AGENTS.md` and its applicable pointers.
2. Read the outgoing acceptance and transfer comment under
   [#235](https://github.com/VladimirMarko/conaled/issues/235). It records the
   delivered commit, checks, review outcomes and successor session ID. GitHub
   issue state and immutable Git evidence take precedence over local scratch
   status files.
3. Inspect the current checkout, remote and worktrees before changing anything.
   Other sessions also use this repository. Preserve their commits and edits.
4. On continuation, reconcile the scope below with live issue comments. Keep
   implementation, review, validation, integration and issue closure distinct.
   A focused build or a clean source review is not full candidate acceptance.

## What this checkpoint contains

- [#427](https://github.com/VladimirMarko/conaled/issues/427) and
  [#430](https://github.com/VladimirMarko/conaled/issues/430) were included in
  checkpoint `ab96603dcb97b4f1b2eef9f750672c3f191963f4`, merged and pushed
  before the final handoff batch. Their reports are
  [the weak groupoid-unit comparison](../local-universes-weak-groupoid-unit.md)
  and [numerical motion wiring](../numerical-motion-wiring.md).
- [#108](https://github.com/VladimirMarko/conaled/issues/108) has an independent
  author archive, a separate evaluation, and a checked direct-Lean comparison.
  Read the [retest evidence index](../agda-transfer-independent-retest/README.md)
  before making authoring claims. The archive was sealed before evaluation;
  evaluator corrections are separate from the author's result.
- [#434](https://github.com/VladimirMarko/conaled/issues/434) assesses what that
  evidence supports. Read the
  [investment assessment](../agda-authoring-investment-assessment.md). The
  successful selected theorem is smaller than the earlier associativity task
  and has no nonempty dependent tail. Neither cycle counts nor build durations
  establish a causal productivity advantage. There is no automatic next
  repair/author trial or broad hand-porting programme.
- [#433](https://github.com/VladimirMarko/conaled/issues/433) remains open.
  The checkpoint contains the ordinary comparison model and its projections,
  generated preservation/composition/equivalence laws, primitive parameter-local
  deformation gluing, independent primitive Čech matching-data identification,
  and a bounded external comparison construction. Read
  [the comparison report](../groupoid-comparison-model.md),
  [generated preservation](../signature-generated-preservation.md),
  [descent prerequisites](../smooth-descent-prerequisites.md), and
  [the source interpretation](../smooth-source-interpretation.md) for exact
  statements and boundaries. These separate constructions do not complete the
  combined source-to-smooth descent obligation.

The final acceptance comment under #235 distinguishes the first checkpoint's
validation from the later combined candidate. Do not reuse a receipt for a
different commit by relabelling it.

## Scheduled continuation

| Owner | Next obligation | Boundary |
| --- | --- | --- |
| [#445](https://github.com/VladimirMarko/conaled/issues/445) | Extend independently specified matching-data identification and effective descent through generated contexts, families and finite dependent tails. | Reuse the primitive Čech identification. Comparing two interpretations alone does not identify one with actual local data. |
| [#446](https://github.com/VladimirMarko/conaled/issues/446) | Prove selected comparison laws through contractions, counits, contextual J and the full generated parameter square. | The outgoing increment stops at external comparison data, primitive cases and comprehension. Root/J and the full generated induction remain work. |
| [#447](https://github.com/VladimirMarko/conaled/issues/447) | Transport matching data and parameter-compatible sections through arbitrary-cover presentations, with a complete two-sheet regression. | An equivalence of cover presentations does not automatically supply section coherence. |
| [#433](https://github.com/VladimirMarko/conaled/issues/433) | Integrate those results with the unchanged source proof and classical effective/ineffective consumers, then satisfy full acceptance. | Keep the parent open until its original combined obligation is fulfilled. |
| [#436](https://github.com/VladimirMarko/conaled/issues/436) | Resume the existing realization-choice checkpoint when the successor is told to continue. | Held during transfer. Preserve the implementation; measurements and final acceptance remain pending. |

#445–#447 are linked subissues of #433, decomposing existing work rather than
expanding its mathematical scope. Primitive construction, generic closure and
final source-consumer integration may have different readiness states; use the
explicit dependencies inside those tickets rather than blocking everything
behind one broad label.

For #436, the preserved checkpoint is
`e15604a98fe8a0c2533679bc6d8f29d0fda7bb7e` on
`work/436-realization-choice`. It contains the shared selection/evidence path,
nested scan and prepared-tree clients, and runtime tests. It is not a completed
delivery. Controlled measurements, full candidate validation, final review
reconciliation and originator review remain. The originator is session
`01a1c20a-c958-7d00-a2b4-efeae402cac6`. Its empirical target is Lean execution,
not an already-demonstrated native-code performance claim. Preserve context
stamps on observations; do not infer unchosen alternatives' performance from
chosen-path observations.

## Decisions to retain

The owner approved the bounded comparison-model route for #433 while retaining
the direct models and an independent implementation route. The common contract
must permit alternatives. There is no requirement to force every implementation
through the comparison model.

Individual comparisons retain their existing strict substitution/section laws.
A comparison between two interpretations can require selected natural
isomorphisms and coherent component isomorphisms. Even a constant base family
rejects universally demanding equality of naturally isomorphic base functors.
The bounded external construction does not justify a general bicategory,
strictification, new source rules, or assumed J-preservation fields.

Retain the equality and observations required by each specification. Distinct
representations may have the same meaning. Some clients require selected paths,
arrows, certificates or correlations; a proof that some witness exists may lose
their required data. State which information a translation preserves or reflects.

Arbitrary parameter restriction need not be invertible or faithful. Recover
supplied local objects without assuming they extend globally. Discrete
deformation-fiber equalities do not establish equality for all groupoid-valued
families. The arbitrary locally surjective-cover bridge remains required;
general hyperdescent and arbitrary higher models remain separate ambitions.

Technical model construction is independent of whether an author trial has a
favorable outcome. #434 consumes the actual evidence, including its limitations.
The owner considers an agent-productivity advantage sufficient for the MVP,
but the current bounded results do not establish that general advantage.

When an important architectural choice remains unresolved, ask the owner
without blocking independent work. An unanswered important question stays
blocked; elapsed time is not approval. Routine implementation choices and
corrections within the authorized scope do not require repeated permission.

## Evidence and operations

The author trial is preserved under
[`experiments/independent-guarded-authoring`](../../../experiments/independent-guarded-authoring/README.md).
Its sealed archive commit is `e2fc23a6ca342354774a75216c3e792f2a452777`;
the validated trial candidate is `ec027e79f612ef1bf21c9968c91639dcfae0f554`.
The independent delivery starts at
`e4f25d61fb2f56570882c872e349b35190cbcd7d`. Preserve the failed attempts and the
first interrupted full validation; they count in the recorded experimental
budget. No further independent trial is authorized by this handoff.

The latest primitive Čech source checkpoint is
`3f27fbcf199fab31f3093bdd7168a5a7299a7df3`; the latest external-comparison
checkpoint is `c44102ed8ca732a98cc861a5ee3d3a7ad710ea27`. Their individual
focused checks do not replace acceptance of the integrated candidate.

Outgoing operational logs and review records were kept in
`/tmp/conaled-resumed-orchestration/`. That is a local recovery aid, not the
durable source of requirements or mathematical results. Use committed reports,
the archived trial evidence, and the tracker acceptance records first. Local
worktree names and agent handles are hints to inspect, not proof of live
ownership. A fresh orchestrator must not assume that old subagents are active
or addressable.

Use the repository's current Nix, review and validation procedures. The outgoing
session serialized full checks and benchmarks and conservatively used two CPUs;
that was a resource precaution, not a mathematical requirement or an established
thermal policy. Keep each project's build outputs private. Follow the existing
integrity-incident procedure for unexpected cache inconsistencies.

Broader research remains tracked under #235 and the repository workstream index.
The [retrospective](../orchestration-retrospective/README.md) and
[semantic-traditions assessment](../semantic-traditions-assessment.md) retain
lessons about combined consumers, authoring effort and discovery bias. Do not
silently discard a direction because it lacks a current library client, or
automatically schedule all adjacent issues as part of this handoff.
