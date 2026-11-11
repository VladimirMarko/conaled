# Measured callbacks: reconciled assessment

Test generalization of the existing measured traversal before adding an owner. Preserve `Resources.Measured`, workload execution and exact list-cost operations. Compare explicit recursion with native traversal on two concrete consumers, with the event schedule and structural charges fixed in advance. A broader observation framework is not justified by the present evidence.

All three assessments inspect source `e80c51d968925be3809ba3acc3259de7041b504b`. Their initial versions remain unchanged. No proposed renderer or measured permutation executor was implemented or checked in this challenge.

## A source-inventory correction

The contract lens found an existing varying-callback traversal outside the resource directory. `StructuredLinear.Costs.traverse` in `Applications/Linear/StructuredCosts.lean` accepts measured callbacks, preserves list values and accumulates their returned observations. Its `traverse_value` and `traverse_cost` prove both projections. `denseStage` in `Applications/Linear/StructuredMeasured.lean` and the workload callers in `Examples/StructuredLinearCosts.lean` consume it.

The coordinator inspected these definitions and callers. The other reports' narrower searches for names such as `mapMeasured` did not find this owner. Their search results must not be promoted into a claim that varying-callback traversal is absent. The operation is specialized to structured-linear event counters and has no independent structural list charge. Generalizing its mathematical shape, preserving its clients and adding a declared source-price specialization is therefore a concrete candidate. It does not already solve ordered event tracing, delayed observation or the proposed counter/permutation clients.

## Existing algebra and new operational choices

`Measured.bind` already sequences observations without commutativity. Existing workload execution admits state-dependent bills; only a particular observation theorem requires command-independent observations. Counter transitions should retain their current owner and full measured-pair correspondence. Rendering seed-inclusive states is a separate consumer, not another counter execution.

The common map laws should be derived from a selected recursion: value erasure, exact observation accumulation, constant-price specialization, congruence and additive reweighting. No equality test on payloads or uniform callback-price assumption is needed. Duplicate occurrences must remain duplicated. Structural charges, including terminal dispatch, define an additional operation convention; they are not missing laws of the uncharged traversal.

The native `List.mapM` alternative deserves the same trial. The alternatives lens inspected the pinned Lean definitions and lawfulness hypotheses. Its accumulator/reversal implementation can carry declared source charges, but those charges do not automatically measure native reversal or allocation. Avoid introducing a broad `Prod` instance merely to obtain this comparator.

## Trace equality is stronger than scalar equality

All lenses identify a limit on generic fusion. Two map phases can emit `f1,f2,g1,g2`; an interleaved composition emits `f1,g1,f2,g2`. Equal Nat totals do not establish equality in an ordered observation monoid. Existing scalar fusion results remain valid in their stated scope. Generic interchange needs a changed statement or explicit commutation assumptions.

ConcatMap similarly needs a declared schedule. Map-then-concat and interleaved callback/append execution can differ in event order while agreeing on values and scalar bills. Reuse actual append execution when its schedule fits. Do not reconstruct a richer trace from an already collapsed scalar charge.

Construction of delayed payloads, forcing them, and observing their inner spines remain separate operations. A thunk provides no cache transition; invoking it twice contributes its measured bill twice. The recovered complete-observer formula and existing append-based concat formula describe different observations, and any callback bill must be included explicitly. The demand/sharing challenge owns the cache and partial-progress questions; this traversal experiment should not silently select that architecture.

## Two-consumer comparison and acceptance evidence

1. Use actual counter states and an independent token renderer with nonuniform bills. The proposed five-state fixture has callback bills `[1,2,3,3,4]`. Under the explicitly proposed unit dispatch/cell tariff its total is 24. Check tokens, line boundaries and ordered callbacks, and distinguish rendering five states from executing four transitions. Include noncanonical equal-valued representations with different rendered lengths.
2. Use positional permutation outputs with duplicate values and exact order. The proposed selection fixture on `[1,1,2]` has six outputs and callback bills `[2,2,2,2,3,3]`; its proposed same-tariff total is 27. These are manually calculated test expectations, not new checked results. A separate recursive generator test must retain removal, append, termination and adequate-fuel complete-pair obligations.
3. Construct and outer-count delayed labels without callback events, then fully observe actual inner payloads, including empties. Retain callback costs and terminal inner observations. Repeat a nonzero-cost thunk and retain both charges; allow function-valued payloads.
4. Test noncommutative traces on distinct inputs as well as duplicates. Preserve intentionally different two-phase and interleaved schedules. Prove exact correspondence only when the schedules match.
5. Compare local recursion, a generalized existing traversal and native `mapM` on the same contracts. Preserve structured-linear callers and the old uniform-price map through appropriate complete-pair specializations. Record recurring inductions, termination adapters and caller obligations; a name change or lower line count is not reuse evidence.

These experiments decide whether the common owner should provide only uncharged traversal or also a shared structural-price specialization. They do not require replacing existing resource primitives or committing to a general evaluator.

The [contract](contract.md), [implementation/use](implementation.md), and [alternatives/generality](alternatives.md) reports and [brief](brief.md) record inspection and exposure limits. Fresh contexts and undisclosed initial reports provide process independence without model diversity. The coordinator retains the minority inventory finding and resolves it against actual consumers. No new Lean proof, build, benchmark or author-effort trial was run; architectural adoption remains for owner discussion.
