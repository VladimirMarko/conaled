# Tracked lifting, interaction hiding and observation contracts

This fifth-wave synthesis under [#235](https://github.com/VladimirMarko/conaled/issues/235)
follows the [fourth wave](semantic-traditions-fourth-wave.md). The bounded #386
lifting and #390 interaction implementations have passed independent ticket
reviews. Combined integration acceptance remains external to this report; the
full #371 internal selected-solution provider remains open.

The accepted [lifting report](assembly-lifting-monad.md) and [interaction report](finite-interaction-strategies.md) address different obligations. Lifting retains a dependent base through partial computation. Strategy interaction exposes matching and hiding of intermediate moves. Neither construction requires replacing ordinary client interfaces with a common semantic representation.

## Lifting retains a base even when computation is undefined

#386 supplies tracked multiplication for program lifting, the ordinary Mathlib monad, a monad in each assembly slice, and coherent comparisons under tracked change of base. Multiplication generates a program that runs the outer program and then the returned inner program. Both outer divergence and a returned divergent program represent bottom. Equality compares underlying assembly maps; it does not equate program indices or execution cost.

For a tracked family p:A→B, the slice lift consists of pairs (b,t) with t:L A and every defined value of t lying over b. Bottom therefore exists over each base, even when the original fiber is empty. Pulling ordinary Lp back along the unit B→LB would instead require `some b = Lp t`, which excludes bottom. The checked negative control prevents those constructions from being conflated.

The slice comparison uses P1's admissible partial-map classifier to recover and reclassify the selected partial value. Its graph retains the new base and the original selected value. Identity/composition coherence, naturality, and unit/multiplication compatibility connect successive changes of base. A natural isomorphism also connects the computed pullbacks to Mathlib's chosen pullbacks, so this presentation does not impose a separate slice interface on later clients.

The examples include both kinds of nested bottom, selected 17, two nonidentity base changes, and an undecidable halting domain retaining its selected index. These support a concrete dependent partial-computation boundary. They supply no iteration object, complete certificate family, state algebra or selected solver. A slice monad is not a theorem that every slice object is complete, and ordinary categorical initiality alone does not supply a uniformly tracked family of folds.

## Interaction composition exposes a different structure

The #390 construction freezes a finite query loop before constructing its strategy model. A responder may inspect prior replies and may leave a query unanswered. The observation retains the full service history and the selected return or pending result. Its handler comparison uses the existing retained-exception tree, fold and algebra, including an arbitrary prior history prefix. An unanswered query remains recorded; pending completion does not imply that no operation occurred.

The alternative model uses a four-phase forwarding component and actual A/B/C interaction events. Intermediate B events are shared by adjacent components. Local transition proofs establish both component projections. Hiding removes B moves, and a converse construction inserts matching intermediate moves into every external relay play. The exact composition theorem therefore covers the finite-play language of this serial response-policy family, including prefixes, rather than only a displayed completed run.

Identity and associativity hold at the hidden external-play boundary. Differently associated internal labelled traces are not equated. Adaptive service replies remain raw in the service observation, while forwarding policies may transform the selected returned value. This separates the channel-composition theorem from the exact comparison with the independently specified native loop and retained handler.

The construction follows AJM's interaction/projection/hiding organization and compares its discipline with Levy's well-bracketed plays, as documented in its source report. It does not construct general AJM strategies, pointer arenas, exponentials, a higher-order interpretation or full abstraction. In particular, its arbitrary history-dependent environment is not claimed to be an AJM history-free strategy. Its source correspondence is restricted to those definitions and this serial model.

## Coarser observations can be intentional

Once and twice querying a constant responder can produce equal final Booleans with different histories. The construction tests this distinction through malformed duplicate/cached forwarding traces and an unmatched intermediate reply. Those controls fail the exact protocol or selected-history contract even when a chosen returned value agrees.

A separate quotient deliberately identifies clients that agree on returns for every constant responder. The once/twice distinction disappears there, and constant-return observers descend through the quotient. The construction also proves that exact-history and adaptive-reply observers cannot descend. This is a legitimate smaller observation contract. It is not an error merely because it discards a distinction retained elsewhere, nor is it a congruence theorem for a higher-order language that has not been constructed.

The architecture should expose which observation a client requires. Retained histories support the protected-operation clients; hidden channel plays support this strategy-composition comparison; constant-return observations support the stated quotient. None of these mathematical records independently validates a physical adapter, crash persistence, fairness or concurrent scheduling.

## Continuation and disposition

Continue #387–#389 under #371. #386 closes the generic monad/change-of-base prerequisite; it does not close the promised internal selected-solution provider. #387 owns iteration objects and the conditional selected fixed-point construction. #388 owns function assemblies, concrete completeness and the uniformly realizable certificate family. #389's family-specific algebra and solver remain after those constructions. The independent external selected-certificate client remains a comparison, not a replacement for the internal instance.

The [#388 proof roadmap](assembly-cut-continuity-roadmap.md) proposes recursion-theorem proofs of cut monotonicity and finite observation, followed by a uniform extension compiler for N/LN. These are unformalized derivations. The all-context completeness requirement and its eventual equivalence to a tracked exponential restriction isomorphism remain acceptance obligations. No source theorem about internal Eff logic has become an assembly theorem through this roadmap.

For #390, retain the existing handler as the ordinary finite-query interface. Retain the bounded strategy model as an account of channel matching and exact hiding. It answers the newly relevant games re-entry probe without justifying universal strategy adoption. The native route pays for a loop/handler comparison; the strategy route additionally pays for protocol phases, projections and converse path insertion. Its reusable laws cover the stated policy family, but no measured authoring or runtime advantage has been established.

Higher-order or overlapping-query interaction remains with #196/#36, with #290 owning observation and interpretation comparisons. A future client must determine legal contexts, synchronization, bracketing and observations before any stronger adequacy or full-abstraction claim. Routine proof difficulty in #387/#388 is not evidence for changing the model; an incompatible required premise would need a separate architectural assessment.

## Selection bias and residual owners

This wave favors explicit finite histories and exact selected outputs. That helps detect lost queries and selected-data mistakes, but it can undervalue intentional quotients and models whose clients require only truth or support. Conversely, a short native loop can conceal the cost of repeated interaction-composition proofs. Count construction and maintenance costs on both sides before claiming productivity gains. The current experiments provide mathematical coverage, not such a measurement.

The query-count, pending-query and adaptive-reply controls discriminate errors that a constant returned-value test cannot detect. Policy cancellation alone is a weaker control because algebraic coincidences can hide composition-order errors. Exact universal composition and unmatched-reply checks carry distinct evidence. Preserve that distinction when choosing further maintenance examples.

Other residuals retain their owners: #289 covers arbitrary dependent binding and, with #36, modal/higher combinations; #290 covers dependent relational transfer beyond the existing graph-like clients. #200/#36/#235 retain general probabilistic sequencing and its model hypotheses. #27/#36 with #288 retain analytic hiding and nonconstant-port dynamics. #196/#225 retain physical correspondence and durability; #193 and #174 retain resource/quantitative comparisons. #290/#196 retain higher-order support and general classical extraction. #289/#290 and #100/#36 retain source/model admission under the existing gates; no quantified transfer chain has been supplied by these bounded constructions.

Matching logic still needs a selected pattern-admission consumer, local universes a named model requiring strictification, and general conversion import a chosen conversion/termination consumer. These remain reasons for targeted deferral, not dismissals of those traditions. #107 stays paused, #108 remains unselected, and #260 inactive. The fifth-wave evidence supports continuing the promised SDT work and retaining the bounded interaction comparison; it establishes no generic architectural winner.
