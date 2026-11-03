# Bounded monitoring of FRP observations

Issue [#207](https://github.com/VladimirMarko/conaled/issues/207) implements the
bounded monitor selected by the [temporal assessment](research/temporal-logic-frp-contracts.md).
A formula has decidable frame atoms, negation, conjunction, next and bounded
until. This property grammar is separate from the proof-relevant certificate
fragment; the two share actual FRP observations through the frame adapter. Its monitor returns `pending` until a conservative observation horizon
is complete, then returns `satisfied` or `violated`. Neither terminal verdict
asserts that the input stream has ended.

## Formula and verdict semantics

[Temporal.Monitor](../SquareKit/Temporal/Monitor.lean) is independent of FRP.
`Formula.Sat` interprets formulas on infinite observation traces. An atom is a
supplied Boolean predicate of the current observation. Next advances one index.
`untilWithin h p q` holds when some `k ≤ h` satisfies `q` and every earlier
`j < k` satisfies `p`. Its waiting interval excludes the terminal position.

The structural horizon is zero for an atom, unchanged by negation, the maximum
for conjunction, one plus the child horizon for next, and
`h + max p.horizon q.horizon` for bounded until. Nested formulas therefore
retain the lookahead their terminal and waiting subformulas require.

`evaluate` is an executable Boolean recursion using bounded ranges and optional
observations. It gives missing entries a provisional value; that value alone
is not a verdict. `evaluate_correct` proves agreement with independent
infinite-trace satisfaction when all entries through the horizon are supplied.
`sat_prefix` shows that changes beyond that horizon cannot affect satisfaction.

A monitor state stores at most `horizon+1` frames. `step` appends a frame and
retains that initial window; `run` folds the transition over supplied input.
`run_entries` identifies the stored window with the corresponding list prefix,
and `run_append` proves composition over concatenated input. Once the window is
full, `step_full` and `terminal_absorbing` retain the state and verdict.

`run_complete` identifies both terminal verdicts with satisfaction or its
negation after enough observations. `run_sound` applies to every infinite
extension of an observed prefix, without asking callers to provide a horizon
bound first. `run_pending` explicitly retains uncertainty on every shorter
prefix. This construction need not recognize an early decisive prefix as soon
as possible, and it does not decide unbounded LTL.

The retention theorem counts stored frames. Payload lists inside frames can
be arbitrarily large. The theorem is not a byte, allocation, source-log or
runtime complexity bound. Atoms must be supplied as executable functions for
an executable deployment; none is inferred from an arbitrary proposition.

## Connection to actual FRP traces

[FRP.Monitor](../Applications/FRP/Monitor.lean) reuses the
[finite-certificate adapter](temporal-frp.md)'s `Frame`, preserving request,
observation and emission as distinct fields. Atoms test pending query,
certified readiness, emission presence and an exact emitted answer.
The answer atom additionally requires decidable payload equality.
`observed = none` is a known fact about current knowledge, not a false assertion
about the source event. `some []` is a known empty batch.

[TemporalMonitor examples](../Examples/TemporalMonitor.lean) exercise the
existing rational-time demand machine:

- From processing state 1, the early query for timestamp 2 emits `[3,4,3]`
  four steps later. Bound 4 is satisfied after five frames; bound 3 is violated
  after four frames. Four frames remain pending for the bound-4 formula.
- Query 1 emits the known empty batch. Its exact-answer atom is satisfied;
  at the next position no second response occurs, while knowledge remains ready.
- Before closing packets arrive, a not-ready atom holds even though the eventual
  source truth contains `[3,4,3]`. Knowledge and source-event truth are distinct.
- An inserted idle step delays the emission by one processing position. An
  inserted rejected packet also delays it, although that packet leaves the
  entire source state unchanged. Bound 4 then fails and bound 5 succeeds.
- Merging input chunks, absorbing terminal verdicts and the five-frame retention
  bound use the generic public laws, alongside semantic soundness applications.

`observed_persists` reuses `Trace.run_persists` to preserve an already certified
answer under later source processing. That observation law does not make next
or step-bounded formulas invariant under inserting processing steps. An emission
atom is also transient in the one-shot demand protocol. Equal observations
through a formula's horizon preserve satisfaction; general time reindexing is
not part of that contract. No source fairness or liveness hypothesis is needed
to judge a supplied bounded trace.

## Source justification and excluded claims

[Bauer, Leucker and Schallhart, *Monitoring of real-time properties*, §§1–3](https://www.pspace.org/a/publications/fsttcs06.pdf)
justify conclusive finite-prefix verdicts by quantifying over infinite
continuations and distinguish them from an inconclusive result. Their automata
construction recognizes decisive prefixes as early as possible. This monitor
instead waits for a structural horizon; its own correctness proof is
`evaluate_correct` followed by the state-window and verdict theorems. It does
not implement their full untimed or timed logic, optimal automata construction,
or a timed-clock interpretation.

[Vardi and Wolper](https://www.cs.rice.edu/~vardi/papers/lics86.pdf) connect temporal
formulas to automata for model checking concurrent finite-state programs.
That result is background for a future automata route, not the proof of this
bounded evaluator. No automata or controller-synthesis backend is introduced.

The checked `unbounded_undetermined` theorem gives two infinite continuations
of every finite silent Boolean prefix: one never emits, the other emits later.
No observation of that prefix decides unbounded eventuality. Separately, the
specification `output n = input (n+1)` has satisfying complete traces but no
synchronous causal implementation for unrestricted inputs. The examples prove
both existence of complete solutions and failure of a causal implementation.
Monitoring is therefore not reactive synthesis.

A future automata backend would need a chosen logic, finite alphabet abstraction,
language/observation preservation and an execution contract. A synthesis backend
would additionally need controlled actions, admissible environments and a
winning-strategy theorem. Neither is required by the demonstrated consumers.
[#27](https://github.com/VladimirMarko/conaled/issues/27) and
[#31](https://github.com/VladimirMarko/conaled/issues/31) retain runtime ownership;
[#196](https://github.com/VladimirMarko/conaled/issues/196) retains interaction
and fault contracts. This monitor changes none of those obligations.
