# Finite temporal certificates and FRP observations

The experimental #206 fragment implements the finite next/until proposal in
[the temporal assessment](research/temporal-logic-frp-contracts.md). It connects
proof-relevant arrival evidence to the existing one-shot demand reference
machine. It supplies neither a guarded recursive language nor an FRP scheduler.

## Direct certificates and optional syntax

[Temporal.Finite](../SquareKit/Temporal/Finite.lean) defines `Until A B n` in
`Type`, with `now` and `wait` constructors. Its horizon `k` describes waiting
evidence at every processing index in `[n,n+k)` and terminal evidence at `n+k`.
`windowEquiv` identifies the inductive certificate with that finite interval
of data. Zero waiting requires only terminal evidence. `Eventually B` uses
unit waiting evidence. `no_terminal` rules out every finite certificate when
terminal evidence is impossible.

`fold` eliminates a certificate into another indexed family. `map` changes
waiting and terminal interpretations; identity, composition and horizon
preservation are checked. Clients can construct and consume these ordinary
Lean values directly.

[Temporal.Syntax](../SquareKit/Temporal/Syntax.lean) adds an optional fragment:
atoms, unit, products, next and until. Contexts list absolute processing indices
and formulas. Variables retain their occurrences, including repeated entries.
`nextI` needs evidence at the next index; it cannot manufacture future data.
The interpreter maps until into the same direct certificates. Substitution
preserves indices and formulas, satisfies identity and composition, and
commutes with interpretation through `Term.eval_subst`. There are no binders,
implication, general recursion or guarded clock rules in this fragment.

## Demand adapter and bounded search

[FRP.Temporal](../Applications/FRP/Temporal.lean) fixes a query timestamp `t : T`
and indexes evidence by processing steps `n : Nat`. These are separate domains:
advancing the processing index need not advance any source frontier.

- `Frame` retains the pending request, current observation and emitted response.
  `frame_comparison` connects an emission to its pending request and observation.
- `Pending` stores the pending-request equality. `Delivered` retains an actual
  list and its emission equality. `Arrival` waits in the former and ends in the
  latter. `some []` is successful known silence; `none` is no response.
- `correct` maps terminal evidence using `Demand.responseSquare`. Its `traceRep`
  premise includes initial validity, initial truth completion and honest source
  messages. `eventual_correct` combines that comparison with conditional progress.
- `eventual_arrival` reuses `Demand.eventual_response`. Its premises are a pending
  request, available strictly closing prefixes, fair source consumption and
  fair enabled processing. The conclusion is `Nonempty Arrival` in `Prop`.
  The proof's least-index selection is not an executable extraction interface.
- `searchArrival` recurses on supplied fuel and trace observations, constructing
  a certificate in `Type`. `searchArrival_search` compares its horizon and output
  with the existing `Progress.search` machine. `search_spec` proves success is
  the first response at or after the starting index, with cost `j-n+1`.
  `search_complete_at` supplies an operational evaluation for a first response;
  `Progress.search_complete` then applies to any sufficient fuel.
  `arrival_has_fuel` proves that a certificate implies some successful finite
  search. None of these results supplies a uniform deadline.

The typed search follows the same transitions as the shared evaluator while
building the dependent witness structurally. It does not eliminate an
operational proposition into runtime data or call `Classical.choose` for data.
Its trace input is supplied; this is not a search that schedules a live source.
Atomic search cost excludes the cost of recomputing reference trace prefixes.
There is no retention, allocation or wall-clock bound.

## Causality and finite delivery

[TemporalCausality](../Applications/FRP/TemporalCausality.lean) defines synchronous
causality by equality of output prefixes whenever equally long input prefixes
agree. The generic processor delivery theorem implies this property when its
input demand is at most the output prefix length. Mealy processors satisfy it
and retain their existing finite delivery bound. The total shift function
fails this synchronous contract because its first output reads the second input.

`response_prefix` also proves locality of the reference trace itself. Equal
actions through step `n` and equal source messages at indices below `n` give
equal responses at `n`, for the same initial state. This sufficient bound is
not claimed minimal. It requires no fairness or honesty.

The [checked examples](../Examples/TemporalFRP.lean) retain ordered duplicates,
zero waiting and zero fuel, a four-step wait, known empty output, post-delivery
silence, satisfiable scheduling and truth premises, stalled and unfair traces,
and a source-availability/fair-consumption distinction. The optional derivation
and direct certificate interpret to the same early-arrival witness. Mapped
responses and an emission-count scan reuse and compose existing Mealy delivery
proofs. Filtering away absent responses is not productive without progress.
`Event.never` has no finite occurrence certificate, although it remains a valid
denotational event.

## Statement review

The terminal index is excluded from the waiting interval; the finite-window
inverse laws preserve data, not only existence. Formula substitution preserves
absolute indices. Progress hypotheses describe available messages and scheduling,
not the desired response; the rational-time examples discharge them independently.
Strict frontier closure, order and duplicates are preserved. Truth comparison
has its own honesty premise, with an accepted but dishonest observation as a
negative case. Causality concerns dependence on prefixes; finite delivery concerns
the explicit machine and supplied inputs. Neither is promoted to unrestricted
stream equivalence, infinite response delivery or an FRP runtime claim.
