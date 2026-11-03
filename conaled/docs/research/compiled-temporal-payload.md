# Compiled payloads through finite temporal certificates

[Issue #215](https://github.com/VladimirMarko/conaled/issues/215) validates the
cross-kind route proposed in the [integration assessment](correspondence-contracts-and-integration.md):
one proof/program interpretation, a relational batch map, and finite delivery
evidence ending in an honest FRP observation. The guarantee preserves related
values and the certificate horizon. It does not turn an arbitrary trace reader
into a causal processor.

## Endpoints and comparison strength

For `R S : Type` and any `E : R → S → Prop`, supply endofunctions `fR`, `fS` and

```
∀ x y, E x y → E (fR x) (fS y).
```

[CurryHowardRelations](../../SquareKit/CurryHowardRelations.lean) constructs
`twiceProof`, the closed singleton-atom proof/program `λf. λx. f (f x)`.
The only formula constructors it needs are the atom and implication. The
primitive family is empty; no scalar operation becomes a proof rule.
`typedCompilation` consumes the accepted Curry–Howard interface.
`compiledTwice E fR` applies its compiled implementation to `fR`, while
`twice_meaning` identifies the semantic interpretation at `fS` with the ordinary
Lean function `twice fS`. `twice_related` specializes the existing
`STLCRelations.compile_preserves` at its full arrow relation. That proof already
uses compiler naturality. It is not replaced by another source induction or a
proof that merely unfolds two applications of `f`.

The direct API is `twice f x := f (f x)`. The optional proof/program retains an
intrinsic term in `Type` and an erased admissibility proposition, as in
[the accepted correspondence](curry-howard-implementation.md). The term is
closed, so its context environment is `()`. Endofunctions are related arguments
to its interpretation, not new primitive symbols. Capture-avoiding substitution
and its interpretation contract remain those of the accepted compiler bridge;
this experiment introduces no additional substitution or source grammar.

The compiler route is at universe zero. The independent
[temporal relation](../../SquareKit/Temporal/Relations.lean) accepts families
at arbitrary universes, including different universes on the two sides:

```
RA n : A n → C n → Prop
RB n : B n → D n → Prop
Until.Rel RA RB : Until A B n → Until C D n → Prop
```

Matching `now` constructors require `RB`; matching `wait` constructors require
`RA` and recursively related tails. Mismatched constructors cannot be related.
Thus every wait is compared at its absolute index, the terminal evidence is
compared at the shared final index, and the horizons agree.
`Rel.horizon_eq` and `Rel.window_horizon_eq` expose that equality.
`Rel.ofWindow` accepts one `k`, `RA` at every `j : Fin k`, and `RB` at `n+k`, then
relates the certificates constructed by the existing `Until.ofWindow`.
The existing `windowEquiv` gives the independent finite-interval presentation;
no replacement temporal datatype is introduced.

## Lifting and composition

`Rel.map` allows independent maps on both waiting and terminal carriers and
requires the corresponding pointwise relation-preservation proofs. `Rel.comp`
composes two such relations through existential intermediate data at each step.
Those existential witnesses remain in `Prop`; they are not used to construct an
executable certificate. `Rel.refl` and `Rel.map_id` provide the equality case.
Certificate map identity, composition and horizon preservation reuse the
existing `Until.map_id`, `map_comp`, and `horizon_map` laws.

[BatchRelations](../../SquareKit/Temporal/BatchRelations.lean) specializes the
terminal relation to `List.Forall₂ E`. `batch_map` retains list order and
multiplicity; `mapBatch` changes only terminal payloads. `mapBatch_related`
transfers a scalar preservation proof to the certificates. `mapBatch_comp`
identifies two successive maps with the composed scalar map. `batchSquare`
packages the guarantee as a `RelSquare`, and `batchSquare_comp` proves that
pasting the squares agrees with composing the payload functions. This layer
requires no compiler imports.

The generic integration theorem `compiled_batch_related` in the
[checked examples](../../Examples/CompiledTemporalPayload.lean) supplies
`twice_related` to `mapBatch_related`. It accepts arbitrary waiting families,
related certificates, heterogeneous scalar carriers and an arbitrary relation.
It establishes forward relation preservation, not reflection or full abstraction.

## Honest FRP observations

[TemporalPayload](../../Applications/FRP/TemporalPayload.lean) consumes explicit
`Arrival s ms a t n` data. `mapPayload` first calls the existing `correct`, which
uses `Demand.responseSquare` under `(traceRep ms).Rel s truth`, then maps its
terminal batch. Its output is an `Until` certificate whose terminal subtype
records

```
out = List.map g (truth .left t ++ truth .right t).
```

`mapPayload_horizon` preserves the supplied horizon.
`mapPayload_value` exposes the external observation, and `mapPayload_output`
connects it to mapping the original certificate's terminal list. Neither list
order nor duplicate occurrences are quotiented away. The mapped certificate
has a certified payload; it does not claim that the unmodified machine emitted
those new values.

This adapter requires no fairness assumptions because the supplied arrival
already contains finite evidence. Obtaining it through `searchArrival` still
requires explicit fuel and a registered pending request. The examples reuse
`arrival_has_fuel` for its existential success proposition. The existing
`eventual_arrival` retains delivery fairness, processing fairness and source
progress premises when deriving `Nonempty` existence. No program, witness or
horizon is selected from that proposition here.

## Cases and deliberate losses

The examples include successor as the shared program's argument, giving `x+2`,
and doubling as a second argument, giving `x*4`. The relation
`tagged x y := x = y.1` relates a natural number to either Boolean-tagged version.
It is nonfunctional in that direction. The successor implementation flips tags;
the doubling implementation retains them. Both satisfy their scalar obligations.

A two-wait certificate ending in `[1,1,2]` is related to a tagged batch. Applying
the compiled successor-twice program gives `[3,3,4]` at horizon 2; composing the
second program gives `[12,12,16]`. Empty batches at horizon zero, explicit
window construction, and relational composition are also checked.
The honest FRP fixture maps the delayed batch `[3,4,3]` to `[5,6,5]` at horizon 4.
A late zero-wait witness and a known-empty emission exercise the same adapter.

Two other explicit certificates both end in `[7,7]`, with horizons 0 and 1.
`horizon_lost` proves that no function of the terminal list recovers the horizon
for every certificate. This does not contradict the accepted first-arrival
search: these are unrestricted unit-wait certificates, not two outputs of that
search for the same trace, starting index and fuel. The examples also reuse
`shift_not_synchronous`, the existing future-reading stream counterexample.
Value preservation of a certificate map supplies no synchronous-causality proof.
A separately supplied pointwise Mealy consumer may use its existing causal laws;
this experiment constructs no online scheduler or physical deadline.

## Authored content and bookkeeping

The direct scalar client contains two function applications. The optional source
proof contains two implication introductions, two eliminations and three
hypothesis occurrences. Two hypothesis indices refer past the newest variable;
the third selects it. Explicit context/formula annotations resolve elaboration.
These indices and annotations are bookkeeping, not additional mathematics.

There is one shared closed proof/program and one generic compiler relation proof.
The empty primitive package has two impossible cases, with no per-model primitive
obligation. Each supplied function pair needs one scalar preservation proof;
the checked nonfunctional example supplies two, one for increment and one for
doubling. No new source induction is needed for their composition.

The temporal side adds one two-constructor relation, its structural preservation
lemmas, and one batch-lifting interface. The window adapter has two local
index-transport steps, for waiting and terminal data. These casts reconcile
`n+(j+1)` with `(n+1)+j`; they add no temporal assumption. The integration theorem
is one application of batch lifting to the compiler theorem. FRP adds one adapter
and three comparison lemmas, reusing the existing honesty contract and search.
These are actual construction/obligation counts, not estimates of saved time.

Ordinary clients can import `BatchRelations` and use `twice`-shaped Lean functions
without syntax. The optional compiler client needs `CurryHowardRelations` and
the same scalar obligations. Both paths keep certificate data in `Type` and
correctness evidence in `Prop`. The result makes no resource-improvement claim;
ADT abstraction and cost contracts remain with #210/#211, and actual transition
instrumentation with #193.
