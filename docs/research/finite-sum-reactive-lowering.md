# Finite sums in bounded reactive circuits

[#482](https://github.com/VladimirMarko/conaled/issues/482) adds a finite source
subset with sum introduction and case analysis, a Boolean circuit lowering,
and canonical admission. The generated initialized programs reuse the existing
[finite-circuit service](indefinite-reactive-service.md). Source semantics,
encoding correctness, circuit resources and environmental progress remain
separate contracts.

## Source and lowering

[FiniteSum.lean](../../Applications/FRP/FiniteSum.lean) admits Boolean, unit,
product and finite sum types. Terms have variables, products, projections, let,
injections, case, Boolean constants, not, nand, and a total Boolean test returning
`Unit + Unit`. False selects the left unit; true selects the right. The structural
`Term.source` embedding uses `CategoricalCompiler.Term`; `eval` calls its existing
evaluator. No circuit execution defines source meaning.

We compared a finite-fragment witness over the full categorical syntax with a
local typed subset and embedding. The witness would reuse the original syntax
directly, but require finite-type evidence through every context and binder,
including rejection of arrow-bearing intermediate terms. The local subset makes
those restrictions explicit in its constructors. Its cost is a separate finite
syntax and embedding. It is a bounded frontend, not a replacement universal IR
or a claim to meet the long-term author-interface goal.

[FiniteSumLowering.lean](../../Applications/FRP/FiniteSumLowering.lean) compiles
this subset directly into existing `Circuit` nodes. `lower_correct` quantifies
all terms and all environments, including the extended contexts under let and
both case binders. It proves equality with the encoded existing source evaluator.
`FirstOrderCompiler.compile_sound` does not prove this new lowering; it remains
available to simpler regions unchanged.

Existing `Squares.coproduct`, `copair` and distribution describe semantic sums
and exact representation squares. They do not supply a product-of-bits encoding,
canonical admission, or eager circuit costs. Here `Source.run_correct` reuses
`Progress.Feedback.run_related` after the new structural proof, preserving
ordered outputs and final state for arbitrary lists related by successful
admission. `Source.stream_correct` uses the existing stream transport theorem.
The circuit wrapper is `ReactiveCompiler.Compiled` followed by
`Indefinite.Program.compiled`; no source terms are interpreted at a tick.

## Representation and admission

A sum `A + B` occupies `Bool × (storage A × storage B)`. False is left, true is
right. Both fixed payload slots exist; the inactive slot must be all zero.
Products and nested sums obey the same recursive convention. Thus `Bool +
(Bool × Bool)` has four Boolean cells, six canonical encodings and ten rejected
raw encodings. There is no unused Boolean tag, but there are unused payload
combinations. Canonicality prevents inactive bits from retaining hidden state.

`observe` is a total internal interpretation, selecting only the active slot.
It is not the external admission policy. `admit_iff` says successful admission
of a value is equivalent to exact equality with its encoding. `validator_correct`
connects an executable circuit to that policy; `checkedAdmit_eq` recovers the
same decoder contract. Nested malformed active payloads and nonzero inactive
payloads are rejected.

`Source.tick` validates the external input and retained state with that circuit
before invoking the transition. Failure returns `none` without a new state or
output. It does not normalize bad bits, reset state, or execute the body.
`tick_preserves` proves canonical output and state preservation. The interface
accepts statically typed Boolean products; parsing a byte protocol is outside
this delivery.

## Eager work, space and progress

The scrutinee is evaluated once. Both total case arms then execute, followed by
a componentwise Boolean multiplexer. `caseCircuit_work` is exactly the sum of
both arm costs, the mux cost and 22 wiring dispatches. The checked unequal-shape
example has arm costs 3 and 5, a 25-dispatch Boolean mux, and total cost 55 under
either tag. Selecting one source branch does not make target execution lazy.

The existing circuit arena model counts node dispatches, Boolean value copies
and frames, retaining temporary allocations until tick end. `TickExecutes`
connects the actual admission check and transition evaluation to accepted and
rejected tick costs. `checked_uniform` bounds every allocation prefix, including
the validator arena, transition arena, branch frame and retained state. Runtime
state contains no trace or cumulative counter.

The checked example has these model costs; the declarations in
[Examples/FiniteSumReactive.lean](../../Examples/FiniteSumReactive.lean) calculate
them from the generated circuits:

| Operation | Work | Arena or total space |
|---|---:|---:|
| Lowered transition body | 543 | 4,272 arena units |
| Four-cell sum validator | 85 | 395 arena units |
| Accepted tick, including input/state validation | 641 | 4,736 units including retained state |
| Sum-to-Boolean regional adapter | 61 | 454 arena units |
| Adapter followed by compiled first-order not | 69 | 480 arena units |
| Stateful sum region, compiled not and explicit delay | 619 | 4,891 units including retained state |

The last row is the composed circuit body, before any external admission wrapper;
it must not be compared to the checked-tick row as if both priced the same work.
`pipeline_work` includes both applications of the existing 31-dispatch sequencing
overhead. The one-bit regional boundary needs no sum storage in the downstream
first-order target; the adapter and its intermediates are charged separately.

`checked_ticks` proves that encoded source streams pass admission at every
prefix. `checked_duration` adds validation work and the branch dispatch to the
service-round duration. `checked_productive` reuses the existing backpressured
service theorem with that finite overhead and explicit finite input, scheduler
and sink waits. These are model-level conditional progress and uniform-space
results. They establish no physical heap limit, wall-clock deadline, host
allocation recovery or external acknowledgment guarantee.

## Independent cases and execution

The plain reference transition was frozen and checked before lowering code was
written. State is `Bool + (Bool × Bool)`, initially `inl false`. False input retains
the state. True input changes `inl b` to `inr (!b,b)` and `inr (u,v)` to `inl u`.
The output observes the old state: `b` for left and `!u` for right. Inputs
`[true,false,true,false,true]` therefore produce `[false,false,false,true,true]`
and final state `inr (false,true)`. Resetting state or reversing the branch
selection changes checked observations. `source_reference` connects the embedded
source to that plain oracle; `lowered_run` then applies the general preservation
result.

The following region actually uses `FirstOrderCompiler.compile` for not, then
an explicit initialized delay. Its expected output is
`[false,true,true,true,false]`. `pipeline_run` supplies the arbitrary-list ordered
composition law, including all retained regional states. `regions_admitted`
checks a separate four-cell sum boundary adapter followed by the compiled
first-order region; its assumption is successful canonical admission.

Run the executable checks inside the development shell:

```sh
lake build Examples.FiniteSumReactive
lake env lean --run scripts/test-finite-sum.lean
python3 scripts/test-reactive-service.py
```

The executable check covers all sixteen raw encodings for both state and input
admission, all six native states across every Boolean trace of length at most
five, the corresponding downstream traces, nested rejection and eager work.
These finite checks complement the universal proofs; they do not replace them.

## Regional use and remaining scope

For [#481](https://github.com/VladimirMarko/conaled/issues/481) and
[#485](https://github.com/VladimirMarko/conaled/issues/485), the reusable boundary
is `Ty.storage`, `encode`/`admit`, `lower_correct`, the priced validator, and the
initialized preservation/service contracts. This fragment requires finite
Boolean representations, cartesian circuit operations and the named total
gates. Other regions retain the existing first-order target interface; no shared
target acquires coproducts, closures or effects. The checked adapter is not an
automatic factoring or weakest-requirement algorithm.

Unbounded recursive alternatives and arbitrary payloads need a different
representation/admission argument and a renewed space bound. Higher-order
residualization belongs to #483, bounded folds to #484, and backend selection to
#486. An emitted artifact needs its own simulation and resource contract (#488).
This delivery adds neither a scheduler nor migration; pending-work migration
remains #480. Effectful or partial primitives cannot be added to eager case
lowering without revisiting evaluation-order and validity guarantees.
