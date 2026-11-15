# Executable finite univalence transports

The direct interface accepts executable forward and backward maps with proofs
that they realize a supplied equivalence. The optional typed recipe interpreter
supports identity, a supplied primitive, sequential composition and reversal.
Neither interface evaluates the noncomputable cubical model.

`Applications/Representations/ExecutableTransport.lean` contains the executable
adapter and interpreter. `Examples/ExecutableUnivalence.lean` connects their
observations to the actual native constructions and runs the finite machine.
The [design challenge](design-challenges/2026-11-15/executable-univalence/synthesis.md)
retains all three independent assessments and their evidence limits.

## Native endpoints and complete package

`forward_native` uses `CubicalNativeUnivalenceTransport.observedNative_eq`.
Its right side decodes transport on the actual constructed native ua line.
`backward_native` uses the selected reverse transport of that original path,
through `CompositionalUnivalence.observedInverse_eq`. `composition_native`
uses the actual selected concatenation of the two supplied equivalence paths.
It does not substitute ua of their composite as the named semantic target.

The bounded examples are Boolean negation, a direction-sensitive cycle on
`Fin 3`, and the existing `Fin 3`/`Phase` machine. The cycle sends 0 to 2;
its inverse sends 0 to 1. The two constituent swaps also detect reversed
composition order. The interpreter is typed at both ends, so it can realize
the machine's change of carrier as well as endomorphisms.

`full_package_recovery` reuses the whole native package equality from #530.
That package contains the initial state, transition, invariant, and its initial
and preservation proofs. `run_native` connects every finite command list and
every starting state to the transition selected by that actual native package.
`executeMachine_native` includes input conversion, every intermediate numeric
observation, the final state, and the returned observation order. The invariant
law retains its explicit initial-validity premise. Tests also execute the
failed state, which is outside the valid reachable subset.

The numeric observer distinguishes all three states. Invariant preservation
is a theorem about the proposition-valued field; the implementation does not
claim to execute arbitrary proposition-valued invariants. The existing wrong
presentation is retained as `wrong_adapter_rejected`: fixing the initial point
is insufficient to preserve the transition.

These observation theorems do not recover arbitrary proof-relevant native
witnesses from executable values. The semantic admission uses the supplied
ordinary equivalence and its existing `ofIso` witness. It does not replace the
more general fixed-witness #530 interface or claim a new model interpretation.

## Declared execution and storage model

The measured operations use the existing `Resources.Measured` and
`Resources.run` APIs. A named primitive conversion, source machine step,
numeric observer, observation-list cons, and final state export each cost one
source event. The conjugated step actually calls the inverse conversion,
source step and forward conversion. Its numeric observation and list
construction are charged separately. The final list reversal costs one event
per returned cell.

A recipe visits and charges each syntax node, including identity and reversal,
and charges each primitive call. `execute_cost` proves the exact bill in both
directions. `prepared` computes the node count as a fresh setup scan and charges
it before interpretation. Recipe storage means its declared syntax-node count;
it does not bound the representation or captured environment of an arbitrary
primitive equivalence. Primitive-call tariffs are explicit supplied-model
assumptions, not costs inferred from an opaque function.

The direct machine pays one setup event and one input conversion. The syntax
machine uses the one-node primitive presentation recipe, pays its one-node setup
scan, and charges dispatch on each conversion, including initialization. Both
return the same intermediate observations and final state, with the same
observation schedule. The exact totals for n commands are:

| Route | Complete declared work | Zero | One | Eight |
| --- | --- | --- | --- | --- |
| Direct supplied presentation | 3 + 6n | 3 | 9 | 51 |
| Interpreted primitive presentation | 4 + 8n | 4 | 12 | 68 |

The generic cost theorem retains the setup and conversion tariff as parameters.
`syntax_extra_work` proves the difference is 1 + 2n on every input. This
experiment supplies no benefit from interpreting the syntax. Direct composition
uses measured bind and keeps all component bills. The cycle followed by its
inverse returns the input but its unprepared recipe costs six events. This
agrees with the existing same-value/different-cost rejection in `Measured`.
The existing parser workload's short-use and repeated-use preparation controls
remain imported and checked; their optimization result is not transferred to
this different client.

There is no retained conversion table, memoization, or mutable cache. The
representation choice and recipe are immutable inputs; every new call pays its
setup again. The runner retains its current state and observation list because
those are returned outputs. No zero-cost update or cache-invalidation guarantee
is claimed. Host allocation, garbage collection, closure layout, compiler work
and CPU instruction counts are outside this source-event model. Complete
accounting here means all named events of that model, not complete physical
machine costs.

## Dependency and execution boundary

The selected native ua, inverse and package constructions remain noncomputable
specification terms. Executable functions call the supplied finite maps,
transitions and observers, together with measured bind and run. They do not
call native decoders, fillers, `admittedCarrier`, or choice-based extraction of
a permutation from a loop. The direct adapter remains usable without syntax.

A targeted `#print axioms` audit was run for `directMachine`, `syntaxMachine`,
`runtimeTests`, all three endpoint bridges, `executeMachine_native`,
`full_package_recovery`, and `executeMachine_cost`. Each reports only `propext`,
`Classical.choice`, and `Quot.sound`, including the executable declarations:
their transitive Lean declarations also include proof-bearing equivalences and
packages. This is not evidence that a runtime choice oracle is executed, nor
an axiom-free claim about those declarations. Their computable data definitions
and successful execution are separate evidence from the logical dependency
report. The full repository audit remains the acceptance check.

Lean's compiler and runtime, proof erasure, and the host execution environment
are trusted for the observed execution. No theorem here verifies their
implementation or proves general cubical normalization, canonicity, binary
serialization, physical allocation, or a Wasm artifact. Backend issues remain
separate and deferred.

## Checks and remaining investigations

`runtimeTests` executes both Boolean inputs, every cycle input in both
directions, positive-cost cancellation, and all three machine states at zero,
one and eight commands. It checks expected final states and every numeric
observation, matched direct/interpreted outputs, exact declared work, and
noncommuting-order controls. These tests supplement universal native refinement,
workload, invariant and cost proofs; they do not replace those proofs.

A separate successful `lake env lean --run` invocation of `runtimeTests`
used the pinned Lean 4.35.0 environment, CPU 0 and nice level 10. It took
0.989 seconds elapsed, 0.636 seconds user CPU and 0.323 seconds system CPU,
measured after acquiring the shared build lock. These are one-run harness
measurements, including environment and Lean startup, on the throttled laptop.
They do not compare the two implementations' runtime performance and do not
validate the source-event tariffs.

The direct route is the current recommendation. Tabulation, source-coordinate
batch execution, and recipe normalization may reduce work for other workloads,
but each needs its own executed algorithm, preserved observation schedule and
complete preparation/storage/update account. A broader evaluator requires a
named additional source fragment and operational correctness evidence. None is
adopted by this bounded delivery.
