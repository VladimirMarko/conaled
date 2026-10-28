# Reusing FIFO client proofs across representations

The operation-only client in [AbstractFIFO](../../Applications/Sequences/AbstractFIFO.lean)
works with ordinary lists and the existing symmetric lists. Its public interface
contains `empty`, `snoc`, `tail`, and `head`. `Simulation.client_eq` proves that
any finite word of enqueue/delete operations followed by a head observation
returns the same answer from related states. The theorem is quantified over the
word and both implementations; callers do not prove it again for each queue.

This is the bounded representation-independence experiment selected by the
[Harper assessment](harper-methods-and-adaptation.md), implementing
[issue #210](https://github.com/VladimirMarko/conaled/issues/210).
The source motivation is relational representation independence in
[Logical Relations as Types](https://arxiv.org/abs/2010.08599) and the separation
of abstract behavior from implementation detail in
[Abstraction Functions as Types](https://arxiv.org/abs/2502.20496).
The Lean result below uses existing relational squares. It establishes neither
full parametricity for arbitrary Lean programs nor a modal fracture/gluing model.

## Public obligations and reuse

`Ops α Q` contains executable operations only. The separate proposition
`Simulation a b rel` requires related empty states, preservation by enqueue
and delete, and equality of head observations. The relation can be partial or
nonfunctional. It needs no chosen inverse, equality of concrete states, or
cost structure. All ordinary clients execute without a proof argument.

For symmetric lists, the existing relation is
`Inv q ∧ fromSL q = xs`. The invariant restricts the two-list layouts so that
the existing operations preserve the intended sequence. `symmetric_correct`
packages `inv_nilSL` and the existing `snocSquare`, `tailSquare`, and
`headSquare` from [Observation](../../Applications/Sequences/Symmetric/Observation.lean).
The implementation and its operation laws are unchanged. `lists_correct`
uses equality on lists.

`Simulation.runSquare` pastes operation squares using `Relational.compose`.
Its projections agree with the direct executor `run`; preservation then gives
`client_eq`. `client_empty` supplies the initial relation once. For arbitrary
initial states, the caller still supplies evidence that those states are related.
`representation_independent` compares two concrete states through one abstract
state, for every word in this client fragment.

The evidence is propositional and may be erased. The executable operations and
command word remain in `Type`; neither client execution nor compilation extracts
an implementation from an existential proposition. `Simulation.comp` keeps an
intermediate state existentially in the *logical relation*. It does not compute
that state. `Simulation.reverse` exchanges the two already supplied operation
interpretations, without constructing an inverse function.

## Checked applications and limits

[Examples.AbstractFIFO](../../Examples/AbstractFIFO.lean) defines one ordinary
client: enqueue 1, enqueue 2, delete, enqueue 3, then observe the head. The
expected answer is `some 2` and the final sequence is `[2,3]`.
`ordinary_correct` is authored once using `client_empty`, then instantiated for
lists and symmetric lists. Empty words, deletion from empty, and concatenated
words exercise the total-operation and composition cases.

Two valid symmetric layouts, `([1],[3,2])` and `([1,2],[3])`, both represent
`[1,2,3]`. Every public word client has the same answer on them. Their private
front-list lengths are 1 and 2. The checked negative theorem rules out any
function of the abstract list agreeing with that private length on all related
states. Thus operation preservation does not justify adding that observation to
the abstraction boundary. The reversed relation relates one list to these two
different layouts, providing a checked nonfunctional instance. A composed
symmetric-list → list → symmetric-list simulation also compares them.

`run_append` gives execution order explicitly. `runSquare_append` proves equality
of the pasted relational squares. `run_flatMap` states that replacing each command
by a word agrees with executing those replacement words; the example duplicates
enqueues and checks the resulting queue. These laws concern finite command words,
not a language with observation-dependent branching or general recursion.

## Optional compiler surface

[AbstractFIFOSyntax](../../Applications/Sequences/AbstractFIFOSyntax.lean) adds an
opt-in surface over the existing intrinsic compiler terms. Its single base type
is queue state; commands become state-to-state primitives. `plug` accepts any
well-typed state expression, and `program` supplies the state variable.
Endpoint head observation remains ordinary Lean, outside this single-base
fragment. This module is restricted to `Type` at universe zero, matching the
existing compiler, while the direct client is universe-polymorphic.

`primitives` supplies operation preservation once.
`compile_preserves` calls `STLCRelations.compile_preserves`, whose existing proof
uses interpretation naturality through `compile_spec`. No fundamental-theorem
induction is duplicated. `compile_plug` and `program_runs` connect compiled
execution to the ordinary executor; `observe_program` transports the public
observation. Both concrete representations instantiate it in the examples.

`eval_plug` proves interpretation of a filled state-expression hole.
`subst_plug` uses the capture-avoiding substitution added in
[Curry–Howard implementation](curry-howard-implementation.md), and proves that
substitution commutes with this word context. `plug_append` states syntactic
context composition. These claims do not add a compiler frontend, prove runtime
performance, or identify all Lean clients with syntax terms.

## Author effort and the cost extension

The direct author writes one command word and one `ordinary_correct` proof.
Each representation supplies four preservation fields once; the symmetric
instance discharges three by existing operation squares. Both client instances
then call the same theorem. Compared with manually composing concrete queue
squares per client, callers no longer repeat that composition or unfold the
queue decoder and invariant. For a new public operation, its preservation
obligation must still be supplied; the abstraction does not make that work vanish.

The optional surface adds one primitive family and one generic preservation
package. `program` builds the term from the same word, so each concrete client
needs neither a handwritten term tree nor a new logical-relations proof.
Changing representations changes the operation/evidence package, not the word.

[Issue #211](https://github.com/VladimirMarko/conaled/issues/211) can extend this
boundary with separately supplied measured operations whose value projections
agree with `step`, and a cost observation that is explicitly public or hidden.
[Resource workloads](../../Applications/Resources/Workload.lean) already provide
`run_value_fusion` and `run_append`; existing potential accounting supplies
amortized bounds. The extension should connect those results to this executor,
then prove its selected cost claim under a stated usage discipline. Behavior
clients should continue importing only the direct module. Equal head results do
not imply equal costs, and the present word executor does not establish a bound
for persistent branching histories or permit sharing credits between branches.
