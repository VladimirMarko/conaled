# Ownership protocols alongside adjoint resource modes

Issue [#360](https://github.com/VladimirMarko/conaled/issues/360) compares an
independent finite ownership protocol with the existing graded mode compiler.
The checked client transfers a handle, consumes two handles, and returns the
selected sequence `[37,99]`. A second representation swaps handle addresses.
Both executions agree on returned values and which handles remain live.

**The mode layer does not establish ownership by itself.** It controls how the
ledger is structurally used and transports primitive payload/resource laws.
A separate protocol contract supplies permission checks, live-handle consumption
and frame preservation. A checked degree-preserving resurrection operation
violates that protocol. This identifies a concrete boundary of the current
mode interpretation rather than recommending modes as the library's mandatory
resource interface.

## Independent protocol and executable machine

[`OwnedHandle`](../../SquareKit/OwnedHandle.lean) uses two handle addresses,
represented by Bool. Each occupied slot stores its owner, selected natural
payload and live/spent state. `liveHeap` exposes only live slots. A consumed
slot remains internally as a receipt, but cannot be used again by the protocol.
The distinction is observable: a spent slot is absent from `liveHeap`.

The inductive relation `Acts` is the specification. Transfer requires a live
slot owned by the stated source and changes its owner while retaining its
value. Consumption requires live ownership, removes the slot from the live
heap and appends its exact payload to the returned sequence. Both require a
nonfailed input. `Runs` composes these mathematical transitions. It is defined
independently of the executable conditional checks.

The executable `step` returns `Option State`; `run` sequences a finite command
list. `step_acts` and `run_spec` prove equivalence to the independent relations,
not merely preservation in one direction. `run_append` derives the sequential
composition law. `consumed_absent`, `transfer_owner` and the native
`consumption_contract` expose the specified observations. There is no allocator,
concurrent environment, pointer aliasing model, scheduler or reclamation
implementation. The claim is abstract sequential ownership and permission
safety for successful protocol derivations. No physical-memory safety,
concurrent interference freedom, fairness or general normalization is inferred.

## Native separating contract

Reynolds's separation logic interprets separating conjunction through disjoint
heap fragments. Its frame rule extends a command's footprint specification with
an untouched disjoint heap predicate, subject also to the restriction that the
command modifies no variable free in that predicate. Fault behavior and
locality matter to soundness; heap disjointness alone is not a theorem about
arbitrary commands. This motivates examining ownership and frame conditions
independently of mode grades. [Separation Logic: A Logic for Shared Mutable Data
Structures](https://www.cs.cmu.edu/~jcr/seplogic.pdf), §§2–4.

[`OwnedHandleSeparation`](../../SquareKit/OwnedHandleSeparation.lean) defines
finite heaps, disjoint union, separating conjunction and exact singleton
ownership assertions. `initial_separated` in the examples supplies an inhabited
split; `no_separating_alias` rejects two claimed disjoint ownership fragments
for the same handle. These definitions do not mention modes or degrees.

The protocol's primitive actions preserve every slot other than their target.
`frame_remainder` proves equality of the entire heap with that footprint removed;
`frame_predicate` transports any predicate of that remainder. This is a bounded
local frame result, not a formalization of Reynolds's full Hoare logic. It
frames heap contents, not the returned sequence or failure flag, which commands
may affect. The source includes no mutable program variables, so the paper's
variable side condition is not silently assumed for a richer language.
Native clients can use the transition relation and frame theorems directly.
They need no adjoint-mode syntax or receipt grade.

## What the mode compiler adds

Pruiksma, Chargin, Pfenning and Reed require a preorder of modes, monotone
structural permissions and the independence restriction on hypotheses.
Shifts form an adjunction. Their invalid-promotion example shows why an
unrestricted result cannot simply capture a linear hypothesis. These are
structural reasoning principles; they do not specify the operational meaning
of a handle consumer. [Adjoint Logic](https://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf),
§§2–3. We reuse the existing bounded two-mode implementation rather than
claiming a new formalization of the complete paper.

[`OwnedHandleModes`](../../SquareKit/OwnedHandleModes.lean) interprets its linear
atom as the ledger State. Degree counts occupied slots, both live handles and
spent receipts. It is **not** live-resource count. Every admitted action
preserves this accounting degree while consumption decreases the live domain.
`acts_weight` derives this conservation from local actions. Failed instruction
execution retains the ledger, sets an observable failure flag and fabricates
no returned value. Later instructions remain failed.

A primitive executes a command from unrestricted data alongside the linear
ledger. A second primitive supplies an unrestricted command literal.
`instruction` actually uses `downMap` and `oneDown`; it does not mark an ordinary
function with a mode tag after execution. `program` composes these typed terms.
Primitive payload agreement feeds the existing `Term.compile_preserves`
theorem, yielding the full-state equation `program_compile`. Independently,
`successful_total` derives agreement with each protocol derivation, yielding
`compiled_protocol` from local transition evidence.

The command-data fragment also exercises actual up/down transposition.
`commandShift_adjunction` identifies source transposition with the existing
hom-set equivalence, and `commandShift_roundtrip` checks its compiled round
trip. The linear ledger is never promoted to unrestricted command data.
This reuses #352's adjunction and its existing cases without changing them.

A typed mode term can still contain two sequential uses of the same handle.
`double_use_mode_failed` checks that such a term returns an explicit failure;
mode typing alone does not claim it is a successful protocol. Successful
ownership-sensitive clients additionally carry a `Runs` derivation, assembled
from local `Acts` steps, and `Finished` when they require all live ownership to
be discharged. `Finished` tests the live heap, not the retained receipt count.
The mode layer neither infers these derivations nor replaces their assumptions.

## Representation change and controls

[`OwnedHandleBackend`](../../SquareKit/OwnedHandleBackend.lean) changes the slot
representation by any equivalence on handles. `lower` renames instruction
addresses and `encode` reindexes slots. The executable backend is still `run`
on those renamed instructions and states; it does not define execution by
calling the source denotation. `encode_replace` proves the update equation;
`encode_acts` derives local operational simulation, then `encode_runs` derives
it for arbitrary successful command lists. `two_stage` composes that result
with mode compilation. The selected output state is preserved, including
returned order, live/spent status and owners. `encode_live` and
`encode_returned` recover the chosen observations.

This is a bijective slot-layout change within the same bounded machine, not a
compiler to a physical runtime or a general independently implemented backend.
The generic theorem covers successful derivations. Concrete rejected programs
are also checked on the changed layout; a generic reflection theorem for every
malformed program is not claimed.

[`Examples.OwnedHandle`](../../Examples/OwnedHandle.lean) retains:

- An independent expected final state after transfer of payload 37 to owner 1,
  its consumption, and consumption of payload 99 by owner 2. The source run,
  protocol derivation, completion and compiled result are connected by the
  general theorems.
- A nonidentity slot permutation, with the same selected sequence and empty
  live heap through `two_stage`.
- Rejection of double use, stale-owner use after transfer, and completion that
  silently discards live ownership. The alias test rejects a duplicated
  separating permission; the unrelated slot's selected value is framed.
- A resource map that revives all spent handles while conserving degree.
  Its live output violates completion. This demonstrates the missing semantic
  obligation, rather than treating accounting conservation as ownership.
- Rejection of a generic map from this ledger to the degree-zero unit and of
  the actual duplication function. We do not claim every map into a tensor
  is impossible: degrees vary across ledger states.

## Obligations and architectural disposition

| Work | Native protocol/separation route | Mode route with the same protocol |
|---|---|---|
| Setup once | State, independent action specification, executable-step equivalence and frame proof. | Reuse native setup; add ledger resource interpretation and typed primitive meanings. Existing compiler induction and adjunction are reused. |
| New command | Specify its live-ownership effects; prove local executable agreement and frame behavior. | Also prove receipt-degree and payload preservation. Modes do not derive permission checks from its name. |
| Reuse in a longer program | Assemble local action evidence; use `Runs` and sequential composition. | Compose typed terms; generic compilation derives payload and accounting preservation. The same protocol evidence is still required. |
| Swapped layout | Prove the update/transition simulation once, then derive runs. | Reuse that simulation and the existing compiler theorem; no new mode or adjunction is required. |
| Ownership-sensitive observation | Preserve exact returned payloads and live domain. | Preserve them through the payload square; degree alone is insufficient. |

Retain the native contract as the direct interface for this client. Retain modes
as an optional structural layer when a larger source combines linear ledgers
with duplicable data. This experiment establishes checked compatibility and a
counterexample to a stronger reading of degree, not a productivity advantage
or a requirement to organize every resource client by modes. No author timings
were measured; proof setup and repeated use are distinct in the table.

#36/#290 retain operational models and source interpretations; #196/#193 retain
runtime-facing consumers. A follow-up with allocation, concurrent interference
or physical handles needs those semantics before adding claims. A frontend
that should reject double-use statically needs a richer ownership/typestate
contract than the current single linear atom; #235 owns that adoption decision.
The geometric crisp/modal work supplies no evidence for these safety claims.
#107 remains paused, #108 unselected and #260 inactive.

All new formal statements and examples enter the normal public import closure
and exhaustive proof audit. Exact candidate validation and statement-review
evidence are recorded in the implementation handoff. External paper statements
remain research context; the Lean results have the bounded scope stated above.
