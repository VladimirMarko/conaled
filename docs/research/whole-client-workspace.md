# Workspace schedules inside a client

[#281](https://github.com/VladimirMarko/conaled/issues/281) composes the accepted
[clean-ancilla schedules](clean-ancilla-implementation.md) with a caller that
uses the first computed output before the second use of the retained dependency.
The source is [ClientSchedules](../../Applications/Uncomputation/ClientSchedules.lean);
[checked clients](../../Examples/ClientSchedules.lean) exercise its public laws.

Six caller-owned Boolean wires enter with arbitrary values. The first two are
stable inputs. The schedule XORs their conjunction into output 2, runs the gap
client, then XORs the conjunction into output 3. Gap mode selects either XOR of
output 2 into output 4, or XOR of the three-input conjunction of output 2 and
inputs 0 and 1 into output 4. Wire 5 is untouched. The independent `output`
function specifies these updates without mentioning gates or scratch.

The high-demand client computes a three-input controlled update from the admitted
CNOT/Toffoli vocabulary. Its first Toffoli stores a two-input conjunction in
scratch; the second uses that conjunction and the remaining input to update the
caller output; the third cleans scratch. This is useful output work, not a dummy
allocation. We compare these specified implementations, without claiming that
no other circuit could use less workspace or fewer gates.

`correct` proves the independent output and clean release for every caller state,
either retention policy, either gap mode, and any finite number of gap steps.
`advance_append` composes segment contracts with the current ownership set;
`advance_repeat` derives arbitrary iteration from one proved segment contract.
The caller-specific entry, gap and exit contracts discharge those premises.
They preserve the inputs that cleanup needs. `repeat_parallel` and
`repeat_serial` also instantiate this law with the existing native schedules.
The new law does not compare their different parallelism by pretending they
have the same event sequence.

`advance_value` connects accepted ownership execution to the gate permutation.
`coherent_reference` then uses the existing `coherent_embed` theorem to establish
the whole-client equation for arbitrary complex amplitudes and an untouched
finite reference, including nonfactorizing states. The known injectivity of
`pairInput`, reused as `input`, makes the zero-scratch embedding faithful.
This retains caller outputs, not just their basis probabilities.

## Work and space

The same event lists determine ownership, gate work, layer depth and live scratch.
Acquire/release events do not reset bits, count as gates, or release caller wires.
All used layers are singleton valid gates. Logical work and depth therefore agree
for this sequential client. `work_depth` proves for every gap length k:

- retain: `4 + k * gapCost`;
- uncompute/recompute: `6 + k * gapCost`;
- `gapCost` is 1 in low-demand mode and 3 in high-demand mode.

For one gap step, `low_costs` and `high_costs` compute:

| Gap | Schedule | Work | Depth | Peak scratch | Final scratch |
| --- | --- | ---: | ---: | ---: | ---: |
| Copy updated output | Retain | 5 | 5 | 1 | 0 |
| Copy updated output | Recompute | 7 | 7 | 1 | 0 |
| Three-input controlled update | Retain | 7 | 7 | 2 | 0 |
| Three-input controlled update | Recompute | 9 | 9 | 1 | 0 |

Retaining is better in work at equal peak scratch for the low-demand instance.
For the high-demand instance, a one-scratch-wire budget admits recomputation but
excludes this retain schedule; a work-first objective with two scratch wires
prefers retention. Peak-space claims here concern the displayed finite instances;
the arbitrary-length law supplies correctness and work/depth, not a global
optimality result. Caller storage adds six wires to each listed scratch peak.

In the retain schedule, wire 6 stays owned during the gap and high-demand work
uses wire 7. In the recompute schedule, cleanup releases wire 6 before the gap,
which acquires, uses and releases that same wire before the final computation.
`retained_wire_not_available` rejects acquiring wire 6 while it is retained,
even when its value happens to be zero. Clean values do not imply free ownership.
The zero-gap case recovers the original 4-versus-6 gate comparison and one-wire
peak for both policies.

## Author obligations and limits

A direct client proves each entire sequence. The shared route proves the entry,
one gap step and exit contracts, then obtains all finite repetitions through
`advance_repeat`. Finite Boolean discharge is kernel-checked. Authors still
supply wire assignments, ownership, clean-entry facts, preserved dependencies and
an independent caller specification. No ownership inference or scheduling search
is provided. Existing native schedule interfaces remain unchanged.

The initial missing connection was from an arbitrary number of useful gap steps
to whole-client ownership and independent output. Checked cases now use the
public iteration and coherence theorems, including original parallel/serial
clients, zero gap, both space-demand instances and a rejected allocation.
Statement review separates universal family laws from the finite peak-space
calculations. The coherent interpretation is the existing admitted permutation
model; no measurement, borrowed dirty scratch, physical timing or energy claim
is added. Remaining scheduling synthesis belongs to #174/#193, and frontend
ownership/compatibility obligations remain with #235.
