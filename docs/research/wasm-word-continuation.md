# Preserving a live word continuation

`Applications.Wasm.WordContinuation` implements the independent word machine
`step (x, (recent, older)) = (x + older, (x, recent))`, with addition modulo
2³² and initial state `(0x12345678, 0xffffffff)`. Every tick returns the output
and both updated registers. The Boolean implementation composes two existing
reactive delays with the word adder. The packed implementation uses five Wasm
instructions. Both are serialized by the native Lean serializer.

| Artifact | Parameters/results | Scratch locals | Instructions | Bytes |
| --- | --- | --- | --- | --- |
| `word-delay-boolean.wasm` | 96/96 | 545 | 2274 | 6216 |
| `word-delay-packed.wasm` | 3/3 | 0 | 5 | 48 |

The profile and serialization theorems check these numbers. The independent
binary parser checks the emitted files, including an explicit packed byte
fixture. Boolean bits are least significant first, with the recent register
before the older register. Packed state uses two i32 slots in the same order.
The decoder requires exact arity, i32 types, and canonical Boolean values.
Executable conversion decodes and re-encodes both registers; its inverse law
recovers every admitted raw state.

After inputs `[1, 0xaaaaaaaa]`, outputs are `[0, 0xbcdf0122]` and live state is
`(0xaaaaaaaa, 1)`. Migrating there and supplying
`[0xffffffff, 0x55555555, 7]` yields `[0, 0xffffffff, 6]` and final state
`(7, 0x55555555)`. These examples expose overflow, initialization resets and
register swaps. The finite-run theorems cover arbitrary prefixes and every
finite suffix, including the empty suffix, in both directions and after a
round trip. They reuse `run_related` and `run_append`.

## Host ownership and failure

`scripts/wasm-word-session.mjs` exposes `createWordSession(bytes, configuration,
options)`, then `session.step(word)`, `session.snapshot()` and
`session.migrate(targetBytes, targetConfiguration, options)`. Configuration
contains `representation` (`boolean` or `packed`) and the artifact's `sha256`;
creation also requires the two-word `initial` state. Public words use unsigned
32-bit JavaScript integers. The wrapper passes actual bytes and descriptors to
the existing stateful host.

Migration snapshots the live owner, converts its state and prepares a target
session. Installation follows successful loading and a final cancellation
check. During preparation the wrapper rejects another tick or migration. A
refused or cancelled preparation retains the old owner and releases the busy
flag. Same-representation migration still validates and installs a prepared
replacement. The formal `transfer` model records readiness and publication as
explicit observations; tests check that the JavaScript adapter enforces those
gates. This is between completed ticks. Existing pending-publication service
contracts, distributed delivery and crash recovery are outside this operation.

## Cost units and boundaries

For source state size `S` and target size `T`, a successful migration records:

1. Snapshot `S` slots and validate `S` source slots.
2. Visit 64 bits for a representation change (zero for the same representation)
   and write `T` target slots.
3. Copy `T` slots into the target's retained initial state; request host
   preparation with the target byte length and state size.
4. Copy `T` active slots after loading, then install one owner.

`migrationTrace` and `migration_accounting` formalize this schedule and its
logical operation totals for valid owned state. Copies total `S + 2T` on
success, and `S + T` when loading refuses. A cancellation after loading still
charges the active copy but no installation. Admission refusal has an empty
trace. Conversion reads each indexed source scalar once, validating and consuming
that same value. On malformed input it discards the partial result and reports
validation, bit visits and writes already performed. The successful-source
schedule does not model that partial traversal.

The owned state overlap bound is `3S + 3T`: the old active and retained initial
states, snapshot, converted target, target retained initial and active states.
It is 198 slots across representations, 384 for Boolean-to-Boolean and 12 for
packed-to-packed. Admission checks this bound before allocating migration
arrays. Adapter artifact admission charges old bytes plus twice the target
bytes (6312 and 12480 bytes for the two cross-representation directions).

These are modeled adapter operations and owned scalar storage bounds, not
elapsed-time measurements or a bound on physical heap use. Recursive admission
helpers, worker messages, engine validation/compilation, engine storage and
GC are external host work. `hostPrepare` exposes that boundary and its inputs;
it does not assign those operations a fictitious constant execution cost.
Discarding a candidate makes no claim about when memory is reclaimed.

## Reproduce and trust boundary

```sh
direnv exec . lake build Examples.WasmWordContinuation
direnv exec . lake env lean --run scripts/WasmEmit.lean /tmp/conaled-wasm
WASM_ARTIFACTS=/tmp/conaled-wasm direnv exec . node --test scripts/test-wasm-word-session.mjs
```

Module invocation theorems include output and both next-state words. Generic
rules give domain preservation, no traps, and completion from every reachable
state; the existing general no-infinite-execution theorem applies. The byte-host
result theorem assumes runtime conformance, fidelity of the loaded bytes and
correct marshalling. Real artifact tests exercise those integration boundaries;
the JavaScript engine is not verified by Lean.

Direct pair codecs and existing reactive transport suffice here. A shared
migration framework would add an interface without removing repeated proof
work in this consumer. In particular, the stronger pending-work FRP contracts
remain in their native relations and are not restricted to invertible codecs.
