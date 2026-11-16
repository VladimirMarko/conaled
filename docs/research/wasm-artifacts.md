# Emitted Wasm artifacts

The native Lean serializer writes the selected closed, single-function modules
as binary WebAssembly. The Node host validates those bytes, resolves `run`, and
returns every i32 result. The Boolean width-32 selector has 65 parameters and 96 results; the packed
selector has three parameters and three results. Both preserve the selected
word and both original words, totaling 96 output bits.

## Reproduce

Run from the repository root in the pinned development environment:

```sh
direnv exec . lake build Examples.WasmWordContinuation Examples.WasmPackedWords Examples.WasmCircuit Examples.WasmArtifacts
direnv exec . lake env lean --run scripts/WasmEmit.lean /tmp/conaled-wasm
direnv exec . node --test scripts/test-wasm-host.mjs
WASM_ARTIFACTS=/tmp/conaled-wasm direnv exec . node --test scripts/test-wasm-artifacts.mjs
```

`WasmEmit.lean` deterministically writes `selector32.wasm`, `selector32-packed.wasm`, `nested.wasm`,
`two-delay.wasm`, `word-delay-boolean.wasm`, `word-delay-packed.wasm`,
`unit.wasm`, and `not.wasm` directly from
`Module.serializeArray`. No assembler participates in production. Repeating
emission yields identical bytes. An IO or serializer refusal fails the command.
The tests compute a SHA-256 descriptor for each emitted file and pass those
same bytes through validation and invocation.

The flake exposes `nodejs_24` from the checked-in Nixpkgs lock. The validated
shell reports Node 24.21.0 and V8 13.6.233.17-node.53. Record versions for a new
lock with `node -p 'JSON.stringify(process.versions)'`. The adapter caps modules
at 16 MiB, each signature at 1000 slots, parameters plus locals at 50000, and
body size at 7654321 bytes. These adapter limits are admission policy, not
proved engine maxima or modeled costs. The complete selector fits them.

## Host contract

Import `loadArtifact`, `createStateful`, and `probeEngine` from
[scripts/wasm-host.mjs](../../scripts/wasm-host.mjs). `loadArtifact(bytesOrPath,
descriptor)` takes a trusted descriptor containing `sha256`, `input`, and
`output`. Shapes are `unit`, `bit`, `i32`, `{product: [a,b]}`, or `{sum: [a,b]}`.
Products concatenate their slots. A sum is a Boolean tag followed by both
payloads; every inactive payload slot must be zero. Boolean words use 32 slots in least-significant-bit-first order; packed words
use one `i32` slot. The packed selector input is `[tag,x,y]` and its output is
`[selected,x,y]`, with canonical 0/1 tags.

The digest binds content to the caller's descriptor. It does not authenticate
the descriptor or establish its source provenance. Successful loading checks
the actual engine validation, selected syntax, exact signature, and export
name/index. The retained byte copy and descriptor snapshot cannot be changed
by the caller. Each invocation creates an isolated worker from that byte copy.

Arguments must be unsigned integer Numbers in `[0, 2^32-1]` with exact arity.
The worker converts those raw words to signed JS i32 arguments and converts
signed results back without losing high bits. The source adapter additionally
requires canonical Boolean/sum encodings on input and output. The bare export
has only the Wasm signature: for example `not` uses `i32.eqz` on any raw i32,
whereas the Boolean adapter refuses input `2`.

A stateful descriptor adds `state` and `initial`, and describes the source
input/output separately. `createStateful` copies initialization once.
`session.step(input)` invokes the product of input and current state, admits
the entire returned product, then commits its state. Refusal, failure,
cancellation and overlapping calls leave the committed state unchanged.
`snapshot()` returns a copy. There is no hidden Wasm memory or start function;
re-instantiation does not reinitialize the source state held by the session.

Results have distinct `kind` values: `loaded`, `result`, `io_error`,
`artifact_mismatch`, `validation_refused`, `binding_refused`, `unsupported`,
`abi_refused`, `resource_refused`, `interrupted`, and `execution_failed`.
A positive `timeoutMs` (default 10000) or optional AbortSignal bounds a worker
invocation. Termination is an interruption, never a source result. A busy
session refuses another transition. Bare-engine probes bypass the source and
selected-syntax admission so tests can distinguish foreign traps and loops
from adapter rejection.

## Mathematical boundary

[Artifacts.lean](../../Applications/Wasm/Artifacts.lean) composes
`Module.serializeArray_correct` with `invoke_compiled` in `serialized_source`.
`host_result` then exposes three independent premises: runtime conformance to
the selected standard semantics, equality of loaded and emitted bytes, and a
faithful observation of the marshalled invocation. `stateful_result` preserves
the entire source output/state product. Refused and interrupted invocations do
not satisfy the successful engine-observation premise.

[WasmArtifacts.lean](../../Examples/WasmArtifacts.lean) applies the result to
all width-32 selector inputs and every two-delay input/state combination.
These are conditional runtime theorems. The Node tests establish empirical
agreement for the tested artifacts; they do not prove V8 conformance, file IO,
SHA-256 authentication, JavaScript marshalling, or the session implementation.
The checked source/serialization results retain their stronger universal
contracts independently of those tests.

This path supports the selected Boolean circuit syntax and fixed multivalue
ABI. It supplies no WASI, dynamic memory, arbitrary-source compiler, browser VM
proof, or wall-clock cost claim. Packed-word lowering is supplied by #513. Live representation migration retains
its separate #515 contract.

## Packed selector and explicit choice

`loadWordSelector(bytes, {representation, sha256}, options)` accepts `boolean`
or `packed` for this concrete selector. Its public input is always three
unsigned words `[tag,x,y]`, and its result retains `[selected,x,y]`. The caller
chooses the representation; `maxSlots` bounds both engine argument and result
arity. A limit of three admits the packed artifact and refuses the Boolean
artifact, whose result needs 96 slots. The normal byte, local and body admission
limits still apply. Refusal does not select another representation silently.

`convertWord(values, from, to)` supplies executable conversions in both directions.
It checks exact arity and canonical scalar values, allocates a new result and
preserves all high bits. Its cost counts checked slots, visited bits and written
result slots. Boolean-to-packed input conversion visits 64 operand bits; returning
all three words to a Boolean caller visits 96 bits. For the word-facing
`loadWordSelector`, the Boolean route performs those conversions in the reverse
direction, also totaling 160 bit visits. Its successful result reports conversion
visits and actual engine marshalling arities: 65/96 for Boolean, 3/3 for packed.
The direct packed path performs no bit conversion.

The actual packed module contains 16 instruction entries, three parameters,
three scratch locals, three results and a peak body operand stack of three.
Its instructions occupy 29 bytes, its function body 37 bytes, and its full
serialized module 74 bytes. The Boolean module emitted by the same serializer
is 8779 bytes. These are syntax and byte observations, not measured speedups.
`PackedWords.profile`, `prefix_stack_bound`, and `selector_serialized` connect
the packed counts to the actual module and execution; counted recursive codecs
prove the 64/96 conversion visits and their value erasure.

Conversion buffers, argument and result array copies, worker message cloning,
retained module bytes, hashing, engine validation, worker startup and engine
execution are additional work. The host copies the input before dispatch and
creates signed argument and unsigned result arrays in the worker. Both ABIs
pay those operations at their respective arities. The reported counters do not
claim an exact JS instruction count, physical heap bound or elapsed-time cost.
In particular, the 16 module instructions exclude these adapter costs.

`PackedWords.both_routes` relates both actual module invocations to the same
complete source result. `PackedWords.host_result` retains the independent
runtime-conformance, file-fidelity and marshalling assumptions. Production tests
execute both emitted artifacts on zero, overflow, high-bit, alternating and
asymmetric inputs and all 33 carry lengths, preserving all three output words.
Nested sums and the Boolean two-delay artifacts remain tested clients.

The [word continuation consumer](wasm-word-continuation.md) transfers a live,
overflow-sensitive two-delay machine between the Boolean and packed artifacts.
Its separate `scripts/test-wasm-word-session.mjs` suite checks live migration,
failure recovery and explicit adapter costs.
