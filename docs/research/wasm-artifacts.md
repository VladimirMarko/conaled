# Emitted Wasm artifacts

The native Lean serializer writes the selected closed, single-function modules
as binary WebAssembly. The Node host validates those bytes, resolves `run`, and
returns every i32 result. The width-32 selector has 65 parameters and 96 results;
its output includes the selected result and both original words.

## Reproduce

Run from the repository root in the pinned development environment:

```sh
direnv exec . lake build Applications.Wasm.Serialize Examples.WasmCircuit Examples.WasmArtifacts
direnv exec . lake env lean --run scripts/WasmEmit.lean /tmp/conaled-wasm
direnv exec . node --test scripts/test-wasm-host.mjs
WASM_ARTIFACTS=/tmp/conaled-wasm direnv exec . node --test scripts/test-wasm-artifacts.mjs
```

`WasmEmit.lean` deterministically writes `selector32.wasm`, `nested.wasm`,
`two-delay.wasm`, `unit.wasm`, and `not.wasm` directly from
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
payloads; every inactive payload slot must be zero. Words use 32 Boolean slots
in least-significant-bit-first order.

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
proof, or wall-clock cost claim. Packed-word lowering and live representation
migration have separate contracts in #513 and #515.
