# Native WebAssembly serialization

`Applications.Wasm.Module.serialize` produces `Option (List UInt8)`;
`serializeArray` supplies a `ByteArray` for IO. Both preserve the existing
single-function module, its complete signature, local types and body, and its
`run` export at function index zero. A failure rejects an unrepresentable
index, vector count, expanded local count or encoded payload length. Serialization
does not replace static validation; source-generated modules already have
`assemble_validate` and `assemble_valid`.

The executable implementation is in `Applications/Wasm/Serialize.lean`.
`Applications/Wasm/Binary.lean` independently defines the binary grammar and
imports no encoder. Each internal encoding operation returns bytes with an
erased proof of its grammar production. The proof is constructed compositionally;
it is not a caller premise, an axiom, or an equality defining the grammar in terms
of encoder output. `Module.serialize_correct` proves that successful bytes
satisfy `ModuleBytes` for the exact input module. `serializeArray_correct` proves
the same statement for the array's byte list.

## Specification correspondence

The pin remains WebAssembly Core 2.0, revision
`05ca4182176763112561ae20153975c12bd689e4`. These are selected productions of that
standard, with no extension to its execution rules.

| Pinned binary production | Lean grammar |
|---|---|
| [Unsigned and signed integers](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/binary/values.rst#binary-uint) | `Unsigned`, `Signed`: explicit terminal digit bounds and seven-bit width decrement at each continuation. |
| [Vectors](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/binary/conventions.rst#binary-vec) and [names](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/binary/values.rst#binary-name) | `Sequence`, `Vector`, `Name`: u32 element count; the selected name is the three ASCII/UTF-8 bytes of `run`. |
| [Value and function types](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/binary/types.rst#binary-valtype) | `ValType`, `FunctionType`: all seven existing value types, ordered parameter/result vectors and function marker `0x60`. |
| [Instructions and expressions](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/binary/instructions.rst#binary-instr) | `Instruction`, `Expression`: selected opcode identity, u32 local indices, signed i32 constants and final `0x0b`. |
| [Sections, locals and modules](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/binary/modules.rst#binary-module) | `Sized`, `Section`, `LocalGroup`, `Locals`, `FunctionBody`, `Export`, `ModuleBytes`: actual byte lengths, local-group expansion, magic/version and ordered type/function/export/code sections. |

The module grammar fixes one type and one function referring to type zero.
Its code vector has one body; its export vector contains exactly `run`, of
function kind, referring to function zero. Every production names its complete
byte list, including nested payload boundaries and final module consumption.
`Reads`, `reads_sequence_cons` and `Sequence.append` expose composition under
arbitrary trailing bytes. Complete consumption is `Reads ... bytes []`.

Locals are emitted as singleton groups. This preserves arbitrary type order and
avoids a separate grouping pass. Counts and lengths stay in `Nat`; the encoder
checks each actual encoded section/body length as well as each vector/index.
`Module.withinLimits` is an independent syntax admission profile and is not used
to infer encoded sizes. The signed encoder uses the i32 value's signed `toInt`,
so high-bit values are emitted with the required negative signed representation.
No total-module u32 cap is imposed: Core bounds section/body sizes individually.

## Checked clients and independent fixtures

`Examples/WasmBinary.lean` connects the encoder to the grammar for the zero-arity
module and retains unsigned/signed boundary encodings, mixed local types, a
128-byte length, a multi-byte local index, and the width-32 selector, nested-sum
and two-delay source modules. The existing source examples retain their stronger
all-input invocation and successive-state results.

`Lowering.serialize_invoke_correct` composes the byte correspondence with
`invoke_correct`: for successful serialization, every reachable state remains
inside the selected standard domain, avoids traps, and retains a finite path to
the complete encoded circuit result. The exact export address is also retained.
It does not require a caller-supplied encoder-equivalence premise.

The native fixture producer and independent Python parser can be run as follows:

```sh
direnv exec . lake env lean --run scripts/wasm-fixtures.lean > /tmp/wasm-fixtures.jsonl
direnv exec . python3 scripts/test-wasm-binary.py /tmp/wasm-fixtures.jsonl
```

The test compares hand-calculated unit and signed-constant binaries, parses the
larger emitted clients, and rejects mutations of headers, sizes, section order,
indices, export identity, instructions, terminators and trailing bytes. These
tests complement the proof; they do not define its grammar.

## Remaining boundaries

Faithfulness of the selected grammar and execution-rule transcription to the
pinned standard remains a reviewed specification boundary. Lean's kernel checks
the proofs; native Lean compilation and execution are trusted to implement the
executable definitions. File delivery must preserve the proved bytes. A host
adapter must enforce the canonical Boolean/sum ABI, preserve result order and
arity, and commit returned state only after successful admitted execution.
An external engine must implement the standard. None of those external
obligations is an encoder-correspondence axiom. Actual artifact delivery,
engine execution and host-state management are owned by #512.
