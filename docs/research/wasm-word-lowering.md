# Canonical circuit words and the first Wasm lowering route

[#509](https://github.com/VladimirMarko/conaled/issues/509) supplies the fixed-word bridge needed by [#488](https://github.com/VladimirMarko/conaled/issues/488). Select the existing Boolean circuit route for the first backend implementation. Its word arithmetic, finite selection and complete 96-bit result now have checked composition laws, and its circuit size grows linearly with word width. Native i32 arithmetic is a smaller alternative with checked local numeric laws and explicit packed adapters; it remains an extension path after the shared circuit backend.

This choice stays within the owner's approved WebAssembly/trusted-encoder boundary. It changes no shared frontend or evidence interface. The work does not establish a Wasm module, a byte serializer, standard module execution or an external runtime result. The [proof-boundary challenge](wasm-backend-design-challenge/synthesis.md) records the earlier proposal; the current #488 body records adoption and owns the remaining delivery.

## Representation and arithmetic

[Words.lean](../../Applications/Circuits/Words.lean) defines `shape n` as `n` Boolean product leaves, least-significant bit first, followed by unit. `encode` decomposes an independent `BitVec n`; `decode` reconstructs it using `BitVec.concat`. Both are executable. `decode_encode` and `encode_decode` prove exact inverses for every width, including zero. Each Boolean product is canonical at this typed boundary. Raw external i32 admission remains a separate #488 obligation.

The `xor` circuit uses the existing xor gate at each leaf. `select` specializes the existing finite-sum `mux`, whose false tag chooses the left value and whose true tag chooses the right. The checked laws return independent BitVec xor and conditional selection for all inputs. No new gate or finite-sum constructor is added.

`ripple` takes two words and an incoming carry and returns a word and a carry. Each stage computes the existing full adder once, retains both input tails, and passes its carry into one recursive circuit. `prepare`, `Circuit.productMap` and `finish` express that sequencing through existing cartesian composition. The existing full adder has repeated subexpressions within its fixed-size stage; those contribute to the counts below. The recursive carry expression itself is not copied into two recursive branches.

`ripple_value` derives the invariant

```
value(result) + 2^n * finalCarry = value(x) + value(y) + incomingCarry
```

from `Adders.fullAdder_addition`, the inductive high-word result and BitVec's concatenation equation. It quantifies over both input words and both incoming-carry values. Width zero returns the incoming carry. `add` supplies false and discards the final carry; `add_correct` proves equality to BitVec addition by reducing the exact equation modulo `2^n`. No Int or Nat source arithmetic is silently truncated.

The existing LCA word machine supplies a workload-specific `Fin (2^width)` model and admitted packing results. Integrated numeral/finite-sum and floating-packing developments supply other useful numeric representations. None was treated as a ready Boolean ripple or Wasm theorem. This implementation uses the existing full adder and core BitVec laws without importing those unrelated workloads.

## The same composed client in both routes

The source meaning is

```
f(tag,x,y) = (if tag then x+y else x xor y, (x,y))
```

on width-32 words. The Boolean `selector` composes xor, addition, the existing finite selector and retention of the two original inputs. `selector_correct` holds for every width; `Examples.CircuitWords.run_correct` specializes the result to BitVec32 observations. Callers supply typed words through `encode`; they do not build projections by hand. The result preserves all three words, totaling 96 source bits.

[Examples/CircuitWords.lean](../../Examples/CircuitWords.lean) connects the circuit theorem to zero, wraparound, the highest-bit carry, alternating inputs and every carry-chain length from 0 through 32. For example, `(0xffffffff,1)` yields selected result zero under true and `0xfffffffe` under false, retaining both operands. With `(0xaaaaaaaa,0x33333333)`, the corresponding results are `0xdddddddd` and `0x99999999`. The finite carry-chain oracle is separately checked over `Fin 33`; every circuit case follows through the universal public correctness theorem.

The native comparison uses `NativeI32.Word = BitVec 32` as an unsigned i32 bit pattern. Its local arithmetic definitions explicitly use these [pinned Core 2 numerical equations](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/numerics.rst): addition takes the sum modulo `2^32`, and xor combines corresponding bits. `add_correct` and `xor_correct` relate those definitions to the independent BitVec operations. The [pinned instruction rule for select](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst) chooses its first operand for nonzero condition and its second for zero. `NativeI32.select` follows that rule. These are local numerical interpretations with reviewed correspondence to the specification, not a mechanization of standard configurations or module execution.

`encodeTag` maps Bool to i32 0/1. `decodeTag_iff` admits exactly those encodings; a checked tag-2 example separates standard truthiness from canonical admission. `decodeWord_iff` admits exactly the unsigned natural value of a word and rejects values outside `[0,2^32)`. `pack`/`unpack` relate the Boolean-product and packed-word representations with exact inverse laws. `NativeI32.selector_correct` and `routes_agree` prove the two routes have the same complete observations for all canonical inputs.

The default ABI remains 32 canonical Boolean i32 slots per word. The native comparison has a distinct packed ABI: one canonical i32 tag and two arbitrary i32 word patterns as input, three i32 word patterns as output. Its pack/unpack and tag admission obligations are explicit. Those adapters are not assumed to cost nothing in an eventual combined backend; the native count below starts after admission/packing and ends before unpacking. A full raw-host adapter and its cost belong to #488.

## Mechanically defined counts

`Circuit.work` counts syntax-node visits. The checked equations are `(ripple n).work = 122*n+3` and `(selector n).work = 194*n+27`. The latter includes both total arms and selection. These all-width equations exclude exponential recursive carry duplication in the actual constructed circuit.

The `plan` fold describes a proposed lowering that aliases routing wires, executes both paired subcircuits, gives each gate a fresh result local, and empties the operand stack after each gate. A constant uses const/set; not uses get/eqz/set; nand/nor use two gets, a binary operator, eqz and set; xor uses two gets, xor and set. `invocationPlan` adds parameter locals and the final ordered result loads. These definitions count a proposed strategy, not an implemented lowering. Proving a future emitter realizes the strategy is still required.

| Observation for the width-32 client | Boolean circuit route | Native packed plan |
| --- | ---: | ---: |
| Source circuit node visits | 6,235 | No Boolean circuit is built |
| Proposed numeric/local instructions, including result loads | 3,266 | 16 |
| Parameter slots | 65 | 3 |
| Total local slots, including parameters | 866 | 6 |
| Result slots | 96 | 3 |
| Proposed peak operand-stack values | 96 | 3 |

The Boolean totals are kernel-checked against `invocationPlan (selector 32)`. The full-adder preparation contributes 68 instructions and 17 fresh result locals per bit; `ripple_plan_instructions` and `ripple_plan_locals` prove linearity for all widths. No circuit arena bound is relabeled as engine memory.

The native list is a fixed plan: load x/y, add, store sum; load x/y, xor, store xor; load sum/xor/tag, select, store selected; load selected/x/y as results. `planCounts` derives instruction count, maximum referenced local index plus one, and a checked prefix stack profile from that list. `selector_plan_counts` proves `(16,6,some (3,3))`, where the final pair is final stack size and peak stack size. The plan's arithmetic corresponds to the separately proved native selector expression. No claim is made that this list is a serialized Wasm function or that a Wasm parser or runtime has executed it.

The counts favor native arithmetic for packed words. The circuit route is selected for the first implementation because the same existing gate target already serves word circuits, nested finite-sum lowering and native explicit-state FRP bodies. It needs no new mixed Boolean/word source sort or common intermediate language. The native candidate's local laws establish its arithmetic feasibility, but do not supply the remaining combined source/ABI lowering. The circuit's linear size and concrete counts make it a bounded first route; actual engine arity and admission remain to be tested. If the 96-result artifact fails pinned-engine admission, #488 must resolve that limitation explicitly instead of discarding results or claiming this count proves engine support.

## Statement review and validation scope

| Claims reviewed | Intended domain and checked use |
| --- | --- |
| Codec inverses, injectivity and cell count | Every natural width, including zero; explicit `5#3` layout and arbitrary 32-bit round trips |
| xor and finite selector correctness | Every word and tag; independent BitVec xor and the existing mux's branch convention |
| Ripple step and arithmetic invariant | Arbitrary words and incoming carry; both recurrence and width-zero carry retained |
| Modular addition | Final carry is discarded only after the exact equation; wraparound and all carry lengths use the public result |
| Composed selector | All inputs and all three outputs, with branch-sensitive asymmetric fixtures |
| Circuit and lowering-plan counts | The actual circuit recursion versus a separately named hypothetical fresh-local strategy; no engine/resource theorem inferred |
| Native numeric laws and codecs | Fixed width 32, canonical tag admission, unsigned bounds and exact Boolean/packed adapters |
| Route agreement | Complete word observations under the explicit tag codec, not arbitrary nonzero host tags |

The induction for `ripple_value` must generalize the incoming carry: the recursively generated carry need not equal the original one. That obligation was exposed during development and is included in the final theorem. Counterexamples retained in the examples show that raw tag 2 is rejected by canonical admission although standard select treats it as true, and an out-of-range unsigned word is rejected rather than silently wrapped.

Focused checks use private outputs and a copied import closure whose source bytes match both the validated dependency candidate and this worktree. Root coordinates immutable candidate validation, the exhaustive proof audit and independent Standards/Spec review. Their evidence is recorded with the issue's implementation handoff. This note does not turn focused checking into completed repository acceptance.

Remaining #488 work: standard rule coverage and transcription review; local/operand-stack framing; module validation, instantiation, export lookup and invocation; finite successful execution with no trapping or divergent alternative; raw Boolean/nested-sum admission; explicit-state transport; the exact-byte correspondence premise and tested encoder; actual artifact emission and pinned-engine tests, including every intermediate state of two delays. No package, toolchain, runtime, module or serialization work is claimed by #509.
