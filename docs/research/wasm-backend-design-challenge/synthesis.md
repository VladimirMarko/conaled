# WebAssembly proof-boundary challenge: synthesis

Recommend a first delivery that proves compilation into selected WebAssembly Core 2.0 standard rules, explicitly assumes correspondence between the emitted bytes and that module, and executes the actual bytes through a pinned runtime. This is a proposed contract for owner selection, not an implemented backend or adoption of trusted serialization. WebAssembly is already selected; LLVM is outside this decision.

## Evidence and limits

All three independent perspectives completed: [contract and foundations](contract.md), [implementation and use](implementation.md), and [alternatives and generality](alternatives.md). Their initial reports and [shared brief](brief.md) are preserved with hashes. They inspected accepted repository e88e83b5 and pinned primary sources, without seeing one another's findings. They share evidence and a model family; agreement is not a correctness vote. No new Lean proof, artifact emission, runtime test or external formalization rebuild was executed.

The decisive reusable structures are the first-order target/law separation, circuit interpretation, canonical finite-sum lowering and relational explicit-state transport. They permit a bounded backend without adopting a universal new IR or #489. None already proves a Wasm module, serializer, or fixed-word arithmetic bridge. Existing one-bit adder and Int stack results must not be advertised as a Word32 compiler.

## Proposed first contract

Keep memory-free straight-line modules, unit as an empty value list, products in left-to-right order, canonical i32 Boolean leaves, and explicit input/state and output/state products. Admit only documented total operations and supported module forms. Make practical arity/local/encoding limits fallible admission conditions rather than imposing a 64-bit semantic ceiling.

The proof must reach standard module validation, instantiation, export lookup and invocation. Prove finite successful execution and exclude trapping/divergence for admitted inputs, with the determinism or equivalent execution property that justifies that exclusion. Instruction composition must preserve surrounding operand stacks and unaffected locals. State exactly which standard rules were transcribed and where their correspondence to the published specification remains a review assumption.

Expose a separate relation connecting exact bytes to the proved module, ABI and export. For the first delivery, the proposed theorem consumes this correspondence as an explicit premise; a tested pinned emitter/assembler supplies engineering evidence, not a proof of the premise. External realization additionally assumes runtime conformance, faithful host marshalling and loading the same bytes. A later verified serializer can establish the binary relation, or a sound byte-facing validator can derive it for accepted artifacts, without changing ordinary source clients.

Raw Wasm integers require admission before native Boolean/finite-sum decoding. Reject tags other than 0/1 and nonzero inactive payloads. If the host adapter performs rejection, identify that adapter as the admitted public entrypoint; do not claim the raw export rejects malformed representations. Eager finite-sum lowering evaluates both arms, so retain total operations or prove a different lowering before introducing partial operations.

## Alternatives and unresolved implementation choices

A verified serializer would remove the encoding premise through a binary-grammar theorem, including section order/lengths, indices and immediates. It need not verify a parser as well. Translation validation is attractive for multiple or optimizing producers, but checking an externally parsed AST still trusts the byte-to-AST connection. Ordinary runtime validation proves neither source semantics nor canonical input admission.

The pinned external Coq/Isabelle formalizations are credible references, but their inspected claims do not supply an already checked Lean bridge or a universally verified binary parser. Native selected-rule formalization is recommended for this bounded delivery because its client proofs compose locally. This does not select native Lean as the universal evidence interface or exclude broader external reuse. Wider instruction/control/memory support should revisit that comparison.

The implementation lens favors a circuit route initially; the alternatives lens leaves native word primitives versus Boolean ripple lowering open. The evidence does not settle proof effort or code size. Resolve this through a small comparison using the same modular word/finite-selector specification and ABI observations. Do not force a shared multi-sort framework merely to avoid the comparison.

A retained engine instance is not the semantic state invariant: correctly passing returned explicit state through fresh instances is equivalent for this pure fragment. Check the state passed to every next invocation. Also distinguish exact artifact identity from semantic equivalence: some byte changes preserve semantics, so negative tests must name what is expected to fail.

## Acceptance sequence

1. Freeze source fragment, ABI, standard-rule coverage, raw-input admission, trusted premises and failure classifications.
2. Check the fixed-word/Boolean bridge and generic instruction-composition laws; select the local lowering route on this evidence.
3. Prove full module invocation preservation, including no-trap termination, and instantiate native pure and explicit-state clients.
4. Emit and execute exact artifacts. Check a composed word/finite-selector result wider than 64 bits, overflow/carry cases, nested sums and every intermediate state of two delays. Proposed arithmetic and delay oracles in the reports still require checked instantiation.
5. Exercise malformed encodings, noncanonical tags/payloads, changed constants/export/layout, unsupported forms and external resource failures. Distinguish parse failure, validity, source preservation and environmental failure.
6. Run repository formal acceptance and independent Standards/Spec review. Record encoding/runtime assumptions with the delivered theorem and artifact evidence.

The immediate owner choice is whether the explicitly conditional, tested-encoder endpoint is sufficient for the first delivery, or whether binary correspondence itself must be proved before delivery. The challenge recommends the former while preserving the latter as a separately measurable extension. No backend implementation has started under this recommendation. Committed report publication still requires the repository's ordinary independent acceptance workflow.
