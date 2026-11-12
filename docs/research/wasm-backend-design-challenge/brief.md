# WebAssembly artifact proof boundary: shared challenge brief

The owner selected WebAssembly for #488 and requested design-challenge on the proof boundary before backend implementation. LLVM is not an alternative target in this challenge. The owner's expectation that LLVM semantics would be harder is a motivation, not an established comparative theorem. Identify relevant evidence without reopening the target choice.

Decision: what exact preservation theorem and artifact correspondence should the first useful WebAssembly backend deliver, and which encoder, parser, validator, runtime and host assumptions may remain trusted? This investigation recommends a contract; it does not implement or adopt it.

## Fixed requirements and candidate proposal

The full issue is ../488-handoff/issue488-design-challenge.json. Preserve a general categorical backend with non-FRP and explicit-state clients, Boolean/fixed-width values, unit/products, finite branching, invalid-input rejection, actual loadable artifacts and external execution. Source semantics, standard target semantics, serialized correspondence and runtime implementation assumptions must remain distinguishable. Ordinary direct clients stay usable. #489's evidence architecture is unselected and is not a prerequisite.

The existing proposal in ../488-handoff/preparation.md uses a memory-free Core 2.0 subset and ordered multi-value ABI: unit empty, products concatenated, Boolean leaves canonical i32 0/1; state explicit in input/output. No automatic64-bit result cap. Existing finite-sum lowering evaluates both total branches and retains canonical inactive payloads. Word32 add/xor/select with modulo arithmetic is a useful proposed client, not yet a proved bridge. Inspect the local code before treating any proposal as an established capability.

Compare proof endpoints within WebAssembly: a standard-rule subset with a small explicitly trusted tested encoding step; verified serialization/parser correspondence; and sound translation validation with a stated parser/byte identity boundary. Runtime validation alone does not establish source semantics. Do not assume a custom evaluator is standard Wasm without an explicit connection, or assume a theorem over ASTs reaches bytes. Consider a staged endpoint if justified, retaining the full issue's real artifact execution requirement.

## Pinned evidence and concrete tests

Use accepted repository e88e83b5b3a6a1cce08f446469187ab40017870c as the code snapshot (worker420 starts there; git show the commit or read clean integration). Main checkout contains unrelated concurrent verification-tooling edits: exclude them, do not edit or assess as the backend proposal. Prior preparation inspected d1a1a048; check intervening changes when relevant.

Inspect Compiler.lean, FirstOrder.lean, Applications/Stack/{Machine,Staging,Measured}.lean, Applications/Circuits/{Syntax,Execution,Correctness}.lean, Applications/Timing/Adders.lean, Applications/FRP/{Indefinite,FiniteSum,FiniteSumLowering}.lean, and existing artifact/translation validation owners found through rg. Read AGENTS, docs/agents/architectural-quality.md, docs/language-direction.md, domain glossary and relevant ADRs (0006,0008,0010). Reuse native constructions where their hypotheses fit.

Core2 spec proposal pin: WebAssembly/spec 05ca4182176763112561ae20153975c12bd689e4, release v2.0.0. Tool-source candidates WABT1.0.41 and Wasmtime45.0.2 are retained under488-handoff. They are source evidence, not executed toolchain tests. Verify primary specifications and relevant mechanizations at exact versions/licenses/proof coverage. External research must cite primary sources; use web browsing when needed. No dependency/tool installation or external proof-framework adoption.

Discriminating clients: composed fixed-word finite selector with carry/wraparound and output wider than64bits; nested finite sums with invalid tags/inactive payloads; native two-delay FRP step with retained state across inputs; swapped output/state ordering, noncanonical booleans, malformed/changed serialized bytes, unsupported opcodes/features, traps/admission failures. Check proposed expected values against actual definitions. Explain what a proof or test of each excludes and what it cannot certify.

## Independent lenses and limits

Three fresh agents assess independently with minimal context. Do not read the other reports or communicate conclusions before all initial reports are saved. Fresh contexts do not establish model diversity. State prior involvement if any. Read only this brief, evidence and your own output.

1. Contract/foundations: exact theorem from source to standard execution and bytes; validity, traps, termination, ABI and trusted premises. Report contract.md.
2. Implementation/use: actual reusable code, source-to-target route, encoding/host tooling obligations, callers, testability and acceptance plan. Report implementation.md.
3. Alternatives/generality: compare trusted encoding, verified serializer and translation validation within Wasm; credible external semantics reuse versus native subset, portability and migration. Report alternatives.md.

Each report: recommendation; strongest evidence for retaining the candidate; concrete supported concerns separated from risks/questions; smallest correction/alternative and discriminating test; missing evidence, exposure and executed-versus-proposed checks. Do not manufacture objections or vote on truth. No source/tracker edits, author sessions, messaging other sessions or recursive challenge. Read-only research and lightweight isolated inspections allowed; no heavy builds while ongoing serialized work uses CPU0. Save outputs here and return. Coordinator will preserve all reports, reconcile disagreements and publish through normal independent acceptance review.
