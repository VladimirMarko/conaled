# Contract and foundations assessment for #488

Retain the proposed memory-free Core 2.0 backend and ordered multi-value ABI. The first useful endpoint can use a tested, explicitly trusted encoder, provided the theorem reaches standard module instantiation and exported-function invocation and the byte correspondence premise identifies the exact bytes executed. Do not describe a custom circuit evaluator, a well-typed Wasm function, or a successful runtime validator as that endpoint.

This recommendation is conditional on the contract below being implemented and checked. No Wasm backend theorem or runtime experiment was checked in this investigation.

## Evidence for retaining the design

At accepted revision `e88e83b5b3a6a1cce08f446469187ab40017870c`, the existing frontend separates target operations from their meaning and local laws (`FirstOrder.lean:67–108`). `compile_sound` supplies general frontend preservation. `Applications/Circuits/Syntax.lean:47–74` supplies interpretation and its commutation with compilation; `Execution.lean:19–38` connects circuit execution to independent Boolean meaning. These provide a compositional route to a new backend without changing ordinary direct clients or adopting #489.

The finite-sum bridge already proves exact encoded outputs for open contexts and nested sums: `Applications/FRP/FiniteSumLowering.lean:111`, `lower_correct`. Its `caseCircuit_work` counts both arms. `FiniteSum.lean:45–77` defines canonical admission and proves `decode_iff` and `reject_iff`. These are stronger building blocks than merely comparing observations after dropping inactive payloads.

For explicit state, `Applications/FRP/Indefinite.lean` exposes input × state → output × state as an ordinary circuit, with `Program.correct`, `seq_machine`, `compiled_source`, and relational `Program.transport`. The backend need only prove its local transition relation and initialization correspondence to reuse stream observations. Its own progress and resource claims remain separate obligations.

The selected standard supplies distinct module instantiation and invocation judgments, so the endpoint can name a standard execution rather than an invented evaluation function. [Pinned Core 2.0 module execution rules](https://raw.githubusercontent.com/WebAssembly/spec/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/modules.rst).

## Proposed exact contract

The notation below specifies required statements; it is not checked Lean. Use separate declarations rather than forcing ordinary clients to construct one universal certificate record.

Let `p : Source A B` have independently defined meaning `meaning p : A → B`. Let `encodeA`, `encodeB` map source values to ordered Wasm numeric-value lists. Define a fallible decoder on raw boundary values, including arity and type checks. For each ABI type prove:

```
decodeT v = some x ↔ v = encodeT x
```

This establishes rejection of noncanonical representations as well as successful round trips. Unit contributes no values; products concatenate left then right; Boolean leaves use exactly i32 0 or 1. Word codecs must fix bit order, unsigned interpretation, and modulo arithmetic. A packed word and a list of Boolean leaves are different ABI representations until related by a checked adapter.

Define fallible artifact construction `lower p = ok M` and a decidable supported-subset predicate. Prove on successful construction that `M` is in that subset, is valid under the selected standard rules, and exports the named function with exactly the ABI parameter and result lists. Specify no imports, start function, memory, table, globals, indirect calls, recursion, or unaccounted features. The success premise must be inhabited by retained nontrivial clients. Syntax/index/encoded-length bounds belong in admission; unbounded mathematical products do not imply arbitrarily large loadable binaries.

For arbitrary valid initial store `S`, construct a standard instantiation of this closed module with an empty import list, obtaining module instance `I` and store `S'`. Then for every source input `x`, exported-function invocation with `encodeA x` must have a finite standard reduction to exactly `encodeB (meaning p x)`. Expose the store/frame invariants needed for composition and repeated invocation. For the proposed pure subset, calls preserve the relevant store after instantiation.

An existential successful reduction alone is insufficient if the modeled relation also permits trapping or divergent executions. Prove determinism for the selected execution fragment, or an all-maximal-executions result; combine it with the finite successful reduction to exclude traps and divergence. Keep engine interruptions, fuel exhaustion, allocation failures, and embedding limits out of this abstract no-trap conclusion unless they are explicitly part of the chosen semantics.

The primitive and block lemmas should quantify over all generated intermediate states, operand-stack tails and local layouts satisfying their invariants. The existing `StackMachine.Certified.correct` (`Applications/Stack/Machine.lean:83–87`) is useful precedent: an empty-stack-only result is not enough to justify composition. A Wasm backend using fresh locals needs the analogous freshness and preservation theorem even if it does not lower through that stack machine.

Finally state a separate byte corollary:

```
lower p = ok M
BinaryDecodesCore2 bytes M
instantiate/invoke the exported function of that decoded M
⇒ the preceding standard execution and ABI conclusion
```

`BinaryDecodesCore2` must refer to the actual binary grammar, including complete consumption, section structure, indices, lengths, and numeric immediates. If the first emitter passes through WAT and WABT, both text generation and assembly lie inside this trusted correspondence premise. The spec separates function declarations and bodies into different binary sections, so testing instruction rendering alone misses module correspondence. [Pinned binary-module grammar](https://raw.githubusercontent.com/WebAssembly/spec/05ca4182176763112561ae20153975c12bd689e4/document/core/binary/modules.rst).

An external-run claim additionally assumes that the runtime loads those exact bytes, resolves the intended export, implements the relevant standard execution, and that the host supplies/reads the ABI values faithfully. Record bytes or their reproducible identity across emission, checking, loading, and invocation. A hash is useful bookkeeping, but comparing hashes is not a theorem about byte equality without the corresponding assumption.

## Concrete concerns and their status

**Established contract distinction: canonical input rejection is not Wasm type validation.** The standard i32 parameter type admits representations outside the Boolean subset. The existing finite-sum decoder starts with Lean `Bool` storage and cannot itself reject an incoming i32 value 2. Add a raw numeric boundary decoder before the existing finite-sum canonicality check. Specify whether rejection belongs to the host adapter or an exported wrapper. Host rejection is adequate if the public API is that adapter and the raw export contract explicitly requires canonical inputs. A claim that the bare artifact rejects arbitrary inputs needs checks in the artifact and an explicit error-result ABI.

**Established missing bridge: fixed-word arithmetic is not yet provided by the inspected Boolean adder theorem.** `Applications/Timing/Adders.lean:61–68` proves the three-bit full-adder arithmetic equation, not an all-width word32 compiler. The proposed word client requires a checked finite-bit/BitVec representation and composition proof, or locally proved i32 primitives. `Applications/Stack/Staging.lean` specializes `Int`; truncating its meaning would change its contract. Standard integer arithmetic is defined at a fixed width; cite those equations for the new bridge. [Pinned numerical semantics](https://raw.githubusercontent.com/WebAssembly/spec/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/numerics.rst).

**Established limit of validity: validity alone does not establish trap exclusion.** The standard instruction semantics has trapping cases for undefined numeric operations. Keep partial primitives out of the selected subset or prove their preconditions. Eager evaluation of both finite-sum arms remains sound for the current total gates; introducing a trapping primitive would require checking the inactive arm too, or changing lowering and proving a different execution theorem. [Pinned instruction semantics](https://raw.githubusercontent.com/WebAssembly/spec/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst).

**Established portability qualification: no 64-bit result cap does not mean unlimited execution support.** Core permits implementations to bound parameter/result/local counts and reject excessive modules during validation, compilation or instantiation. Keep product semantics general and make target/engine admission explicit. A mathematical termination proof does not prove acceptance or completion by every engine. [Pinned implementation limits](https://raw.githubusercontent.com/WebAssembly/spec/05ca4182176763112561ae20153975c12bd689e4/document/core/appendix/implementation.rst).

**Plausible specification risk: a local subset embedding can be circular.** An embedding into another locally invented AST proves no connection to the published standard by itself. Give every emitted instruction, module form, validation rule, administrative reduction, and invocation step an exact pinned rule reference. Formalize that connection inside an imported or explicitly transcribed standard relation. Human correspondence between the relation and the specification remains trusted when no authoritative mechanization is imported. Differential tests help find transcription errors but do not discharge this premise.

**Plausible state-boundary risk: output and state have the same low-level types.** Swapping fields can remain Wasm-valid while invalidating the source theorem. Name and preserve `(output,state)` order, compare every output and final state, and bind ABI version/layout to the checked artifact. `Program.transport` assumes an actual total backend transition; it cannot be applied directly to an external API returning load errors or interruption. Use the successful abstract transition for that theorem, and separately state the environmental conditions under which the fallible driver realizes it.

**Open implementation choice: trusted encoder versus stronger byte theorem.** The issue expressly allows a tested trusted encoding boundary. There is no foundations reason to block the first backend on a full verified parser. If translation validation is chosen, require a theorem `check p bytes = ok → artifact contract p bytes`, not `check M = valid`. A checker supplied with an externally parsed AST retains a parser premise and must bind that AST to the consumed bytes. `GraphTranslationValidator.check_sound` (`SquareKit/Internal/GraphTranslationValidator.lean:69–104`) demonstrates source and actual-artifact identity, but its Lean-expression checks are not a Wasm parser or validator.

## Smallest correction and separating cases

Revise the preparation into the three explicit statements above: standard AST execution, conditional binary correspondence, and conditional external realization. Add raw input admission, instantiation/export identity, and successful-termination/no-trap obligations. Preserve the existing circuit route, multi-value ABI and explicit-state clients. Avoid adding an external proof framework as a prerequisite unless inspection demonstrates a practical benefit.

Proposed checks, all still unexecuted:

| Case | Required observation | What it separates |
|---|---|---|
| Unit, nested products, and output containing three word32 values | Exact list arity/order, all 96 output bits compared | Eliminates unit-slot mistakes, product reversal, and a hidden 64-bit truncation |
| Composed selector `f(tag,x,y) = (if tag then x+y else x xor y, x, y)` over word32 | For `x=0xffffffff,y=1`, true gives `(0,0xffffffff,1)`; false gives `(0xfffffffe,0xffffffff,1)` | Wraparound, branch choice, and complete wide output; add a nonoverflow carry-chain case |
| Raw Boolean/tag 2; missing/excess fields; nested inactive payload changed from zero | Adapter rejects before invoking the proved function | Prevents silently using Wasm truthiness or dropping hidden inactive payloads |
| Two native delays, seeds `(false,false)`, inputs `[true,false,true]` | Outputs `[false,false,true]`, states `(true,false)`, `(false,true)`, `(true,false)` | Reinitialization and state-order errors; expected values follow by expanding `delay` and `seq_machine`, not by running an emitter |
| Mutate one constant, export index, or output/state local index while preserving Wasm validity | Correspondence/translation check rejects, or trusted-encoder regression catches the changed result | Demonstrates why validation does not establish source preservation |
| Malformed/truncated bytes and unsupported instruction/module forms | Parsing or subset admission rejects with a distinct outcome | Distinguishes binary decoding, standard validity, and compiler feature admission |
| Deliberate trap fixture and external interruption/resource failure | Harness reports failure, never a source result | Exercises outcome classification; it does not refute abstract termination of admitted generated code |

For a trusted encoder, tests can expose mistakes but cannot certify all emitted artifacts. For a proved serializer, prove the serialization relation for all admitted modules and retain runtime tests because the external engine and host remain outside that theorem. For a sound translation validator, include a valid positive instance to rule out an always-rejecting implementation and mutation cases to challenge source/byte binding.

## Evidence and limits

I inspected the accepted source via `git show` and declaration searches, with detailed reads of the frontend laws, finite-sum codec/lowering, state transport, and existing translation-validator contract. The proposed word32 case is new mathematics to formalize; the two-delay oracle is a paper expansion of inspected definitions. No Lean build, proof audit, runtime installation, emission, external execution, or checker experiment was performed. Unrelated working-tree verification changes were excluded from the code assessment.

I read the pinned Core 2.0 primary sources linked above. The pinned WasmCert-Coq README at `58a3d3f8b7af4dc8aa9351f254a9e672643b21f8` describes type-safety/checker/interpreter/instantiation results, but explicitly calls its binary parser unverified; importing that project would therefore not automatically establish the byte endpoint. It also includes extensions beyond Core 2.0. I did not audit theorem dependencies, licenses or cross-prover transport sufficiently to recommend adopting it. [Pinned WasmCert-Coq scope](https://raw.githubusercontent.com/WasmCert/WasmCert-Coq/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/README.md).

This assessment received the neutral brief and its linked preparation, which already recommends a candidate. It had no prior involvement in that preparation and did not read other lens reports or coordinate conclusions. The invocation supplied repository/user guidance; fresh-context independence is limited by the shared brief, common model and common evidence. Agreement with another lens would need checking against these shared assumptions.
