# FRP integration

This records the disposition of [issue #26](https://github.com/VladimirMarko/conaled/issues/26)
against the preserved [discussion](history/frp/frp-chat.md) and
[mathematical notes](history/frp/event-denotations.md). The
[import inventory](history/frp/README.md) supplies the artifact mapping and
original verification evidence. The five historical artifacts retain their
original contents. Current declarations live in `Applications/FRP/`.

## Claims and scope

| Originating claim | Current evidence and disposition |
|---|---|
| Response 1 §1: historical Reactive failures | Historical source synthesis, not a Lean theorem or a reproduced runtime failure. It distinguishes library strictness/ownership problems, confirmed RTS bugs, and unresolved failures. Integration does not infer that one RTS fix repaired Reactive. |
| Response 1 §2.1: finite past interprets “discretely non-empty” | Corrected by response 2: timestamp monotonicity alone does not imply finite history. `eventEquiv` covers the maximal total raw carrier; `totalEventEquiv` separately restricts it. Neither identifies Elliott's intended image from an informal comment. |
| Response 2 §§2–4: total co-lists and exact grouping | Checked in `Equivalence.lean`: `finite_or_infinite`, the rank enumeration, `eventEquiv`, and `admissible_iff_representable`. Order and multiplicity remain observable. |
| Response 2 §§5–6: why finite history is needed | Checked necessity for lossless merge with arbitrary singletons, and the empty-or-last characterization. Infinite batches and Zeno examples retain raw round trips and fail finite history. |
| Response 2 §6 and notes: conversion to native `List` | Now checked in `Finite.lean`: `CoList.exists_list`, both directions of `Native.equiv`, and `Native.oldEquiv`. Finite support yields a finite union of finite index sets; finite occurrence history yields finite support by timestamp projection. |
| Response 2 §7 and notes: stable merge | Now checked: `Native.merge`, `group_merge`, `merge_preserves`, `merge_left`, and `merge_right`. Chronological rank enumerates the concatenated finite batches; each right batch starts after the left batch's length. The output has finite history. This is a total mathematical construction, not a lazy merge evaluator. |
| Response 1 §2.2 and response 2 §7: pointwise behaviors, event map, snapshot | Existing Reader equations, `OldEvent.group_mapWithTime`, `group_map`, and `group_snapshot` are checked. Mapping does not require finite history. `never`, `once`, map, merge, and snapshot in the native model prove finite-support closure. |
| Response 1 §2.3 and response 2 §7: switching | `Realization.before_eq` and `switcher_eq` preserve strict histories and last selection between chronological co-lists and co-list batches. Native `Event.switcher` folds sorted finite batches; `switch_at_change` checks the strict boundary. The new carrier equivalence is not presented as a theorem transporting every native operation, including this fold, at once. |
| Response 1 §2.4: semantic equality and laws | The FRP compatibility facade now consumes shared `RawMap.induced`, category congruence/law transport, product comparisons and product-law transport. Equality remains equality of denotations, not program storage. |
| Response 1 §2.5: causality, integration, detector, feedback | `AgreeThrough`, `Causal`, and `CausalMap` state the ordinary behavior contract. No recursive higher-order causality theorem, analytic integration contract, sparse detector contract, or feedback implementation is claimed. Unrestricted `warp` is an offline denotation. |
| Response 1 §3.2–3.3: RNF and frontiers | `RNF.denote` and `Prefix.Sound` are specifications. They do not prove a normalization pass, complete-batch protocol, residual-state initialization, or source progress. |
| Response 1 §3.4–3.6: scheduler and operational proofs | Proposals: pure graph transitions, push phase changes, pull evaluation, soundness for all input completions, schedule independence, productivity, cancellation ownership, reclamation and conditional costs. No runtime is implemented here. |
| Response 1 §3.5: nested ordered bind | The retained Python counterexample checks failure of associativity under max-retiming and stable ties. It is not a reproduction of Reactive's bugs. No lawful Event Monad is claimed. |
| Response 2 §8: lazy evaluation and missing primitive semantics | Total functions/co-list spines exclude bottom and partial elements. Mathematical `before` does not certify termination of lazy `filter` followed by `last`. Neither `predicate` nor `integral` receives invented semantics. |

The runtime, partial-information, analytic-primitive and feedback proposals are
tracked in [#27](https://github.com/VladimirMarko/conaled/issues/27). That issue
requires a scope decision before runtime implementation. This follows #26's
explicit runtime exclusion; it does not defer either requested carrier/merge
bridge. There is no unconditional lossless raw merge: an occurrence after a
Zeno history would require a position after all natural indices.

## Architecture and Felix comparison

The comparison uses Felix revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490` from [SOURCES](SOURCES.md).
The inspected primary definitions are
[`Homomorphism.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda),
[`MakeLawful.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda), and
[`Construct/Comma/Type.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda).

Felix separates object/arrow maps, `CategoryH`, product comparisons and
`CartesianH`; `MakeLawful` pulls laws back along a homomorphism using induced
equality. The accepted shared Lean infrastructure already provides these
capabilities through `RawMap`, `MapLaws`, `ProductMap`, and transport results.
FRP now supplies its existing local preservation facts to those interfaces.
`Homomorphism.comp_assoc` consumes the transported category laws. Clients also
receive both identity laws, composition congruence, and all product laws without
reproving their semantic calculations. `composed_semantic_map` composes the FRP
interpretation with `FunctionCategory.toTypes`; `semantic_pair_eta` exercises
product transport. No interpretation injectivity is required.

The original `Raw`/`Homomorphism` fields remain for source compatibility.
`categoryOps` and `productOps` project their reusable structure; `semanticMap`
provides the identity object map. The cost is a few definitional projections
and identity product comparisons, not new runtime data or stronger assumptions.
FRP primitives remain specialized proof fields because there is no second
primitive-signature consumer that would justify a new generic FRP framework.
The shared map API remains available independently of that facade. Terminal
preservation remains in the legacy facade; this change does not introduce a
new terminal adapter just to bridge `Unit` and the shared `PUnit` convention.

Felix's comma object is a semantic arrow; its morphism stores two arrows and
a commutation proof. `finiteRep`, `mergeSquare`, and `observeSquare` use the
existing exact function-square specialization of that construction.
`merge_observe` composes these squares, then `merged_native_roundtrip` checks
ordered duplicates through the public result. The raw map example remains
valid for infinite and Zeno events. A new general comma wrapper would add
comparison bookkeeping without changing these exact carrier statements.

A realization *relation* is appropriate for approximate execution or a behavior
handle with its whole-function contract. Here the bridges are exact bijections;
replacing equality by an arbitrary relation would weaken the result and require
clients to reconstruct uniqueness. The existing relational/witness-square
infrastructure remains the intended route for those future implementations.
Neither the legacy facade nor these exact squares establish the full Lean/Felix
comparison (#25) or the broader port (#8).

## Statement review and checks

The first checked case was an arbitrary finite batch round trip, including the
empty list and repeats. The missing connection was the native-list inverse of
`CoList`; `ofList_injective` and `ofList_toList` now discharge it. The next case
merges `[3, 3]` and `[7]` at time 2 and obtains `[3, 3, 7]` through public square
composition. The positional merge laws cover every input timestamp and valid
left/right batch index, not only that example. `ticks_roundtrip` accepts an
infinite event at natural-number timestamps using `ticks_finiteHistory`; this
checks that the bridge does not require a finite whole future.

Statement review checks that `CoList` conversion assumes only finite positions,
that the event conversion quantifies over every real observation time, and that
finite history never means a finite whole future. Extracting finite batches
uses the existing `NoMaxOrder` theorem, instantiated at real time. The support
proofs concern occurrences, not just distinct values. Merge uses explicit
left-before-right concatenation and retains repeated values. Its hypotheses
exclude the retained raw counterexamples. The law-transport changes preserve
the original associativity statement and assumptions; the new laws use induced
semantic equality and identity product comparisons.

Reproduce validation in the pinned environment:

```sh
direnv exec . lake build Examples.FRP
direnv exec . ./check-foundation.sh
direnv exec . ./check.sh
direnv exec . lake env python3 scripts/test-proof-audit.py
direnv exec . python3 docs/history/frp/ordered_event_bind_counterexample.py
```

Validation on 2026-10-18 passed the targeted `Examples.FRP` build, the
dependency-free foundation check, and the fresh 97-module source check including
`Finite.lean` and the infinite-future tick example through the public entrypoint.
The exhaustive transitive audit passed with exactly `propext`, `Classical.choice`,
and `Quot.sound`. The historical Python counterexample passed its assertions.
The five original artifacts were compared byte for byte with the integration
starting commit; local Markdown links and `git diff --check` also passed.
The documented audit regression command passed all four cases: unused external
axiom, private transitive axiom, private admission, and source unsafe declaration.
