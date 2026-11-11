# Dynamic arrays: reconciled assessment

Compare two named insertion policies over shared concrete storage primitives and existing `Resources.run`. Preserve raw execution, ordered events, insertion boundaries and invariant-qualified refinement. The reports favor this bounded experiment; they do not justify a general storage hierarchy or adopt a new architecture.

No integrated literal/eager resize implementation was found at the assessed revision `e80c51d968925be3809ba3acc3259de7041b504b`. Existing fixed buffers, vector stores and resource accounting remain useful owners. The contract lens also inspected historical implementations; its opening recommendation concerns preserving their mathematics in a future native construction, not retaining an already integrated dynamic-array API.

## Reconciliation of uneven source evidence

The implementation and alternatives lenses left raw copy semantics and some potential domains unresolved because they did not inspect the archived definitions. The contract lens inspected those files. The coordinator then independently read the relevant definitions and signatures and recomputed their hashes. They match the recorded members in `docs/research/adwh-preview-233-inventory.json` and `adwh-reconstruction-map.json`. [The source check](source-check.json) records the hashes and limits. No historical proof was replayed.

This resolves three factual questions:

- Historical `copyInto` consumes a fixed list of source values and applies total `Array.setIfInBounds` updates to its destination. It does not reread the progressively modified destination. A live-read overlapping-copy operation would be a different extension, not an unresolved convention of this source operation.
- Both policies' work and allocation potential inequalities quantify over all raw states. Their existing scope can use the current generic telescope. A hypothetical invariant-only future policy may need a restricted theorem, but that is not required by these inspected source statements.
- Eager spare-space and balance results require layout and positive initial free space. Layout alone is insufficient. Capacity-growth accounting has a broader raw-state domain. Preserve these distinctions when rebuilding useful claims.

This evidence is historical source inspection, not book verification or native acceptance. The owner's criteria still govern which capabilities to preserve or improve.

## Shared mechanisms and information to retain

Use the existing measured bind, workload execution, invariant/fusion and additive reweighting laws. The policy steps can share allocation, copy and write functions without a new command language or law-field hierarchy. Keep their differing growth predicates, semantic refinement and local potential arguments explicit.

Raw state accepts natural cursors, zero capacity and malformed states. A valid carrier can serve refined clients, but must not become the only executor if that discards the intended raw behavior. Existing `Fin`-indexed stores can support bounded suboperations; they do not already supply the whole raw dynamic domain. Preserve the arbitrary surrounding prefix/suffix copy theorem. Strengthening its currently blank destination window to arbitrary overwritten contents is a proposed additional theorem, not established by this assessment.

An ordered event word must retain allocation size and copy/write payloads, including zero-slot allocation. Counters lose distinctions needed by arbitrary tariffs. An insertion should also retain its event block: flattening `[[a,b]]` and `[[a],[b]]` loses the different bill boundaries. A wrapper around the same step can retain grouping without replaying storage execution.

Package an additive list-price function for existing `reweight_run`. Exact repricing does not imply the same amortized constant for every tariff. Nat-valued additive prices alone also cannot distinguish permutations, so retain the independent event-order requirement. Both endpoint potentials remain part of workload accounting.

## Discriminating comparison

1. Implement one total snapshot-copy primitive and both named policy steps, comparing direct local steps against shared primitives. Preserve attempted out-of-range event behavior separately from in-bounds layout theorems.
2. Check arbitrary destination prefix/window/suffix preservation, empty and boundary windows, repeated commands, malformed cursors and zero capacity. Distinguish zero allocated slots from one allocation/growth event.
3. Replay the same three- and four-insertion examples under both policies, with independent full states, ordered event blocks, work/allocation/growth projections and per-insertion bills. The historical short totals remain fixtures to check in the native implementation; this investigation did not execute them.
4. Retain the full-singleton negative control for eager positive-spare balance, non-power capacities, empty command lists and nonzero initial potentials. Prove each result at its exact domain rather than imposing one universal validity premise.
5. Exercise arbitrary additive repricing and an order-retaining observation. Compare actual repeated obligations and native client usability before selecting a broader interface. A command language or backend abstraction needs another real interpretation or transformation to justify its added machinery.

The recommendation preserves the option of two local policy executors sharing only primitives and copy lemmas. It makes no physical allocation, ownership or machine-time claim. Fixed byte-buffer clients remain unchanged in any proposed comparison.

All three initial reports are retained: [contract](contract.md), [implementation/use](implementation.md), and [alternatives/generality](alternatives.md), with the [brief](brief.md). They used independent fresh contexts and undisclosed initial reports, without model diversity. The coordinator resolved the source-access disagreement after all reports were saved. No new Lean build, experiment or performance trial was run; broader adoption remains for owner discussion.
