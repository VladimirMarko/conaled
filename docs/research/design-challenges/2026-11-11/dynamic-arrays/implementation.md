# Dynamic arrays: implementation and use assessment

Assessment of pinned revision `e80c51d968925be3809ba3acc3259de7041b504b`, inspected in `/tmp/conaled-wave-20261111/design-challenges/source`.

## Recommendation

Build two concrete insertion policies over a small common storage and ordered-event implementation, reusing `Resources.run`. Share the copy-window proof and observation transport. Keep policy transitions, layout preservation and potential inequalities separately stated. A general storage hierarchy has no demonstrated consumer requirement in the inspected material. Two local executors sharing copy lemmas remain a reasonable first implementation if their primitive behavior and event equations are kept identical; a common executor should earn its place through these two callers.

This is a recommendation for a bounded implementation experiment, not an adoption decision. The pinned repository contains useful fixed-capacity operations and cost infrastructure, but the inspected owners do not implement the literal/eager resize policies. `docs/research/adwh-recovered-handoff.md`, the “Literal and eager dynamic arrays” row, explicitly lists resizing, full copy windows, arbitrary prices and policy potentials as remaining work. Existing buffer proofs should survive unchanged as useful mathematics and clients.

## Strongest retention evidence

`Applications/Resources/Measured.lean` defines `Measured`, `bind`, and `reweight` using ordinary pairs. `bind_assoc` assumes an additive semigroup, not commutativity. `Applications/Resources/Workload.lean` supplies `run_append`, `reweight_run`, `run_invariant`, and `run_value_fusion`. These already separate execution, observation and invariant-dependent semantics. Neither a new command language nor a storage class is required to get those benefits.

Actual clients support this assessment. `Applications/Resources/RandomAccess/Observation.lean` builds `measuredUpdateQuery` by square composition, obtains cost addition definitionally, and applies `reweight_run` in `bulkRun_reweight`. The valid carrier is imposed at the client boundary; underlying `bulkRun` still accepts the raw representation. `Examples/ByteBuffer.lean` exercises overflow, invalid cached state, successful and failed traces, conversion and zero capacity. This is evidence for retaining explicit validity boundaries and executable specializations, rather than treating the raw state domain as an inconvenience.

## What the existing storage implementations provide

| Owner and declarations | Implemented behavior | Limitation for the proposed policies |
|---|---|---|
| `Applications/Dijkstra/Store.lean`: `Store`, `lookup`, `write`, `lookup_write`, `accum`, `accum_lookup` | `Vector α n`, indexed writes and ordered repeated updates; `accum_lookup` handles duplicate indices through `valuesAt` | Fixed capacity and `Fin n` indices. No dynamic allocation or arbitrary raw natural-index executor |
| `Applications/Resources/Dijkstra/StoreCosts.lean`: `copy`, `copy_value`, `associationStep`, `bulkRun_exact` | Whole-store `Vector.ofFn` copy, then measured ordered updates; modeled work `n + 3 * ivs.length` | Copy has no destination window; scalar `Nat` cost cannot recover allocation/copy/write ordering |
| `Applications/Sequences/BoundedSummary.lean`: `Buffer`, `push`, `decode_push`, `tryPush` | Initialized Boolean slots with a bounded prefix length; one indexed append, refusal at capacity | Capacity is a type parameter; resizing and front-array layout are absent |
| `Applications/Sequences/ByteBuffer.lean`: `Machine`, `push`, `convert`, `copy`, `attempt` | Finite byte slots, finite counter, explicit allocation/output refusal and trace refinement | `convert` copies all slots at the same capacity. Its comment explicitly leaves physical separation to an adapter |
| `Applications/Resources/ByteBuffer.lean`: `Events`, `events`, `measuredConversion`, `projected_cost` | Per-operation multiplicities, modeled payload peak, tariff projection to an existing client theorem | `Events` stores counters, not an ordered event word. It cannot distinguish permutations with identical multiplicities |
| `Applications/Sequences/LCA/Control.lean`: `fillLoop`, `fillLoop_value`, `tabulate_value` | An existing ordered fill loop over actual vector writes, with an extensional tabulation proof | Specialized finite-index allocation and control accounting, not a resizable-array policy |

These are capability limits, not defects in their declared contracts. In particular, `DijkstraStore.copy` is extensionally the identity by `copy_value`; its modeled copy charge is not evidence about Lean's physical allocation. Likewise, byte-buffer `conversion` describes a contract with ownership obligations, not a verified allocator implementation. A new dynamic implementation must state the same execution boundary honestly.

## Copy windows and the executor domain

The useful shared lemma is a destination preservation theorem: copying a selected source segment into a destination window changes that window and leaves arbitrary surrounding prefix and suffix unchanged. A fresh-allocation-only theorem cannot establish this, because initialization erases the surrounding-data obligation.

`Dijkstra.Store.lookup_write` supplies the one-step reasoning principle. `accum_lookup` already supports repeated destination indices. Only `valuesAt_map_unique` introduces `Nodup`, and it does so for the specialized conclusion that each selected cell has exactly one associated value. That separation is worth preserving. A simultaneous batch specification may need distinct indices; the ordered executor does not acquire that requirement merely because one corollary does.

The raw total executor's treatment of malformed cursors and out-of-range indices must be fixed before choosing `Fin`-indexed commands as its public domain. Requiring every command to contain a bounds proof would exclude the raw executions named in the brief. An internal finite-index write after a runtime branch can still reuse the vector lemma. A raw list-backed model with total indexing/update conventions is another viable first owner. The distinction is between representations and domains, not between proof quality levels.

Copy source semantics also need an explicit decision: a captured source snapshot and reads from the progressively modified destination differ on overlapping windows. Neither `copy_value` nor the existing fresh tabulation theorem decides the intended behavior. This is an unanswered specification question to resolve against the recovered policy definitions before claiming general overlap preservation.

## Event and price obligations

Use an ordered free additive observation for primitive allocation, copy and write events. A zero-slot allocation must remain an event: an allocated-slot projection may yield zero while a growth-count projection yields one. Current byte counters collapse this distinction if used as the sole observation.

`reweight_run` already transports any additive homomorphism through the same state trajectory. For an original list price satisfying empty and append laws, package that function as the corresponding homomorphism. Its determination by singleton prices follows by list induction; this does not require an extra independent proof field. A formal implementation should prove this adapter, including arbitrary prices, rather than only instantiate work and allocation tariffs. Noncommutative observations provide an especially useful check that order was not accidentally discarded.

Per-insertion grouping must be produced while insertions execute. A grouped observation such as a list of event lists can be flattened and priced, but a flat trace cannot recover its original partition. For example, `[[a], [b]]` and `[[a,b]]` flatten to the same word and have different numbers of bills. This is a paper counterexample about lost information, not an executed Lean fixture. Shared primitive execution can return each insertion's event word; an outer runner can append that word as one bill. No separate replay of policy transitions is needed.

## Obligations that remain policy-specific

Each policy builder must establish its actual allocation/copy/write order, raw transition equations, layout preservation, decoded insertion semantics, and local potential inequality or identity. Shared copy lemmas and `run_value_fusion` remove duplicate loop arguments but cannot establish these policy facts automatically.

A proof of layout preservation need not imply positive spare capacity. A valid full singleton separates those claims, as the recovered research note observes. Require positive free space only where the particular balance or spare-space theorem needs it. Arbitrary initial states, empty workloads, non-power capacities and malformed raw cursors must retain their own equations even when they cannot satisfy a layout theorem.

`Applications/Resources/Potential.lean` already retains both boundary potentials in `run_potential` and `run_potential_exact`. Its `initial_potential_matters` is a concrete source theorem showing why deleting the initial potential is unsound in general. There is a practical integration detail: `run_potential` takes a local inequality for every raw state. If a policy inequality holds only under layout, use a valid carrier or prove a reachable-invariant version from `run_invariant`; do not silently strengthen the raw executor's input type. The invariant-restricted telescope is a proposed small derivation, not a theorem checked in this assessment.

Changing the price model also changes what potential bound can be claimed. Transporting an exact event observation to any additive price is distinct from proving one uniform scalar amortized constant for all such prices. A caller may obtain exact repricing without any monotonicity assumption; transporting inequalities requires the relevant order-preservation hypotheses, as `Measured.reweight_bound` already makes explicit.

## Discriminating experiment and acceptance evidence

Implement both policies locally with the same primitive owner, and make the following cases checked clients before considering a wider hierarchy:

1. Copy a nonempty window into a destination with nonempty, unequal sentinels on both sides. Prove arbitrary prefix/suffix preservation parametrically, plus empty and boundary windows. Include overlapping-source cases according to the chosen source semantics, repeated commands and out-of-range raw commands with their specified behavior.
2. Run identical insertion lists `[1,2,3]` and `[1,2,3,4]` from the empty state. Check full ordered event words, grouped bills, final slots/layout, capacity/free space and price projections. The table in `adwh-recovered-research.md` predicts opposite work comparisons for these two workloads; it labels them source-only future fixtures. This assessment has not independently checked those totals.
3. Check zero-capacity allocation with separate growth and allocated-slot prices. Check full singleton, malformed cursor, non-power capacity and empty workload from arbitrary initial states. Record exactly which raw equations survive and which layout conclusions fail.
4. Prove the arbitrary-list-price adapter and reweight theorem. Test an order-retaining observation as well as work, allocated slots and growth counts. Check grouped and flattened observations against the same transition result.
5. Apply the existing telescope with both boundary potentials. Where layout is necessary, expose that assumption in the local theorem and retain a raw operational definition. Compare proof obligations and client signatures for two local executors versus one shared executor.

The final comparison should count repeated proof arguments and inspect caller assumptions. Fewer declarations alone would not show better author usability. A successful small implementation could justify extracting a reusable owner; failure to preserve raw domains or grouping would justify retaining two local executors while correcting the shared interface.

## Exposure and validation limits

I had no prior involvement in this design and read no other lens reports or coordinator conclusions. This agent received the shared brief, repository guidance and local evidence pointers. The parent did not request a different model; this assessment supplies an independent context, not evidence of model diversity.

This report is source inspection and explicitly marked paper reasoning. No Lean compilation, proof audit, runtime benchmark or private experiment was executed. Searches and reads covered the pinned current owners and clients cited above; the historical literal/eager source definitions were not available through the inspected tracked paths. Consequently, I do not independently establish their precise transitions, reported short-trace totals, or book correspondence. No external factual claims or upstream capability comparison are made. Concurrent uncommitted #472 work was excluded. No target source, issue or other report was changed.
