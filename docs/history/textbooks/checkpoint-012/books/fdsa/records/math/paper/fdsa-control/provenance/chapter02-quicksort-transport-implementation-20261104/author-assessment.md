# Actual quicksort mapping transport: author source assessment

Author root; complete new source and proofs read. This is an uncompiled development candidate, not an elaborated-type assessment, independent review or acceptance. Existing source, public roots and pins are unchanged. The pre-existing source-tree cache was neither read nor built or modified.

Candidate: `e71092c38cf68cae5b984fd9cea85c9f5b34a570`; parent `0ec9954479b081664bd4504c90fb66fba5fd22c8`.

| Declaration | Complete intended contract and source assessment |
|---|---|
| `Resources.QuickSort.run_map` | Independent payload universes; arbitrary f and Bool comparator; complete actual returned pair, with pulled-back comparator. Both filters and recursive results are retained. No injectivity or payload instances. |
| `Resources.QuickSort.counts_map` | Actual exercise/append pair projection of run_map; no surrogate cost. |
| `Resources.QuickSort.exerciseCost_map` | Existing first cost projection preserved. |
| `Resources.QuickSort.appendCost_map` | Existing actual append count projection preserved, including terminal calls. |
| `Resources.QuickSort.literalCost_map` | Existing sum of actual exercise and append coordinates preserved. |
| `Examples.QuickSortTransport.arbitrary_occurrence_lookup` | Actual Fin xs.length occurrence lookup preserves full run. The label list need not be complete or Nodup; payload remains arbitrary. |
| `Examples.QuickSortTransport.arbitrary_occurrence_costs` | All three cost projections consume their public transport APIs with the same label list and comparator. |
| `Examples.QuickSortTransport.noninjective_constant_run` | Bool-to-Nat constant map is explicitly not injective; still preserves actual run and all duplicate occurrences. |
| `Examples.QuickSortTransport.duplicate_fixture` | Three distinct occurrence positions map to three equal values, actual exercise25 and append9; uses run_map then existing run_cons. |
| `Examples.QuickSortTransport.empty_uninhabited` | Empty source type, no default or nonempty assumption; uses actual count transport and nil execution. |
| `Examples.QuickSortTransport.comparator_cost_boundary` | Two concrete Bool branch choices have actual literal19 versus20; shows comparator correspondence matters, without claiming cost invariance for unrelated comparators. |

No source-level mathematical findings. Compilation may identify API/elaboration corrections; retain failures and do not weaken contracts. Full central focused build, all11 explicit types, independent chapter reviews and integrated candidate gates remain pending.
