# Retained incremental-search transport

[Transport.lean](../../Applications/Search/Incremental/Transport.lean) moves a
native incremental-search session through a supplied bijection of `Fin n`.
It maps the graph, endpoints, heuristic, all `g` and `rhs` entries, and the
queue in its existing order. Batch assignments retain their order and repeated
writes. The inverse recovers the raw state, graph and batch exactly.

The migrated session retains every clause of `Valid`: the rhs equation,
queue uniqueness, exact queue membership for inconsistent vertices, and
nonnegative labels. Positivity and heuristic consistency transport separately.
`distance` transports rational walk existence and optimality, including
unreachability. The native API returns a cost; its attainment theorem is
existential and supplies no executable selected path.

`begin_correct` reuses `Session.begin_correct`. `advance_correct` executes
native repair from the migrated retained state and reuses
`Session.advance_correct`. `advance_observe` uses `distance_unique` to compare
its distance with the source repair. `History` retains the full session at
every subsequent batch, with dependent positivity and heuristic evidence;
`history_correct` gives correctness at every observation.

Arbitrary permutations can change successor enumeration, queue ties and the
retained state after a native repair. `Ordered` requires equality of the actual
successor lists after mapping. Under that condition, `run_map` preserves the
literal fuelled execution, including exhaustion and full terminal state;
`repair_map` and `history_map` preserve complete continuations. A repair needs
the condition only on its final batch graph. The
[checked examples](../../Examples/IncrementalSearchTransport.lean) include a
nonidentity permutation, residual inconsistent state, two successive repairs,
loss and restoration of reachability, repeated writes, a sparse ordered case,
and an equal-key fork whose native queue order changes.

Direct callers retain the native API. `square_correct` uses the existing
`repairDistanceSquare`, which composes repair and observation through
`Relational.compose`; the client still supplies graph, batch and invariant
transport. `stateAdapter` uses the supplied executable-bijection adapter from
#533. Its tariff is one conversion call, not memory-copy work or a comparison
of search costs. No operation-cost invariance is claimed under permutation.
The unary state package from #530 does not account for this client's changing
graph and dependent batch evidence, so this client does not route through it.
