# Successful cache writes: implementation handoff

Local10020 bounded worker Map completed this slice within root's existing
implementation loop. Only CacheWrite.lean and Examples/SuspensionCacheWrite.lean
were edited; root owns Git and integration. All proposed public signatures are
retained. Both files are frozen after focused r2 success.

## Public statements

- cacheWrite_event_iff identifies exactly a value returning through the top
  memoize frame for the event address. No occupied-thunk premise is added.
- Settled is HasValue plus absence of any pending frame at that address.
  OutcomeSettled retains only the value fact in a finished answer.
- Settled.no_cacheWrite excludes the immediate cache-write event.
- step_settled preserves the property with bounded input memory.
- cacheWrite_settles removes the unique pending occurrence, using pending-list
  Nodup; it establishes the immediate post-step property, not output bounds.
- observe_settled, observe_unfinished_settled and observe_no_cacheWrite use
  ConfigBounded for all later actual prefixes, including completed answers.

The raw statements assume no purity, typing, primitive compatibility,
termination or nonreentry. HasValue fixes the cell constructor, not its
payload. ConfigBounded remains separate from immediate successful-write
provenance. The pure source count theorem belongs to later layers.

## Connected cases

The first successful force reuses the Pending client's actual body entry and
Nodup proof. Its five transitions write on the third step and settle the
address before inner matching. Arbitrary later unfinished prefixes exclude a
new write; an absorbing budget suffix adds no machine work.

An older same-address frame survives an inner successful write. That value
cell is not yet settled: three later transitions reach the older return, which
overwrites7 with8. The complete raw continuation takes seven transitions.
No pure source reachability is asserted for that raw counterexample.

Assignment of any Value Unit takes six transitions, emits referenceWrite and
retains Settled at every actual unfinished prefix. The7-to8 specialization
checks explicitly that payload equality is not part of the invariant.

The existing outer-exception source case has two body entries and one cache
write. It retains the inner cached7 when the outer body raises; a later force
takes the actual hit and remains settled. Exceptional unwinding skips the
current frame's write but retains memory actually reached.

## Validation

r1 ended1 on an unavailable List.not_mem_cons.mpr helper and its downstream
no-goals diagnostic. Map replaced only that proof step by
simp only [List.mem_cons, not_or]. No public statement, premise, transition or
expected example result changed.

r2 ran2026-11-02T23:15:23–23:20:11Z, terminal0,751 jobs. Core191s; client70s.
All26 source/config inputs remained unchanged. The recorded starting HEAD
was78ed1a1501a955a5579a7a098910a5d4bc1361be; the authorized uncommitted proof
correction is captured by its exact input hashes. Preserve both rounds:
validation/suspension-cache-write-r{1,2}.{json,log}.

Frozen CacheWrite SHA256:
95e3cad6dfc478ec88d3f4f442a077bd3533395a8987731dc2edd33444e35347.
Frozen example SHA256:
a342c700c663f64d8c0456b050e9c3717ee92dfeb4b577387b68c221454ba7bc.

Focused compiler ownership was released to Ordered for CacheAccounting.
This handoff is implementation statement review, not independent Standards
or Spec approval. Complete candidate validation, exhaustive audit, both
independent review axes and immediate final verification remain required.
