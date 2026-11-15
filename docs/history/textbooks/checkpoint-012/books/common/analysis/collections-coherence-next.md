# Collections coherence: next mathematical step

**INT-020/021 — uncompiled follow-up, outside accepted integration.** Read-only assessment of candidate `f52a47b9e240b3937533f48befb8622527b7f6db` in `integration-20261113/fixes`. No source, index, refs or compiler changes.

## Inspected sources and ownership

| Source | Exact paths |
|---|---|
| Current PFDS integration | `Applications/Search/OrderedMap/Interface.lean`, `Applications/Search/OrderedMap/Basic.lean`, `Applications/Search/AbstractSet.lean`; existing relation owner `SquareKit/Relations.lean` |
| XA01 donor `20a5b5537a704be016d09e4eb31db0dad8a12d61` | `Applications/Collections/Map.lean`, `Applications/Collections/AList.lean`, `Applications/Collections/Modify.lean`, `Applications/Collections/Set.lean`, `SquareKit/ValidGraphs.lean` |
| Frozen VFA preparation | Checkpoint `books/vfa/records/math/drafts/table-specs/TableObservations.lean` |

Keep **`Search.OrderedMap` as the owner of shared partial lookup/write semantics** and **`Search.AbstractSet` as the insertion/membership owner**. XA01 supplies additional deletion and modification contracts; VFA supplies default/presence observations and concrete realizations. Integrate these through adapters and optional capabilities, without another generic client framework or requiring deletion from every PFDS map. Share the minimal update/client proofs rather than importing competing versions of them.

## 1. Map realization and validity

Current `OrderedMap.Ops` has `empty`, `bind`, `lookup : K → M → Option V`; `Laws` relates these to a separate `observe : M → K → Option V`. XA01 has `update`, `delete`, and lookup with reversed arguments; its laws hold only on `Valid m` and use lookup itself as abstraction.

For XA01 law evidence `h`, construct the minimal current operations on `{m // Valid m}`: empty carries `h.empty_valid`, bind uses `update` and `h.update_valid`, lookup flips arguments. Observe by `fun m q => ops.lookup m.val q`. Prove its `OrderedMap.Laws` using `lookup_update_eq` and the extensional identity

`Function.update f k (some v) = OrderedMap.write k v f`.

This follows PFDS's existing `Tree`/`trees_laws` construction. It does not assert the update equations on invalid raw states. For raw carriers, retain the restricted graph `Valid m ∧ lookup m = meaning`.

The XA01 `ValidGraphs.liftFun_iff` identifies preservation with **both** output validity and the decoder equation on valid input. Keep it as a small bridge to existing `Relational.RelRep`/`RelSquare`, with `preserves` identified with `Relator.LiftFun`; `comp_iff` must retain intermediate validity. No second composition machinery is needed. Current `RelRep` and map declarations share one universe, whereas XA01/VFA use independent universes: preserve the latter at the algebra/relator layer and explicitly scope any square adapter requiring a common universe.

PFDS's raw `lookup_bind` is unconditional, but equality with its independent whole-tree `observe` requires `OrderedBy`. For example, root `(0,"root")`, left child `(1,"hidden")`, and empty right gives directed lookup at one `none`, but whole-tree observation `some "hidden"`. Do not remove that invariant merely because directed lookup satisfies an update algebra.

## 2. Sequential updates and representation agreement

For any two lawful realizations, corresponding valid starting states and **every** binding list, derive equal final partial observations from existing `Laws.bindAll_correct`/`lookup_bindAll`. The relation includes validity plus equality of lookup functions, and each intermediate update must preserve validity. Retain repeated-key, untouched-query and arbitrary-start cases, not only an empty two-write example.

Chronological lists are processed left-to-right; the last equal key wins. VFA's raw `lookup?` takes the first matching list entry. Thus `[(0,"new"),(0,"old")]` observes `"new"` as a raw VFA list but yields `"old"` when interpreted as chronological PFDS bindings. Prove the precedence conversion explicitly: prepending chronological writes produces `bindings.reverse ++ initial`; do not equate the two list interpretations directly. XA01 `AList.insert` removes older keys, so its bridge is observational, not equality with a duplicate-containing raw list.

## 3. Default lookup, presence and modification

Place VFA's `withDefault d m q := (m q).getD d` and `hasBinding m q := (m q).isSome` in the shared map observation layer. Prove preservation of write (`withDefault_update`) and presence after writing a key. Preserve the stronger reconstruction law:

`m q = some v ↔ hasBinding m q = true ∧ withDefault d m q = v`.

It needs no equality or order on payloads. Pointwise agreement of **both** observations then recovers partial-map equality. Agreement of default lookup alone does not: missing and explicitly stored default values coincide. For payload `Option A`, outer `none` and `some none` remain distinct; do not flatten them. VFA total-table adaptation needs an explicit `d : V`; the partial-map core must still admit empty payload types and cannot require `Inhabited V`.

Preserve XA01 deletion as writing outer `none`, and its `Modify` callback on the entire `Option V`, including callbacks that create a value from absence. `toMap_ofMap` recovers original operations by reduction. The reverse round trip preserves validity and lookup **on valid states**; it does not recover concrete state identity or callback evaluation counts. Reuse these exact boundaries when adding the optional capability.

## 4. Set correspondence and genuinely extra laws

XA01 sets adapt directly to `AbstractSet`: retain empty/insert, flip `isin`, and observe membership in `decode`. Prove `decode s ∪ {a}` agrees pointwise with `AbstractSet.add a (decode s)`; reuse `insertMany_observe` and `member_insertMany`. Deletion remains an additional capability. Its `validGraph` representation agrees with the current pointwise-iff representation by set/function extensionality.

A map's domain is `fun q => ∃ v, m q = some v`, equivalently `hasBinding m q = true`. Writing any supplied payload adds the key; deletion removes it. A standalone set insertion operation cannot choose an arbitrary payload without extra data: use maps with `Unit` payload, or explicitly supply a fixed value.

None of the minimal map/set laws supplies finite support or enumeration. A partial-function model over `Nat` may contain every key. Current `trees_finite_domain` provides a finite **covering list** for successful lookups, not an exact, ordered, duplicate-free enumeration. Any enumeration API must separately prove soundness, completeness and whatever uniqueness/order its clients consume; representation finiteness must not become a universal map axiom.

## Statement review and next checked cases

Quantify over all queries, binding lists, supplied values and valid starting states. `empty_valid` gives an inhabited valid domain; `AList` and ordered trees provide concrete positive realizations. No injective decoder, surjective realization, payload equality/order or global key order belongs in the shared laws; concrete key decisions/order remain explicit. Retain absence/stored-default, stored-`none`, shadowed duplicates, invalid-tree and infinite-support boundaries. Equal values establish no allocation, persistence, cost or runtime correspondence. These obligations require future checked implementation and the existing review loop before acceptance.

Peer challenge: `../evidence/reviews/collections-coherence-peer.md` independently confirms this ownership/adapter shape and its boundaries. Its malformed-tree and precedence countermodels are incorporated above. This is paper review, not a compiler result or acceptance.
