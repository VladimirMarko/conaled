# Collections seam: bounded peer challenge

Read-only assessment of donor `20a5b5537a704be016d09e4eb31db0dad8a12d61`,
the frozen VFA draft, and current candidate
`f52a47b9e240b3937533f48befb8622527b7f6db`. No compiler, source, index, refs,
setup or remote writes occurred. This is paper-level INT-020/021 research,
not acceptance or an expansion of the current candidate.

## Proposed shape

The architecture agent's proposal is sound subject to the obligations below:
retain `Applications/Search/OrderedMap/Interface.lean` as the minimal
empty/bind/lookup interface and `Applications/Search/AbstractSet.lean` for
insertion/membership; preserve XA01 deletion and modification as additional
capabilities. Adapt invariant-conditioned XA01 maps on `{m // Valid m}` when
using PFDS's unconditional laws. Keep total/default lookup as an observation
over partial meaning, not an equivalent replacement.

## Concrete challenges

1. **Presence is observable.** PFDS `Examples/OrderedMap.lean` already separates
   `present_none` (`some none`) from `absent` (`none`). In
   `books/vfa/records/math/drafts/table-specs/TableObservations.lean`,
   `forget_default_not_injective` proves that absence and storing the supplied
   default have equal total observations. Retain partial lookup as the stronger
   observation; `binding_iff` requires both `hasBinding` and `withDefault` to
   recover a binding. Flattening `Option (Option V)` loses information.

2. **Validity cannot disappear in an adapter.** XA01
   `Applications/Collections/Map.lean` assumes `Valid` for mutation laws and
   proves validity at each actual intermediate state. PFDS's
   `Applications/Search/OrderedMap/Basic.lean` obtains unconditional interface
   laws by packaging `OrderedBy` in `Tree`. A concrete malformed raw tree with
   root `(0,"root")`, left child `(1,"hidden")`, and empty right subtree has
   directed `lookup 1 = none` but whole-tree `observe ... 1 = some "hidden"`.
   Preserve the invariant when identifying these observations. XA01
   `SquareKit/ValidGraphs.lean:comp_iff` also retains the intermediate predicate;
   its removal is explicitly refuted by `Examples/ADTRefinement.lean`.

3. **Two different order conventions must be bridged.** VFA's
   `lookup? 0 [(0,"new"),(0,"old")]` is `some "new"`; PFDS `bindAll` on
   those bindings from empty returns `some "old"` at key zero. Converting a
   raw association list requires reversal/right-folding or another proved
   first-binding-preserving normalization. Both projects' chronological write
   clients correctly use later-write-wins. XA01's update/update/delete client
   must additionally retain the coinciding-key case: its final result is absent.
   Standard `AList.insert` erases the old binding; VFA's raw list keeps shadowed
   bindings, so state equality and raw-entry enumeration are stronger claims.

4. **Finite support is additional structure.** PFDS `Meaning` and XA01's map
   model permit arbitrary partial functions. A lawful function-map realization
   can contain `fun _ : Nat => some true`; no finite enumeration covers its
   successful keys. `Basic.lean:trees_finite_domain` supplies a finite covering
   list for actual trees, not an ordered, duplicate-free exact enumeration.
   Such enumeration needs its own validity/completeness/order contract. A
   shadowed VFA raw-list member is not necessarily the observed binding; the
   draft already retains that counterexample.

5. **Do not strengthen payload assumptions or erase capabilities.** Partial
   maps support payload type `Empty`; the total Table interface requires an
   explicit default `d : V`. No global `Inhabited`, value equality or value order
   belongs in the common core. XA01/VFA support independent carrier universes;
   PFDS's common-universe interface needs an explicit generalization or checked
   lift before claiming preservation of that generality. PFDS's minimal map/set
   interfaces have no deletion operation: the reverse extension requires one
   with its laws. XA01 `Applications/Collections/Modify.lean` allows callbacks
   creating a binding from `none`; an existing-value-only modifier is weaker.

6. **Semantic correspondence does not transfer charges.** `Modify.Laws.roundTrip_lookup`
   preserves lookup and its companion theorem preserves validity; neither
   establishes concrete-state identity, callback counts or execution cost.
   These interfaces carry no common resource tariff. Keep existing cost and
   sharing results separate until an actual measured-executor correspondence
   connects them.

The next bounded implementation should prove the subtype/update bridge and a
connected same-key client while retaining these separating cases. No new
universal container framework is needed.
