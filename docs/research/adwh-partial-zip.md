# Online zip and labeling of partial-spine observations

This development selects twenty declarations from checkpoint 335's
`ADWH.Chapter01.LazyListDemand`. The [source ledger](adwh-partial-zip-provenance.tsv)
preserves their exact coordinates, original planning fields, full canonical
statements, destinations and semantic qualifications. This is one bounded
Chapter 1 adaptation; related operator families have separate contracts in the [integration record](adwh-recovered-integration.md).

## One finite interpreter and the existing ideal extension

[Zip](../../SquareKit/PartialSpine/Zip.lean) takes a total `Stream' β` first
and an arbitrary partial spine or observation ideal over `α` second. At a
known cons it pairs the next first-stream label with the known second-input
label, then shifts the first stream. Bottom remains unknown and nil remains
a completed end. The two element universes are independent; neither element
type needs an order or a continuity assumption.

The finite specification uses the existing prefix/end view. If the second
input's view is `(xs, complete)`, the result's view is

```lean
((σ.take xs.length).zip xs, complete)
```

This specification is separate from the constructor recursion. It proves
that every known second-input value is paired and that the end flag is
preserved. Existing `Below` induction proves monotonicity. The semantic
operation is the principal-valued interpretation of this finite operation
through `IdealCompletion.extend`, using the existing `Order.Ideal` carrier
and its coherent full-directed CPO. The shared `mem_extend_principal` gives
the exact observation characterization; there is no second membership or
completion implementation.

Principal, bottom, nil and arbitrary-tail cons laws use the shared extension
and continuous-extensionality results. The genuine-stream law sends the
existing directed family of principal open prefixes to the corresponding
prefixes of standard `Stream'.zip Prod.mk`. Continuity is in the second input
with the first total stream fixed. These statements do not define symmetric
zip on two arbitrary partial inputs or assert joint continuity in labels.

The independent view also supplies a useful consumer law:

```lean
Observations.map Prod.snd (Observations.zipStream σ I) = I
```

Native `List.map_snd_zip` applies because `Stream'.take` supplies exactly as
many labels as the second spine already knows. The semantic proof combines
that finite fact with checked `map_principal` and continuous extensionality
on principals. Consequently projection recovers every observation ideal,
including unknown ends, completed finite ends and actual infinite streams.

## Native online labels

`labelFrom n` specializes the total first stream to `fun k => n + k`;
`label` starts at zero. The cons law increments the start index without
inspecting the input length. Completed finite observations refine directly to

```lean
Ideal.principal (PartialSpine.ofList ((List.range' n xs.length).zip xs))
```

The open-prefix equation uses the same known list and retains its unknown
end. These native finite expressions specify observations of the online
operation; they are not a length prepass in its implementation. The canonical
source's finite `Lists.labelFrom` helper is therefore unnecessary here.
`List.zipIdx` places the value first and index second, so it cannot replace
this expression without an explicit swap. Infinite labels are `(n + k, σ k)`;
the zero-based law uses standard `Stream'.enum` with its index-first order.
Second projection after `labelFrom` is an instance of the all-ideal zip law.

## Actual paired producers and retained consumers

[SpineZips](../../Applications/Progress/SpineZips.lean) starts with the existing
`Progress.zipCoalgebra` and `unfold_zip`. The ordinary corec/take connection
identifies the paired coalgebra's standard stream. Existing observation
adequacy then proves that semantic zip of the second producer's observations
equals observations of the actual paired guarded or paused producer. The
operational theorem follows the existing Progress interface's common
universe, while the semantic theorem remains independently polymorphic.

[The connected cases](../../Examples/PartialSpineZip.lean) reuse the existing
count coalgebra for both natural indices and values. Starting from `(10,4)`
produces `[(10,4),(11,5),(12,6)]` and reaches `(13,7)`. The guarded realization
has an actual three-transition delivery witness. The paused realization has
an actual six-transition witness and reaches `(false,(13,7))`. These counts
belong to the paired atomic producer model; they are not sums of independently
scheduled costs or physical runtime claims.

Existing first/allCuts consumers see the first pair and finite open prefixes
through those producer equalities. Mapping second projection recovers the
original counting observations. Separate finite cases label `[4,9]` from
seven as `[(7,4),(8,9)]`, distinguish completed and unknown ends, check start
zero and heterogeneous Boolean/Nat labels, and retain nil distinct from
bottom. Producer observations themselves have no completed-end transition;
completed finite cases use principal `ofList` inputs.

A generic adapter for silent producers is outside this slice: it would have
to retain its index on silent steps. The existing paired coalgebra and its
paused realization supply the required actual implementations. Mathematical
natural indices do not establish bounded Haskell `Int` endpoint or overflow
behavior, compiler adequacy, sharing, allocation or memory bounds.

## Scope and validation

The source ledger retains the twenty selected source declarations, their
assumptions and their maintained destinations. The public aggregate imports the
zip and labeling cases, so the normal build and exhaustive audit cover them.
The result preserves ordered finite observations; it does not establish a
scheduler, wall-clock rate, or sharing/allocation guarantee.
