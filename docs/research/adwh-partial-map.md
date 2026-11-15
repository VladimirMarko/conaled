# Partial-spine map and first-output consumption

This development adapts the twenty selected head/map declarations from the
335 recovery source. The exact source statements, coordinates, file hashes,
destinations and qualifications are in
[the provenance ledger](adwh-partial-map-provenance.tsv). This is one bounded
Chapter 1 slice; related operators are covered by the [integration record](adwh-recovered-integration.md).

## Existing owners and new operations

[Map](../../SquareKit/PartialSpine/Map.lean) adds semantic map and general head
beside the existing partial-spine limits. Both use the same semantic fold and
`Order.Ideal` carrier. Semantic map folds mapped cons with principal nil as its
seed. Head folds the projection step with bottom as its seed, in the standard
`CompletePartialOrder` instance supplied by the caller for the element type.
There is no new global order on labels, flat Option order, domain/completion
hierarchy, finite map executor or limit engine.

The standard information order on spines fixes every known label. Therefore a
mapping function may be arbitrary: continuity of semantic map requires no
order or continuity on that function. The operation is Scott-continuous on
observation ideals, strict at bottom, preserves nil and commutes with cons.
Its all-principal refinement reuses the existing finite `PartialSpine.map`;
that map's independent prefix/end view retains the end flag. Ordinary finite
lists and infinite standard streams refine to their standard map operations.

Fold-after-map uses the existing strict continuous fold fusion law. For each
tail-continuous algebra `f`, it retains exactly

```lean
foldr f e (map g I) = foldr (fun a => f (g a)) e I
```

The observer is the semantic fold itself. Its bottom law establishes
strictness, its cons law establishes commutation, and its nil law recovers
the same seed `e`. Map composition follows from this public fold law with
the inner label function applied first. No merely monotone tail step is
silently substituted for the required Scott continuity.

Head returns the known label of any cons for an arbitrary tail. It agrees
with `List.headD` at the result bottom on completed finite lists and with
the first element of a standard stream. Both the bottom ideal and principal
nil yield result bottom; those input ideals remain distinct. This is a
deliberate loss of information in the head observation, not an identification
of the two ends.

## Actual producers and connected consumers

[SpineMaps](../../Applications/Progress/SpineMaps.lean) identifies the standard
corec stream of `Progress.mapCoalgebra` using the existing finite `unfold_map`
law and corec/take bridge. Together with observation adequacy, semantic stream
map then relates actual guarded and paused mapped producers to semantic map
of their observations.

[The connected examples](../../Examples/PartialSpineMap.lean) consume these
equalities through existing `allCuts`/`truncate` and `first`. The arbitrary-ideal
identity

```lean
head (map p I) = PartialSpineLimits.first p I
```

uses the standard CPO on Prop and follows from public fold-after-map. Actual
mapped counting producers then instantiate that consumer. Counting from 4
after adding 10 exposes `[14,15,16]`; the original delivery judgments witness
3 guarded transitions or 6 paused transitions, ending at state 7. These are
operational facts about those producers, separate from the noncomputable
semantic map. No runtime, allocation or memory cost is asserted for map.

The composition example adds 10 and then doubles, yielding `[28,30,32]` through
the public map fusion law and allCuts consumer. The reversed functions would
yield a different sequence. The once-emitting producer retains an unknown end
after its mapped singleton, whereas a mapped completed singleton retains nil.
An arbitrary-tail head case and a finite Set-valued CPO specialization exercise
the general head interface without introducing another element order.

## Source adaptations and limits

The source's finite semantic `ofList_cons` fact is reused through existing
`PartialSpine.ofList_cons` and semantic `cons_principal`, without another public
wrapper. The source `mapFold_streamPrefix` helper is covered by the stronger
`map_principal` theorem for every finite spine, combined with the existing
`foldr_principal` and finite `map_openPrefix` laws. The infinite result uses the
standard `Stream'.map_take` law and full directed-lub preservation on the
existing nonempty prefix family.

The head/map source files include further operators outside this slice. This
ledger does not claim those are adapted. These results describe mathematical
partial/infinite observations of fixed labels; they do not establish whole
language semantics, compiler adequacy, sharing or physical execution behavior.
Focused compilation, statement inspection, integrated build/audit and both
independent review axes are tracked separately in the local work records.
