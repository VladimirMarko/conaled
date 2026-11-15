# Semantic concat and its nested fold law

This development adapts seven concat declarations from checkpoint 335 using
the existing observation, append and fold owners. Inner values remain arbitrary
observation ideals, including partial and infinite ones. The retained application
uses an actual outer producer that emits one inner counting-stream ideal and
then stays silent.

## Shared operation and order

`SquareKit/PartialSpine/Concat.lean` extends the existing
`SquareKit.PartialSpine.Observations` namespace with:

```lean
concat xss = Observations.foldr Observations.append (Ideal.principal .nil) xss
```

The outer carrier is `Observations (Observations alpha)`. Its finite spine order
holds each inner-ideal label fixed. It does not refine those labels pointwise or
turn a changing inner label into an ordered parameter. The existing observation
CPO applies at both levels, with `Order.Ideal`, standard `ScottContinuous`, the
same principal embedding and the one generic ideal extension.

The continuation of the outer fold occurs in append's **right** argument.
`concat_continuous`, the bottom and nil laws, and the arbitrary-cons equation
therefore use `append_right_continuous` and its monotonicity consequence. There
is no additional domain, limit engine, or joint-continuity requirement on inner
labels. Neither outer nor inner ideals are restricted to finite ordinary lists.

## Boundaries preserved by the constructor laws

The laws distinguish absent information, a known end, and a known inner value:

| Outer observation | Flattened result |
|---|---|
| Bottom | Bottom |
| Known nil | Known nil |
| `cons xs rest` | `append xs (concat rest)` |
| `cons bottom rest` | Bottom, even when a later inner value is nonempty |
| `cons (stream sigma) rest` | The entire first stream, for every outer `rest` |

`concat_infinite_first` uses the existing stream append theorem. Its arbitrary
outer continuation includes bottom and partial ideals, with no productivity
hypothesis. A retained counting-stream case consumes this equation through
`allCuts` at budget three, obtaining `[4,5,6]` for an arbitrary outer tail.

`concat_ofList` connects the semantic operation to ordinary `List.flatten`:

```lean
concat (Ideal.principal (ofList
  (xss.map fun xs => Ideal.principal (ofList xs)))) =
  Ideal.principal (ofList xss.flatten)
```

Both the outer and inner finite embeddings are completed spines. The retained
source-order calculation `[[], [1,2], [], [3], []]` produces `[1,2,3]` through this
public bridge. Empty inner lists do not block later values. A separate first
inner-bottom case does block a later completed singleton. The outer bottom/nil
case also proves that the two result ideals are distinct, using the independent
finite constructor distinction through principal injectivity.

## Nested fold fusion and its exact seed

For a standard result CPO, seed `e`, and a Scott-continuous tail step for each
label, the public fusion equation is:

```lean
Observations.foldr f e (concat xss) =
  Observations.foldr (fun xs r => Observations.foldr f r xs) e xss
```

The proof is an application of the existing strict fold-fusion theorem. The
observer `Observations.foldr f e` is continuous in its ideal input and strict
by its proved bottom law. The commuting equation is `foldr_append` from
the [append construction](adwh-partial-append.md). The nested algebra's tail monotonicity comes from the existing
`foldr_seed_continuous` theorem, retaining the required continuity of every
original tail step.

Fusion first produces the target seed
`Observations.foldr f e (Ideal.principal .nil)`. The proof uses the existing nil
law to identify it with `e`. That equation is derived, not assumed. No law is
claimed for arbitrary noncontinuous tail algebras, and no continuity in changing
inner labels is smuggled into the outer fixed-label order.

## A nonproductive outer producer with visible infinite contents

The existing `PartialSpineProgress.once` producer emits its initial value once
and then remains silent forever. Its observation ideal is an **open** singleton:

```lean
observations once (some xs) = Ideal.principal (.cons xs .bottom)
```

`PartialSpineConcat.concat_once` connects this actual producer to the new
operation and gives `append xs bottom`. The guarded and paused specializations
reuse the existing producer/append bridges from `PartialSpineAppend` to show
that an infinite inner observation ideal is recovered unchanged. The retained
application pairs the guarded specialization with the existing proof that the
outer emit-once producer is nonproductive. It does not replace that unknown outer
end by a completed nil.

The function-valued `allCuts_once_guarded` and `allCuts_once_paused` laws then
recover every ordinary unfolded inner prefix together. Counting from 4 yields
the independently expected `[4,5,6]` at budget three in both cases. The retained
`Delivers` facts still refer to the original inner producers: three guarded and
six paused transitions reach state 7. They are separate witnesses, not a runtime
cost for concat or a nested producer scheduler.

`first_concat` specializes the public `foldr_concat` law to the existing
first-output algebra. `first_concat_once` then evaluates the outer open singleton
through principal refinement of that nested fold. It returns the first consumer
of the inner value for **every** inner ideal. The counting specialization obtains
`p s` for either actual realization starting at `s`. This proof path exercises
the nested fusion equation directly; it does not merely rewrite the final ideal
equality.

`Examples.PartialSpineConcat` is imported by the normal public aggregate. All
application claims remain Lean declarations within the integrated build and
proof-audit closure.

## Provenance and remaining scope

`adwh-partial-concat-provenance.tsv` maps exactly the seven selected named rows:
`concat`, `concat_bottom`, `concat_nil`, `concat_cons`, `concat_infinite_first`,
`concat_ofList`, and `foldr_concat`. There are no selected anonymous source
cases. The ledger preserves the original statements, locations and qualifications
and records the actual public destinations. Input continuity is a useful derived
specialization, without a further selected source row.

The canonical source is checkpoint 335's
`ADWH/Chapter01/InfiniteListFusion.lean`, SHA-256
`5361a0bafad1f966393222bb0ec0ee7d1aee15de123541c4899e14c467d3a4da`.
The supplied archive SHA-256 is
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
Standard owners use the repository's pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

[Function-accumulating concat](adwh-partial-difference-concat.md) separately
accounts for its different demand behavior. Neither result establishes
whole-book completion; the concrete queens-16 proof remains excluded.

These are denotational contracts over fixed-label observations. They do not
define an executable flattened producer, prove a new scheduling/productivity
or whole-language adequacy theorem, or establish sharing, allocation or memory
costs. A failed bounded search is not evidence of divergence. Focused evidence
and integrated acceptance are recorded separately from this source description;
the combined candidate still needs the full build, exhaustive audit, final
candidate verification and both independent review axes.
