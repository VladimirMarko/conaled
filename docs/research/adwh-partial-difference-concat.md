# Function-accumulating concatenation and its completed-end demand

This development adapts the five function-accumulating concat declarations from
the supplied successor-335 material. The implementation extends the existing
`SquareKit.PartialSpine.Observations` owner in
`SquareKit/PartialSpine/DifferenceConcat.lean`. Its clients are in
`Examples/PartialSpineDifferenceConcat.lean`, imported by the public aggregate.

## The actual algorithm and its function domain

`concatD` is the specified strict left fold, followed by application to the
completed empty observation:

```lean
Observations.foldl
  (fun h xs ys => h (Observations.append xs ys)) id xss
  (Order.Ideal.principal .nil)
```

The accumulator is an arbitrary function from observation ideals to observation
ideals. The existing scoped `SquareKit.DirectedLimits.piCompletePartialOrder`
supplies its pointwise order, constant-bottom function and directed suprema.
There is no new domain engine and no restriction to bundled continuous
functions. The strict semantic left fold already accepts every accumulator
step: its monotonicity concerns the outer finite spine with fixed labels, and
does not require monotonicity of the accumulator step or its seed.

This connection was missing from the existing strict-fold and concat APIs.
The old native-list function-accumulation theorem addresses ordinary lists;
the new operation must also accommodate inner partial and infinite ideals.
The actual fold is retained in the definition so that its infinite-input
demand is a theorem about that algorithm.

## Finite agreement retains the function and the final tail

The public invariant states:

```lean
xss.foldl (fun k xs zs => k (Observations.append xs zs)) h ys =
  h (xss.foldr Observations.append ys)
```

Here `xss : List (Observations alpha)`, the initial `h` is any function, and
`ys` is any observation ideal. A short list induction generalizing `h` proves
the equation. The cons case uses the induction hypothesis at
`fun zs => h (append xs zs)`. It needs neither append associativity nor an
order or continuity premise on `h`.

`concatD_ofList` applies the invariant at `id` and completed nil, using the
existing `Observations.foldl_ofList` and `Observations.foldr_ofList` bridges.
Only the outer list must be completed and finite. Its inner labels can be
bottom, a partial spine, a stream, or any other observation ideal. The theorem
does not pass through the narrower native-list `concat_ofList` result.

The independent order case fixes inner blocks `[1]` and `[2,3]`, an initial
function that prepends `[0]`, and final tail `[9]`. The expected result
`[0,1,2,3,9]` records both composition order and tail placement. The client uses
the public arbitrary-function/tail law and then `append_ofList` to identify
the finite result. A separate finite-outer client starts with an infinite
inner stream and leaves the later inner ideal arbitrary; it still recovers
the entire first stream.

## Infinite input and boundary cases

`difference_foldl_stream` instantiates the shared strict-fold stream theorem
at the full function CPO. For every initial function, the accumulated function
is the constant-bottom function. Applying it at an arbitrary tail remains
bottom; `concatD_stream` specializes that application to completed nil.

The canonical `concatD_infinite_disagrees` witness retains three conclusions
for an outer stream repeatedly containing one infinite inner stream:

1. Function-accumulating concat is bottom.
2. Right-fold concat equals the inner stream.
3. The two results differ.

The right-fold equation uses the existing `stream_cons` and
`concat_infinite_first` laws. `stream_ne_principal` distinguishes the inner
stream from bottom. No new stream representation or coinduction principle is
needed.

Completed empty outer input yields completed empty output. Unknown outer input
yields bottom, and principal injectivity separates those results using the
independent finite constructors. A completed finite outer input can also yield
bottom when its first inner label is bottom. Finite completion suffices for
agreement of the two algorithms; it does not guarantee an informative result.

## Actual outer producers and existing consumers

`repeatCounting` is an outer coalgebra with natural-number state. At state
`s`, it emits `observations (guarded PartialSpineProgress.count) s` and retains
state `s`, so successive outer labels are the same whole counting ideal.
The existing guarded and paused Progress bridges connect its realizations to
their independent `Stream'.corec'` semantics.

For either outer realization, the strict function accumulator yields bottom.
Right-fold concat exposes the first infinite inner label and returns the
counting ideal. The proof only needs the outer stream's first constructor;
it does not add a redundant unfolding API for the repeated outer stream.
The existing consumers make the difference observable:

| Consumer | Right-fold concat | Function-accumulating concat |
|---|---|---|
| `first p`, starting at `s` | `p s` | `False` |
| `allCuts`, at budget `n` | Open prefix `unfold count s n` | Bottom |
| `allCuts`, start 4, budget 3 | Open `[4,5,6]` | Bottom |

The outer delivery witnesses are separate: two repeated inner ideals take
two guarded transitions or four paused transitions, with the same outer
state. The original inner counting producer delivers `[4,5,6]` from state 4
to state 7 in three guarded or six paused transitions. These are witnesses
for the specified individual producers. Semantic equality does not supply a
nested scheduler, sharing implementation, or runtime bound for concat.

## Source correspondence and review scope

The [exact five-row ledger](adwh-partial-difference-concat-provenance.tsv)
preserves the selected declarations, statements, coordinates and qualifications
from `ADWH/Chapter01/LazyListEvaluation.lean`, SHA-256
`4f6308bd80e6b10c58d2eb97dbccf40abb8e3b625e2f93b1d5288c6e277ad01c`.
The selected source names are `concatD`, `difference_foldl_apply`,
`concatD_ofList`, `concatD_stream` and `concatD_infinite_disagrees`.
The function-valued stream law and boundary cases are derived support and
clients; they do not claim additional selected source rows.
