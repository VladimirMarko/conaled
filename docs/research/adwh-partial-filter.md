# Partial filter and actual filtering producers

This development adapts the nineteen selected filter declarations from the 335
recovery source. The [provenance ledger](adwh-partial-filter-provenance.tsv)
retains their exact source statements, coordinates, file hash and destinations.
The other partial operators, Chapter 1 and the whole book have separate scope.

## Partial tests and shared fold laws

[Filter](../../SquareKit/PartialSpine/Filter.lean) interprets ordinary
`Option Bool` data through the existing semantic fold:

| Test | Tail step |
|---|---|
| `none` | Result bottom |
| `some false` | The unchanged tail |
| `some true` | The current known label followed by the tail |

Standard constant, identity and semantic-cons continuity establish the required
tail laws. Filter itself is Scott-continuous on the existing observation CPO,
preserves bottom/nil appropriately and preserves arbitrary ideals under
accept-all. The total finite refinement agrees with ordinary `List.filter`.
Completed inputs retain nil, while open finite prefixes retain an unknown end.
The stream result uses the existing nonempty directed family of principal
`Stream'.take` prefixes; it does not introduce another completion or generic
membership engine.

Fusion evaluates the inner partial predicate first. Inner undefined gives
undefined; inner false gives false without requesting the outer result; inner
true delegates to the outer predicate. For total predicates the expression is
`some (inner a && outer a)`. Ordinary commutativity of Boolean conjunction does
not justify reversing partial predicate evaluation.

The fold/filter algebra works over a supplied standard result CPO. Undefined
returns its bottom, false retains the accumulator, and true applies the
supplied algebra. For continuous tail steps it establishes

```lean
foldr f e (filter p I) = foldr (filteredStep f p) e I
```

The proof uses the shared strict continuous fusion theorem, keeps the
transformed seed explicitly, and reduces it to the original arbitrary `e`
through the nil law. No additional continuity, domain or finite filter
executor is introduced.

## Exact operational boundary

[SpineFilters](../../Applications/Progress/SpineFilters.lean) relates the
existing total-Bool `Progress.filterProducer` to semantic filtering of its
guarded input observations. Its finite correspondence has two different forms:

| Direction | Contract |
|---|---|
| Delivery to input prefix | A delivery with exactly `k` transitions outputs `(unfold c s k).filter p` and ends at `advance c s k`. |
| Input prefix to delivery | Filtering `unfold c s n` has a delivery with some `k ≤ n`, ending at `advance c s k`. |

The converse does not force consumption of trailing rejected inputs. An empty
filtered prefix may use the zero-transition delivery. Correspondingly, the
helper that prepends a silent step explicitly requires nonempty output. The
general `unfold_add`, `advance_add`, `Delivers.unique` and
`Delivers.prepend_silent` laws belong to the existing
[Progress.Streams](../../Applications/Progress/Streams.lean) owner. Other
producer clients can use them directly through that API. `SpineFilters` owns
the filter-specific finite correspondence and semantic bridge.

The two directions show that the actual observation ideal is the lub of all
principal filtered open input prefixes. The existing stream-directed and
filter-continuity laws give the same lub for semantic filtering. This yields

```lean
observations (filterProducer p c) s =
  Observations.filter (fun a => some (p a)) (observations (guarded c) s)
```

Only a total Bool predicate enters this bridge. A partial `none` is never
coerced to false. Public semantic fusion then connects outer filtering of an
actual filtered producer to the existing producer with the inner-first
conjunction.

## Connected cases and qualifications

[The examples](../../Examples/PartialSpineFilter.lean) use public fold/filter
fusion through the existing first-output consumer and the checked head/map
interface. Counting from 4 under the total even predicate has the finite
delivery `[4,6,8]` in five transitions, ending at 9. The six-element underlying
prefix `[4,5,6,7,8,9]` filters to the same list. The general converse supplies its
at-most-six witness; deterministic delivery uniqueness rules out an exact-six
delivery of that same output list. These counts describe the existing atomic
transition model, not the host cost of predicate evaluation or semantic filter.

Another case composes filtering the actual even producer with a test for values
at least 6, using the public actual-producer fusion law and a three-transition
delivery of `[6]`. The arbitrary predicate consumer observes the first even
output at 4 through the semantic/operational bridge and fused fold.

Partial-order cases distinguish outer undefined after inner rejection (nil on
a completed singleton) from the reversed predicate order (bottom). Separate
cases retain nil for an all-rejected completed singleton and bottom for an
all-rejected open prefix or infinite stream. Accept-all retains arbitrary
ideals. The actual all-reject counting producer uses the existing
`observations_filter_never` and `filter_no_match` results, while its guarded
input remains productive.

The finite even delivery does not by itself assert filtered-output productivity.
The all-reject stream equality is denotational; the separate operational
negative result uses absence of finite evaluation, not failed fuel search.
No whole-language, compiler, runtime, sharing or physical-memory theorem is
claimed. Source preparation, focused compilation, elaborated statement review,
integrated build/audit and both independent review axes are tracked separately
in the local work records.
