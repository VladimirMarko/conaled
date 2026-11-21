# Difference-list closure observations

Historical checkpoint and local-ticket references in this account resolve through
the [preserved FDSA records](../history/textbooks/checkpoint-012/books/fdsa/README.md).
Current coverage and follow-up belong to [#558](https://github.com/VladimirMarko/conaled/issues/558);
old process and tracking instructions describe the producing session.

This shared unit gives an explicit closure model for the constant composition
and deferred application claims used by FDSA's natural mergesort discussion.
It does not activate or accept
Chapter 2, and it does not implement the source scanner.

**Validation snapshot — 4 November 2026.** A successful focused check included
the difference-list core and examples. A separate successful inspection
printed 72 public types from those modules. These are historical results;
reuse requires matching candidate evidence, and complete unit acceptance was
still outstanding in this snapshot. The full acceptance gates below remain
required.

## Sources and existing interfaces

The source is the July 27, 2026 [FDSA book](https://fdsa-book.net/), printed
pp.21–22, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion `Natural_Mergesort.thy` comes from the dated
[AFP Efficient-Mergesort archive](https://isa-afp.org/release/afp-Efficient-Mergesort-2026-10-26.tar.gz),
whose SHA-256 is
`148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708`.
The theory's SHA-256 is
`2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51`.
It supplies the actual ascending-run builder recurrence used for later
correspondence and imports `HOL-Data_Structures.Sorting`. The separately
inspected `Sorting.thy` is pinned to Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`; that revision does not identify
the AFP theory. The dated archive postdates the book edition, so this is
provenance for the compared source, not a claim of identical July source.
The exact unit requirements, bounded design preflight and its provenance
correction are preserved in the preserved FDSA records directory.

The value representation is existing `Batteries.DList`, at pinned revision
`66e469188fe07963e5cf666c7d4433f45b8131c5`. Its `apply` function and invariant
say that application appends a fixed prefix to the supplied suffix. Its
`toList`, append, singleton and push laws already supply the relevant value
semantics. The timing comments in the library are not themselves formal
resource proofs.

The unit reuses `Resources.Measured`, `bind`, `CallCount.tick` and `run`.
There is no alternative DList datatype, expression tree, executor or compiler
model. Existing ordered-summary and fusion clients retain their value laws;
they acquire no cost claim merely by using an equivalent representation.

## Two phases and their observations

`Resources.DifferenceListCosts.Builder α` is an ordinary function:

```lean
List α → Resources.Measured (List α) Nat
```

The separate contracts are:

```text
Rep f prefix: for every suffix, value(f suffix) = prefix ++ suffix
AppCost f k:  for every suffix, cost(f suffix) = k.
```

Rep says nothing about cost. AppCost is uniform over suffixes because a
composition applies its first callback to the list produced by its second.
Neither contract needs equality, order or an inhabitant of the payload type.

The charged identity `empty` returns the suffix with one application entry.
`singleton a` returns `a :: suffix`, also with one entry. `compose f g` first
applies g, then applies f to that returned list, and adds one composition
entry. Its exact general application observation is

```text
cost(g suffix) + cost(f(value(g suffix))) + 1.
```

Thus f representing p and g representing q give a callback representing
`p ++ q`. Their application order is g then f; their output prefix order is
p then q. If their uniform application costs are k and l, the resulting cost
is `k+l+1` over natural observations. The proof retains the actual intermediate
value before specializing those two cost contracts.

`createEmpty`, `createSingleton` and `createCompose` are different operations:
they return the corresponding callback and charge one construction event.
They capture their fixed number of supplied references without applying the
callbacks. A supplied callback has already been constructed at this boundary;
capturing it does not repeat its construction or application work.

This is a declared fixed-size closure-capture tariff and a unit invocation
tariff. It is not a measurement of compiler allocation, processor instructions,
memory retention or Lean's runtime evaluation. Scanner/control traversal costs
remain a separate observation to be supplied by each source algorithm.

## Compositional construction

`pushRun a f` creates a singleton callback and composes f with it through the
existing measured bind. The two construction events cost two. `buildFrom`
executes these pushes through existing `Resources.run`; it does not recreate
or recharge its supplied seed.

For n items and a seed with prefix p and application cost k, the public laws
separately establish:

| Observation | Result |
| --- | --- |
| Construction during `buildFrom` | `2*n` |
| Represented prefix afterward | `p ++ items` |
| One application afterward | `k+2*n` |

`build` first creates charged identity, then runs that construction. Both
construction and one later application therefore cost `2*n+1`. The bound
follows from the primitive callbacks and actual push recurrence; the final
builder's cost is not supplied as an assumption.

The examples define actual measured programs for construction followed by
one application and by two applications. Both returned values are retained in
the two-application program; it does not silently reuse the first materialized
list. Their exact counts are:

| Input length | Construction | Each application | Construct, apply once | Construct, apply twice |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 2 | 3 |
| 1 | 3 | 3 | 6 | 9 |
| 3 | 7 | 7 | 14 | 21 |
| n | `2*n+1` | `2*n+1` | `4*n+2` | `6*n+3` |

The retained length-three input is `[3,1,3]`; nonempty suffixes and duplicate
values remain in their original order. Empty construction/application is also
instantiated at payload type `Empty`. The singleton-seed example charges only
subsequent construction, giving `4*n+1` when that already supplied seed is
extended by n items and then applied once.

## Existing DList values and different cost histories

`toDList f prefix rep` uses the existing DList record with application function
`fun suffix => (f suffix).1`. Rep supplies its invariant and toList value.
The semantic bridge reuses the standard append/push laws and equality to
`Batteries.DList.ofList prefix`. It carries no construction history or cost
information into the DList value.

The pinned `Batteries.DList.push` implementation is the fused function
`fun suffix => f (a :: suffix)`. The measured push in this unit explicitly
composes f with a singleton callback. Their values agree, as exercised by
`fused_push_value`; their exact construction/application decompositions are
not identified. The two-singleton example independently expects `[1,2,9]`
from prefixes `[1]`, `[2]` and suffix `[9]`, with three application entries.

Charged identity is also only a value identity. Composing an arbitrary callback
with it retains the returned list but adds two application entries: the
identity invocation and the composition invocation. `identity_value_cost`
retains this equation. No builder Monoid instance asserts a false identity
law for the full measured observation.

## Empty output does not bound application work

The `padded` family repeatedly composes with charged identity. Every member
represents the empty prefix and decodes to the same empty DList value, but
its application count is `2*n+1`. `no_bound_from_output_length` supplies a
member exceeding any proposed affine expression in that common zero output
length. Extensional DList validity alone cannot justify a materialization
bound in output length.

The `doubled` family makes a second distinction. Each extension creates one
new composition that captures the previously built callback twice. The
description is shared, while the actual composition invokes that callback
twice. After n extensions:

```text
construction cost = n+1
application cost + 1 = 2^(n+1)
represented prefix = [].
```

The successor equation is proved first, before deriving the natural-subtraction
form `2^(n+1)-1`. Four extensions create five closures; applying the result
to `[9]` returns `[9]` with application count 31. The actual measured program
that constructs and applies it costs 36. These examples separate distinct
creation events from unfolded invocation occurrences.

Consequently, a statement about application work being linear in representation
size must identify that size. Unfolded occurrence weight or an explicit
application contract is appropriate here; the number of distinct shared
closure-creation events is not a bound on arbitrary later application work.
The push chain has a linear application weight because each extension captures
its prior builder once and a fresh singleton once, as its recurrence proves.

## Source correspondence still required

The source ascending-run builder starts from singleton-prefix `(#) a`, then
extends through explicit composition and ultimately applies to `[last]`.
It does not start from identity. For a run of length r>=2 it has r-2 extensions
after its singleton seed, so the later correspondence target in this tariff
is application weight `1+2*(r-2)=2*r-3`. Empty and singleton runs bypass that
path. The source-to-model branch equations and actual run-size invariant remain
Chapter 2 obligations; the generic seed theorem merely provides the shared law.

FDSA-2-112 additionally needs actual scanner/control, descending cons construction,
emitted-run construction and merge-dispatch observations. Its comparison
counters remain unchanged by the separate closure tariff. FDSA-2-109's ordinary
repeated append versus prepend/reverse construction also remains chapter work.
No chapter completeness claim follows from this shared interface.

## Statement review and validation history

The meaningful premises are the ordered-prefix value relation and a uniform
cost contract for an already supplied callback. The base constructors satisfy
both, and composition/build laws preserve them without payload restrictions.
No final workload bound or physical execution theorem is postulated.

Source review retains the two phase boundaries, actual intermediate values,
arbitrary suffixes, supplied-seed scope, duplicate/order preservation, empty
payload case, repeated materialization and the two distinct history examples.
The architecture preflight identified and corrected the shared-allocation,
fused-push and singleton-seed distinctions before implementation.

No additional compiler was run for this draft while the frozen old Chapter 1
gate remained active.

Acceptance requires immutable-candidate elaboration, public-entrypoint coverage,
the complete guarded candidate build and exhaustive audit, both retained
independent review axes, and immediate candidate identity verification.
