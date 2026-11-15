# Partial-spine observations and producer adequacy

This development connects the Chapter 1 finite partial-list algebra to
conaled's existing producer semantics. A known output followed by an unknown
continuation is represented separately from a completed finite list. The
implementation proves an independent prefix/end description, exact strict fold
fusion and an observation-set interpretation of finite producer deliveries.

## Public ownership

| Owner | Interface and meaning |
|---|---|
| `SquareKit.PartialSpine` | Finite bottom/nil/cons observations; prefix/end equivalence; standard information order; fold/map and strict fusion. |
| `SquareKit.PartialSpine.Observations` | Uses Mathlib `Order.Ideal` directly; faithful principal finite embeddings and an independent `Stream'` observation ideal. |
| `Progress.Delivers.prefix`, `prefix_of_length_le` | Reuse the existing finite operational judgment and its deterministic coherence to recover shorter deliveries and order observations. |
| `Progress.SpineObservations` | Actual delivery witnesses generate an ideal; exact open-prefix adequacy; productivity characterization; guarded/paused stream refinement and silent-producer boundaries. |
| `PartialSpineProgress` | Map/head fusion consumed after an existing mapped producer; emit-once-then-silent and counting examples, source counterexample and six anonymous source cases. |

The normal build reaches these modules through `Examples.PartialSpineProgress`
in `SquareApplications.lean`. The existing foundation, total-list fusion,
producer interfaces and categorical stream APIs retain their contracts.

## Independent finite meaning

`PartialSpine α` has three constructors. Its `viewEquiv` identifies it with a
pair consisting of an ordinary ordered `List α` and a Boolean saying whether
the final nil was observed:

| Spine | Independent view |
|---|---|
| `bottom` | `([], false)` |
| `nil` | `([], true)` |
| `cons a s` | `(a :: s.view.1, s.view.2)` |

`ofList xs` has view `(xs, true)`; `openPrefix xs` has view `(xs, false)`.
Both retain duplicate labels and their exact positions. `IsTotal` means the
completed flag is true, and `isTotal_iff_exists` characterizes exactly the
images of ordinary finite lists. A known label may itself be an `Option` value;
`cons none nil` is still a known cons and differs from spine bottom.

The recursive fold has separate observations for the two ends. Its independent
meaning is the theorem `foldr_eq_view`:

```lean
foldr bottom f e s =
  s.view.1.foldr f (if s.view.2 then e else bottom)
```

The reconstruction uses standard `List.foldr`. Total-input refinement therefore
reuses the ordinary List API, including independence from the unused bottom
parameter. Fold uniqueness has all three constructor clauses, and its invariant
law has both terminal bases. Mapping changes the labels and preserves the
completed flag; its finite/open-prefix bridges, composition and fold-map laws
follow through that observation.

The constructor refinement relation becomes a standard `PartialOrder` and
`OrderBot`. `fromView_le_fromView` independently characterizes it:

- An open observation `(xs, false)` is below `(ys, flag)` exactly when `xs` is an
  ordinary list prefix of `ys`.
- A completed observation `(xs, true)` is below `(ys, flag)` exactly when
  `xs = ys` and `flag = true`.

No equality or ordering requirement is imposed on labels. In particular, a
completed list cannot gain another label, whereas a matching open prefix can.
`knownLength` counts known labels only; it does not assert the final length of
an unknown continuation.

## Exact fusion contract and reuse

For arbitrary result types and maps, the all-finite-partial-spine fusion equation
has target seed **`h e`**:

```lean
h (foldr bottomB f e s) = foldr bottomC g (h e) s
```

`foldr_fusion_iff` proves that holding for every finite partial spine is
equivalent to two requirements: `h bottomB = bottomC`, and the commuting
equation at every accumulator actually produced by folding a tail. Under an
unrestricted commuting equation, `foldr_fusion_iff_strict_of_commuting` isolates
bottom preservation as the exact remaining condition. The invariant form
requires `P bottomB`, `P e`, preservation of `P` by the step and commutation
only on `P`.

The sufficient invariant law uses `SquareKit.ListFusion.foldr_reachable` after
the independent prefix/end interpretation. There is no second basic-list
fusion library. Total finite embeddings use the same existing law with no
strictness premise, since their bottom end is unobserved.

The retained constant-some-true observer/step counterexample distinguishes
these statements. Its commuting equation holds, its observer changes none to
some true, fusion fails at spine bottom, and fusion still holds on every total
finite list. This is a statement counterexample, not a compilation failure.

`PartialSpineProgress.mapped_head` specializes strict fusion to `Option.map` and
the projection fold. `mapped_producer_prefix` then consumes a known nonempty
prefix from `Progress.mapCoalgebra`: the mapped observation is actually
delivered, and its head is exactly the mapped initial coalgebra output. Both
the algebraic transport and the producer realization participate in the proof.

## Observation ideals and independent stream meaning

`Observations α` is an abbreviation for `Order.Ideal (PartialSpine α)`.
Mathlib owns its nonemptiness, lower closure, directedness, extensionality,
subset order and principal embeddings. Finite observations are embedded with
`Order.Ideal.principal`; bottom, nil and finite total lists use those same
standard operations. `principal_injective` proves that this embedding retains
the entire finite spine, including its end.

For a total `Stream' α`, `stream σ` contains exactly those observations below
`openPrefix (σ.take n)` for some finite `n`. This definition uses the standard
stream carrier and prefix operations independently of a producer execution.
Every finite prefix is observable and its known length is exactly `n`.
`stream_ne_principal` separates this ideal from every finite principal ideal,
including bottom-tailed finite spines and completed finite lists.

This slice does not construct a directed supremum, continuous constructor or
infinite fold. Their future implementation should use standard
`CompletePartialOrder` and `ScottContinuous` interfaces rather than copying the
source's parallel `Domain` hierarchy. In particular, the existing ideal
complete-lattice instance has stronger base-order requirements than these
incompatible spine observations satisfy.

## Connection to actual producers

The existing `Progress.Producer` can emit a value or continue silently.
`Progress.Delivers` records a finite trace, ordered outputs, final state and
exact atomic step count. The new observation ideal has the public equation:

```lean
q ∈ observations step s ↔
  ∃ xs t k, Delivers step s xs t k ∧ q ≤ openPrefix xs
```

The two operational additions prove prefix closure of delivery and obtain the
prefix relation between coherent deliveries ordered by their lengths. These
justify the ideal construction. `openPrefix_mem_iff` proves the stronger exact
adequacy statement: an exact open prefix is observed if and only if that same
list has a finite delivery witness. The reverse direction uses actual prefix
closure; it is not a restatement of the carrier definition.

`productive_iff_observations` identifies existing `Productive` with observations
of every finite output length. The producer interface has no completed-end
transition, so `ofList_not_mem` and `not_total_of_mem` exclude all completed
spines. Finite completed lists remain valid independent ideals, but this
particular operational interface never emits a nil/end event.

`unfold_eq_take_corec` connects the existing independent finite coalgebra
unfolding to `Stream'.corec'`. Given finite deliveries of every prefix of a
specified stream, `observations_eq_stream` proves equality with its independent
stream ideal using deterministic coherence. `observations_guarded` and
`observations_paused` discharge that premise using the existing actual delivery
theorems. Their observation ideals agree, while the existing exact counts
remain `n` for guarded execution and `2*n` for the paused realization.

An always-silent producer has the bottom ideal by absence of finite evaluations.
An exhausted `Progress.search` budget alone does not establish this conclusion.
The never-matching filter producer specializes the silent theorem; the result
is an operational boundary, not the separate [semantic filter law](adwh-partial-filter.md).

## Retained distinguishing cases

The `once` producer emits `a` from `some a`, changes state to none and then
silently stays there. `once_observations` identifies its entire observation
ideal as `principal (cons a bottom)`. Its known head is available, no second
output is observed, completed nil is absent, and it is not productive. For the
known observation `cons 7 bottom`, the projection fold returns some 7, while
the Option-summing fold returns none because it requires the unknown tail.
The universal `once_consumers` theorem connects both consumers to the same
actually observed spine for every natural output value.

The counting producer starting at 4 delivers `[4,5,6]` and reaches 7 after
three guarded transitions or six paused transitions. Arbitrary starting states
and prefix lengths retain the existing `n`/`2*n` laws. Its mapped nonempty
prefix has the corresponding mapped head; mapping successor in the displayed
case gives some 5.

The six source anonymous cases also retain: an undefined label in a known
constructor; a step ignoring that label; mapping `[7,9]` with an unknown end to
`[8,10]` with the same unknown end; and sum 10 on the total list `[2,3,5]` with
separate bottom result 100. Additional order cases preserve duplicate positions
and distinguish extendible open prefixes from maximal completed lists.

## Source correspondence and remaining work

The source is the user-supplied checkpoint-335 canonical material. The
declaration-level companion `adwh-partial-spine-observations-provenance.tsv`
retains all 243 named commands from the seven partial/infinite/lazy Chapter 1
files. Exactly 56 are selected here: all 31 PartialLists commands and 25
LazyListDomain commands. Generic order laws use their standard owners; multiple
source finite bridges can map to one stronger standard refinement. Private
counterexample helpers remain in the example module.

The supplied archive SHA-256 is
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
Each ledger row records its canonical source path, file hash, declaration,
kind and line. Standard-owner references were checked against the pinned
Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The six anonymous PartialLists cases are retained together in
`Examples/PartialSpineProgress.lean`, in source order:

| Canonical source line | Preserved observation | Public connection |
|---|---|---|
| 244 | Projection of `cons 7 bottom` is some 7. | `foldr_eq_view` |
| 248 | Strict Option sum of `cons 7 bottom` is none. | `foldr_eq_view` |
| 252 | `cons none nil` differs from spine bottom. | Distinct datatype constructors |
| 255 | A step can ignore an undefined label and return some true. | `foldr_eq_view` |
| 259 | Mapping successor yields `cons 8 (cons 10 bottom)`. | `view_injective`, `view_map` |
| 263 | Total sum `[2,3,5]` is 10 with separate bottom result 100. | `foldr_ofList` |

The original file hashes are:

- `PartialLists.lean`:
  `4235bff0b33f9b96ce3b3522ccb4f9c2c4d986e9dca186525ae5025e5fe94b11`.
- `LazyListDomain.lean`:
  `11c925f78d8814621e33e7cd1c82de4dee6df59c2b4cab674b8843da5e54fb46`.

The other operators have separate source ledgers and connected cases in the
[integration record](adwh-recovered-integration.md). This foundational slice
alone does not establish their laws or whole-book completion.

The source observation order keeps label values fixed. Joint label refinement,
whole-language evaluation, recursive fixed-point semantics, contextual or
compiler equivalence, sharing, physical allocation and native runtime are
additional contracts outside this model. Atomic delivery counts retain the
existing operational cost convention; the ideal observation itself forgets
those counts.
