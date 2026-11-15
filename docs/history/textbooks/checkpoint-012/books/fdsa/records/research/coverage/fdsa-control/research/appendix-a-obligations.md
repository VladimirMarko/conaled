# Appendix A: List Library — exact API and boundary inventory

Prepared 2026-11-02. Cross-cutting reference inventory only; no chapter or
appendix acceptance is asserted. Root may develop the shared adapters separately
while retaining the sequential chapter prerequisite. This note changes no Lean
source and reports no build or audit.

## Source and inspected versions

Appendix A of FDSA, July 27, 2026, occupies printed pp. 343–345 (PDF pages
349–351). The PDF SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`;
official source: <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
The extraction is `book-source/appendix-a.txt`; the minimum and predicate page
was also rendered for inspection. The appendix has no direct theory link.

The source mappings below were checked against conaled
`1aabd512284fe86254278ac631eda061d311050b`, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The key core files are
`src/Init/Data/List/{Basic,Lemmas,MinMax,Pairwise,TakeDrop}.lean` at
<https://github.com/leanprover/lean4/tree/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/List>.
Mathlib's `Data/List/Intervals.lean` supplies the exact interval-list interface.
All these Lean-library sources carry Apache-2.0 notices.

| Inspected reading copy | SHA-256 |
|---|---|
| `LeanList-Basic.lean` | `566e74dd5c3e72b2111af000b8bd1552f1aaffe29be317ba01bc91c9e5b55293` |
| `LeanList-Lemmas.lean` | `9365fb1c6da0313a4c73e8cf096377e69c28ece28d38290a0423e5f8cc1fdfdb` |
| `LeanList-MinMax.lean` | `f7c8ec372abc8277b14103553c1559ff925c59b16eaba6708fc96399fb2d704f` |
| `LeanList-Pairwise.lean` | `fcc984c70a81216c178d42a858dea5e3640201023a9a4d2837e76f138fd9b0f4` |
| `LeanList-TakeDrop.lean` | `9efed9c3f05746ce0dd47c5fcd2c414ba9541d6631d6ddf0cb06203d723c7918` |

Reading copies remain outside deliverables. The durable item is this original
mapping and its provenance.

## Finding and governing interface choice

**No genuinely new value-level operation is needed for any of the twenty source
entries.** The useful work is checked recurrence/notation correspondence and
connected boundary examples, reusing the standard APIs directly. Do not create a
parallel list library just to reproduce the book's names.

The source omits invalid-input equations for `hd`, indexing and minimum.
Following `fdsa-control/DECISIONS.md`, use `Option` or an explicit valid-input
proof. An empty Lean element type is permitted. No blanket `Inhabited α`,
default element or artificial order top/bottom belongs to this foundation.
List tail, drop, take, drop-last and update already have defined total behavior;
their valid source behavior must not be replaced by a failure convention.

## Complete declaration/equation mapping

Every source equation is included in the normalized description column. A
standard theorem already expressing an equation can be the coverage witness;
it does not need an extra public alias.

| ID | Source declaration and all displayed cases | Exact Lean/Mathlib route and remaining adapter |
|---|---|---|
| A-001 | `length`: empty length 0; cons length tail length plus 1. | `List.length`, `List.length_nil`, `List.length_cons`; no hypotheses. This is element count, not `sizeOf`. |
| A-002 | Append `@`: empty left input returns the right input; cons distributes over recursive append. | `List.append`/`++`, `List.nil_append`, `List.cons_append`; no hypotheses. The right argument is arbitrary. |
| A-003 | `set`: empty set on `[]`; singleton-head union tail set on cons. | Use `Set` membership observation `{a ∣ a ∈ xs}`; `List.not_mem_nil`, `List.mem_cons` and `Set.ext` give both equations. No `DecidableEq α` is needed. A finite-set encoding would introduce an unnecessary equality capability for this mathematical observation. |
| A-004 | `map f`: empty stays empty; mapped cons is `f x :: map f xs`. | `List.map`, `List.map_nil`, `List.map_cons`; arbitrary function and universes. |
| A-005 | `filter p`: empty stays empty; keep the head iff Boolean `p x`, then filter the tail. | `List.filter` already accepts `α → Bool`; `filter_nil`, `filter_cons`, `filter_cons_of_pos/neg`. A Prop predicate uses an explicit `DecidablePred`/`decide` bridge. |
| A-006 | `concat`: empty outer list gives empty; cons of a list gives that list appended to flattened tail. | `List.flatten`, `List.flatten_nil`, `List.flatten_cons`. Do not confuse this with appending one final element. |
| A-007 | `take`: empty input yields empty at any count; on cons, count 0 yields empty and successor count keeps the head then recurses. | `List.take`, `take_nil`, `take_zero`, `take_succ_cons`; exact saturation for overlarge counts. |
| A-008 | `drop`: empty input yields empty at any count; on cons, count 0 returns the input and successor count recurses on the tail. | `List.drop`, `drop_nil`, `drop_zero`, `drop_succ_cons`; exact empty result for overlarge counts. |
| A-009 | `hd`: the only displayed equation returns the head of a cons. | Total view `List.head?`, `head?_cons`; proof-domain view `List.head xs h`, `h : xs ≠ []`. `head?_eq_some_head h` connects them. Empty yields `none` under the chosen total view, rather than a fabricated source element. |
| A-010 | `tl`: empty stays empty; cons returns its tail. | `List.tail`, `tail_nil`, `tail_cons`; do not replace by `tail?` unless supplying a separate explicit interface. |
| A-011 | `butlast`: empty stays empty; a cons returns empty if its tail is empty, otherwise keeps its head and recursively removes the last element. | `List.dropLast`, `dropLast_nil`, `dropLast_singleton`, `dropLast_cons_cons` (or `dropLast_cons_of_ne_nil`). The displayed conditional follows by cases on the tail, with no decidable equality on elements. |
| A-012 | `rev`: empty stays empty; reversing cons is reversed tail followed by singleton head. | `List.reverse`, `reverse_nil`, `reverse_cons`. The standard implementation uses an accumulator; the displayed equation is a value law, not a cost equivalence with naive recursive reversal. |
| A-013 | `!`: on nonempty input, index 0 returns head and successor index recurses on tail. | Zero-based `xs[i]?`, `getElem?_cons_zero`, `getElem?_cons_succ`; valid view `xs[i]'h` with `h : i < xs.length`, related by `getElem?_eq_getElem h`. `getElem?_eq_none_iff` identifies invalid indices. The source supplies no empty-list result. |
| A-014 | `list_update`: empty update is empty; index 0 replaces head; successor index preserves head and updates tail. | `List.set`, `set_nil`, `set_cons_zero`, `set_cons_succ`. `set_eq_of_length_le` proves out-of-range update leaves the entire input unchanged; it does not extend the list or return failure. |
| A-015 | `upt [i..<j]`: upper endpoint 0 yields empty; successor upper endpoint appends `j` when `i≤j`, otherwise gives empty. | `List.Ico i j`, defined as `List.range' i (j-i)`; `List.Ico.succ_top`, `eq_nil_of_le` give exactly the conditional recurrence. `List.Ico.mem` is `i≤x ∧ x<j`, `length` is `j-i`, and `zero_bot` gives `range`. The upper endpoint is excluded; reversed/equal endpoints give empty. |
| A-016 | `replicate`: count 0 gives empty; successor count conses one copy to the recursive list. | `List.replicate`, `replicate_zero`, `replicate_succ`; no equality/order assumption on the repeated element. |
| A-017 | `distinct`: true on empty; cons is distinct iff head is absent from tail and tail is distinct. | `List.Nodup`, `nodup_nil`, `nodup_cons` are the mathematical contract. If a Boolean executable view is needed, use `decide xs.Nodup` with `DecidableEq α`; do not add that capability to purely propositional statements. |
| A-018 | `sum_list`: empty sum 0; cons sum is head plus tail sum. | `List.sum`, `sum_nil`, `sum_cons` require only `[Add α] [Zero α]` for these literal equations. Associativity, identities or commutativity are separate laws for later transformations, not assumptions needed to state this recurrence. |
| A-019 | `min_list`: singleton returns its element; on at least two elements, take minimum of head and recursive tail minimum. | `List.min?` plus `min?_singleton`, `min?_cons`; proof-domain `List.min xs h` plus `min_singleton`, `min_cons`. Details and minimal assumptions are below. |
| A-020 | `sorted_wrt P`: true on empty; cons requires `P x y` for every tail member and recursively sorted tail. | `List.Pairwise` and `List.pairwise_cons` exactly express it, with `.nil` at empty. For a Boolean source relation use `fun x y => P x y = true`; a Boolean result can use its decidable Pairwise instance. No transitivity is needed for this definition. |

## Minimum: precise existing interfaces and assumptions

`List.min? : List α → Option α` and proof-domain `List.min` both need only
`[Min α]` for their operations. Core already supplies:

- `List.min?_nil`, `min?_singleton`, `min?_eq_none_iff`;
- `List.min_singleton`, `min_cons_cons`;
- `List.min?_eq_some_min h`, where `h : xs ≠ []`;
- `List.min_eq_get_min? xs h` and `List.get_min?`.

The implementation folds from the left. Its exact source-style right-recursive
equation is the standard theorem

```text
(x :: xs).min? = some (xs.min?.elim x (min x))
```

`List.min?_cons` and the analogous `List.min_cons` require
`[Std.Associative (min : α → α → α)]`. This requirement must not be silently
omitted when generalizing the equation to an arbitrary `Min` instance. A normal
`LinearOrder α` provides the book's intended lawful specialization. Leastness
and membership then use `List.min?_eq_some_iff`, `min_mem` and `min_le_of_mem`;
order-free operation existence and these laws remain separate.

Mathlib also offers `List.minimum : WithTop α` and
`minimum_of_length_pos`, but the explicit optional/nonempty core APIs already
fit this task and avoid introducing a top element. Existing conaled
`Optimization.Thinning.argmin id` is another total minimum realization, with
`argmin_eq_none_iff`, `argmin_correct`, and first-tie contracts. If a connected
optimization example uses it, prove its agreement with the standard minimum
through the independent leastness contract; no new minimum algorithm is needed.

## Boundary and observation bridges worth checking

1. **Empty element type.** Each total operation applies when its explicit
   capability parameters exist. `head?` and optional indexing require none and
   return `none` on an empty list. `min?` can likewise return `none` using the
   empty-domain `Min` instance. By contrast, `sum` requires `Zero α`, which
   cannot be instantiated for `Empty`. No arbitrary inhabitant can be produced
   by an unrestricted `hd [] : α`. A proof-domain view has no invalid call.
2. **Invalid lookup versus invalid update.** `[1,2][2]? = none`, while
   `[1,2].set 2 9 = [1,2]`. Keep those different source semantics. Existing
   random-access clients already prove `fetchRA_refinement` to `getElem?` and
   `updateRA_refinement`/update-query laws to `List.set`; these are useful
   connected applications of the shared adapter.
3. **Valid update observation.** `List.length_set`, `getElem?_set_self h` and
   `getElem?_set_ne hne` connect list update to lookup without modifying unrelated
   positions. A direct value-only update example is weaker evidence than this
   existing composition.
4. **Index conventions.** The appendix index is zero-based. Selection's public
   `selectWith` remains one-based with rank zero returning `none`; its checked
   value theorem explicitly uses `k-1`. Do not change that established API.
5. **Duplicate/order retention.** Set observation forgets repetitions and order;
   maps, flattening, filtering and reversal do not generally do so. `Nodup` and
   `Pairwise` must remain their own observations. In particular, adjacent
   `List.IsChain` is not equivalent to `Pairwise` for an arbitrary nontransitive
   relation.
6. **Ranges and truncation.** Check equal/reversed endpoints, a singleton
   interval, and an endpoint example such as `List.Ico 2 5 = [2,3,4]`.
   Natural subtraction `j-i` is truncated, which implements empty intervals
   when `j≤i` rather than producing a negative length.

## Value equations versus source costs

Appendix A introduces values and predicates. Appendix B.1 assigns costs to a
selected subset, including higher-order map/filter callbacks. Their recurrence
proofs are separate coverage obligations. They cannot be inferred from A's value
equalities: the standard reverse has the same value as naive reverse but not
the same source execution recurrence; standard minimum also uses a different
fold association internally.

Chapter 1's candidate already provides `Resources.ListReversal.appendRun_exact`,
`appendRun_nil/cons`, `naiveRun_value`, and
`Resources.SymmetricCosts.reverseRun_value/work`, with explicit cost models.
These may be reused after their required acceptance; neither the existing
standard value law nor this inventory upgrades their validation status.

The appropriate deliverable is a small checked adapter/example layer over these
APIs and an exact coverage ledger, not twenty newly defined aliases. All A-001
through A-020 still require a named checked witness and applicable review before
this appendix is declared covered. No source defect was identified in Appendix
A; its intentionally omitted invalid cases require the explicit bridges above.
