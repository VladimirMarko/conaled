# Ordered insertion — pinned API and reuse preflight

Date: 2026-11-03 UTC. Ticket: `FDSA-XI01`.

**Status: source/API preparation only, with no new source unit, implementation
release, compilation, final review or acceptance.** Chapter 1 remains the
sequential prerequisite; its third attempt is the sole authorized gate. This
task did not inspect or control that gate. The original first Chapter 2 prefix
remains exactly `c80eec92f5458eccfd1c34c8314d666c2a1e3847`. The later potential
tip `c28ba71863d2a35ee1c3a089caa90464e4cca692` is not that prefix.

## 1. Recommendation and actual remaining gap

Keep XI01 as preparation for Chapter 2. The bounded search found no additional
consumer that justifies freezing a new shared source unit now. Canonical
ordinary insertion, its length/permutation/sublist laws, forward sortedness,
mapping, and whole-sort stability already exist. The exact negative and
positive filter equalities are small missing observations of that operation;
the source sortedness iff and all-members immediate-cons claim are short
assemblies of existing declarations. None needs another executor, carrier,
comparison record or cost framework.

The two filter equalities can be proved using existing sublist, permutation,
filter and equal-length APIs. In particular, the positive equality needs a
sorted input and **transitivity**, but not totality. Negative filtering needs
neither. This gives a smaller proof route than the insertion induction
suggested in the historical reuse plan, without changing any source statement
or that plan's identity.

Current sorting and selection clients already use the existing correctness
contracts. X002 already supplies an actual measured insertion/sort and a
connected sorting-to-rank client. Chapter 26 has a genuine later ordinary
insertion by cached weight, but its inspected uses need existing forward,
permutation and mapping laws, not the missing filter equalities. Chapter 14's
chosen sorted-list exercise implementation likewise does not establish a new
need for those equalities. Details and qualifications are in sections 6–8.

This disposition retains **all 112 current Chapter 2 obligations**, including
C02-009 and every supporting claim in C02-094–098. An existing proof of the
final stability theorem does not turn its displayed source helpers into
optional prose coverage.

## 2. Inputs, pins and bounded reading

Paths below are relative to `/workspace/scratch/845aa1048b05` unless a Git
revision is specified. Ordinary SHA-256 identities describe inspected source
bytes, not elaboration or acceptance evidence.

| Input read in full | Bytes / lines | SHA-256 |
|---|---:|---|
| `fdsa-control/tickets/FDSA-XI01.md` | 2,571 / 44 | `3fa60ef644bcfad90930520e055e1e3a6d97d687d5715c7e0d714ef0349578fb` |
| `fdsa-control/research/chapter02-obligations.md` | 42,539 / 391 | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `fdsa-control/research/chapter02-reuse-plan.md` | 31,586 / 346 | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| `fdsa-control/reviews/insertion-requirements.md` | 3,257 / 60 | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `fdsa-control/research/insertion-cost-preflight.md` | 10,516 / 164 | `325802496d4270b8ee167227fd1d6f1eecebf7a40123121d925d0e899d9a66a1` |
| Stopped `fdsa-control/research/ordered-insertion-source-preflight.md` | 27,603 / 363 | `42ad87047a0f9debbdf8729e9fa0ff9158ef1d9486115fe752c52e5ec6219ab5` |
| Pinned `Mathlib/Data/List/Sort.lean` | 35,291 / 901 | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |

The reuse plan's opening count of 107 describes its historical snapshot. The
current inventory has 112 rows; the frozen Chapter 2 requirements intentionally
retain their original snapshot, with the appended scope reconciliation
preserving C02-001–107 and unpacking C02-088 into C02-108–112. No inventory,
requirement, old plan or ticket is changed here.

The project reads used the pinned Nix development shell for read-only Git
commands. Current conaled APIs were read at the repaired C1 candidate
`07e480f6ec9958d4975bb90151005b84f2907614`; the two X002 source files were read
from the **exact c80 prefix**, rather than inferred from a later branch tip.
The relevant existing `Stable`, `Sort`, `StableSorting` and `Selection.Rank`
files are byte-identical at those two revisions. Applicable AGENTS and linked
architecture/domain/implementation guidance were read within this workflow:
reuse the canonical operation and ordinary laws, keep semantic observation
separate from execution, and avoid unnecessary payload capabilities or a new
general framework.

Pinned Mathlib is `56a005855ea17e0b0958f73ec801ae140b0a1679`, at
`conaled/.lake/packages/mathlib`. Lean is v4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. List support signatures were read
from the retained primary copies and the installed toolchain's source files;
no Lean process was invoked. The complete canonical Mathlib sort file and all
tracked Mathlib mentions of `orderedInsert` were inspected for the narrow
missing-law search. The other mention is the different `simplicialInsert`
construction in `AlgebraicTopology/SimplexCategory/GeneratorsRelations/NormalForms.lean`;
it supplies no filter-insertion equality. This is a scoped absence result at
the pin, not a claim about future libraries.

Primary source correspondence was checked against `book-source/Sorting.thy`,
especially 346–405, and the stopped source report. The theory is 14,846 bytes,
SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`,
pinned at Isabelle `f86f290225eebcc52c1ae7dba2e098f405f51c21`:
<https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorting.thy>.
The official July 27, 2026 book PDF is
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>, retained at
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The later theory pin is not asserted to be the PDF's generating revision.

## 3. Exact coverage mapping

Write `I r x xs` in this report for the existing `List.orderedInsert r x xs`.
This abbreviation is explanatory, not a proposed Lean definition. Its source
decision is left-on-true: nil returns `[x]`; a nonempty list returns `x::y::ys`
when `r x y`, otherwise retains `y` and inserts into `ys`. The keyed source
specialization is `r a b := key a ≤ key b`. Equal keys take the first branch.

| Obligation | Exact reuse | Remaining connection at active Chapter 2 |
|---|---|---|
| C02-009, source (2.4) | `List.Pairwise.orderedInsert` gives forward sortedness; `List.sublist_orderedInsert` plus `List.Pairwise.sublist` gives the converse. | Assemble the actual iff. Do not substitute only preservation or a result about sorting the whole list. No extra insertion operation is needed. |
| C02-094, (2.35) and one-insert support | `Sorting.insertionOn_spec` supplies whole-sort sortedness/permutation/stability. `List.perm_orderedInsert`, `List.mem_orderedInsert`, and `List.pairwise_map` supply full-occurrence, membership and key-order bridges. | Expose the exact keyed source recurrence and its one-insert sortedness iff. Multiset equality is the ordinary permutation quotient; no payload equality decision is needed. |
| C02-095, (2.36) | `orderedInsert_nil` and `orderedInsert_cons_of_le`. | A nil/cons proof under `∀ y ∈ xs, r x y` retains the source all-members premise. The existing head theorem is stronger on nonempty inputs; a renaming wrapper is unnecessary. |
| C02-096, (2.37) | Old-list sublist, filtered insertion permutation, equal-length sublist equality. | The exact negative filter equality is absent from the inspected exports. Prove the thin equality for arbitrary decidable `r`, with only the predicate being false on `x`. |
| C02-097, (2.38) | `List.Sublist.orderedInsert_sublist` under `IsTrans α r`, then filtering and equal lengths. | The exact positive filter equality is absent from the inspected exports. Preserve `xs.Pairwise r` and the predicate being true on `x`; totality is not needed. |
| C02-098, Lemma 2.11 | `(Applications.Sorting.insertionOn_spec key xs).stable k`. | This is the exact equal-key filtered-list observation after the source-operation correspondence. Reuse its existing proof; separately retain C02-095–097. |

For C02-094, `Multiset.coe_eq_coe` in `Mathlib/Data/Multiset/Defs.lean:100`
states `(l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂`. `Multiset.cons_coe` in
`ZeroCons.lean:101` identifies multiset cons with the list cons quotient.
Thus `perm_orderedInsert` expresses preservation of every old occurrence and
one new occurrence without `DecidableEq α`. Using `List.count` or erasure here
would introduce an unnecessary equality decision. `mem_orderedInsert` gives
the set-membership statement directly, independently of the quotient bridge.

## 4. Canonical insertion API and premise placement

The following are the inspected declarations at the Mathlib pin. `r` is a
relation on `α`; executing insertion requires `[DecidableRel r]`. Types `α`
and `β` may have independent universes. The line locations refer to
`Mathlib/Data/List/Sort.lean`.

| Declaration / call shape | Statement or hypotheses relevant here |
|---|---|
| `List.orderedInsert r x xs` (43–45) | Actual canonical recursion, with no relation laws, payload order, equality or inhabitance assumption. |
| `List.orderedInsert_cons_of_le r xs h` (53–55) | For implicit `a b`, `h : r a b` gives `orderedInsert r a (b::xs) = a::b::xs`. |
| `List.orderedInsert_of_not_le r xs h` (57–58) | For `h : ¬ r a b`, the actual result is `b :: orderedInsert r a xs`. |
| `List.orderedInsert_length r xs x` (74–76) | Length is `xs.length + 1`. No sortedness. |
| `List.mem_orderedInsert r` (90–92) | `a ∈ orderedInsert r b xs ↔ a = b ∨ a ∈ xs`; equality is propositional, not a required global decision. |
| `List.perm_orderedInsert r x xs` (101–106) | `orderedInsert r x xs ~ x::xs`. No sortedness. |
| `List.sublist_orderedInsert (r := r) x xs` (170–171) | `xs <+ orderedInsert r x xs`. The relation is implicit in this declaration. |
| `List.Sublist.orderedInsert_sublist (r := r) x hs hb` (177–197) | Under `[IsTrans α r]`, `hs : as <+ bs` and `hb : bs.Pairwise r` imply `orderedInsert r x as <+ orderedInsert r x bs`. No totality. |
| `List.Pairwise.orderedInsert (r := r) x xs h` (203–213) | Under `[Std.Total r] [IsTrans α r]`, `h : xs.Pairwise r` gives `(orderedInsert r x xs).Pairwise r`. No antisymmetry. |
| `List.Pairwise.insertionSort_eq` (150–152) | A pairwise-ordered list is fixed by `insertionSort`; this theorem is before the total/transitive section and needs neither global law. |
| `List.perm_insertionSort r xs` (113–115) | Canonical full-sort permutation. |
| `List.pairwise_insertionSort r xs` (218–220) | Full-sort pairwise order under the same total/transitive assumptions. |
| `List.sublist_insertionSort` (228–239) | An ordered sublist of the input remains a sublist of its insertion-sort output. This is the existing conaled stability route. |

`List.insertionSort r` is the right fold of this same insertion (61–66). The
book's recursive tail-sort/insert equations therefore need a value-level
recurrence bridge, not a separately defined sorter. The all-members theorem
`insertionSort_cons_of_forall_rel` at 124–127 concerns the **whole sort**; it
must not be cited as though it already states the one-insert source (2.36).

### Existing mapping contract is already usable

The actual signature at 94–97 is:

```lean
List.map_orderedInsert r s (f : α → β) (xs : List α) (x : α)
  (h₁ : ∀ a ∈ xs, r a x ↔ s (f a) (f x))
  (h₂ : ∀ a ∈ xs, r x a ↔ s (f x) (f a)) :
  (List.orderedInsert r x xs).map f =
    List.orderedInsert s (f x) (xs.map f)
```

Both operational relations have their own decision instances. The pinned
public theorem explicitly asks for **both** local equivalences, even though
the displayed insertion only tests the second orientation. Use those actual
premises. There is no need to add a replacement theorem just to weaken one
unused premise for this task. No injectivity of `f` is required; a
key-preserving payload map discharges the two comparisons by rewriting keys.
This transports a value, not the work of computing maps, keys or comparisons.

`List.map_insertionSort r s f xs` at 135–143 similarly uses comparison
equivalence for every pair from the old list. Existing conaled
`StableSort.map` separately transports the stronger stable-sort contract
across a key-preserving map, with independent payload universes.

## 5. Missing thin statements and exact proof routes

The schemas below are **proposals for later Chapter 2 source coverage**. They
are not frozen public names, a source release, or a proposed new shared file.
Use `p : α → Bool`, as `List.filter` does. A Prop predicate can be exposed
through `decide` with `[DecidablePred P]`; it does not require deciding payload
equality. An explicit `x : α` is supplied by insertion, not by `Inhabited α`.

### 5.1 Sortedness converse and iff

For any observation relation `R : α → α → Prop`, including one unrelated to
the insertion decision `r`, the law-free implication is:

```text
(orderedInsert r x xs).Pairwise R → xs.Pairwise R.
```

Apply `List.Pairwise.sublist` to `List.sublist_orderedInsert`. There is no
`DecidableRel R`, transitivity, totality or equality premise. To obtain the
source iff with `R = r`, combine this with the canonical forward theorem
under `[Std.Total r] [IsTrans α r]`. These are the canonical sufficient
uniform hypotheses; no claim is made that they are logically necessary for
each fixed input. For keyed source order, rewrite through `List.pairwise_map`
with `r a b := key a ≤ key b`. The source linear-order specialization satisfies
the hypotheses without imposing an order on payloads.

### 5.2 All-members immediate insertion

The proposed observation is
`(∀ y ∈ xs, r x y) → orderedInsert r x xs = x::xs`.
Case split `xs`. Nil is the existing equation; at a cons, apply the hypothesis
to the head and then `orderedInsert_cons_of_le`. No sortedness or relation law
is used. Keep the source premise in its source witness, but do not manufacture
a parallel operation or redundant head theorem. The premise is sufficient,
not necessary: insertion of `2` into `[2,0]` under Nat `≤` stops at the head.

### 5.3 Negative filtering

Schema, with only `[DecidableRel r]`:

```text
p x = false → (orderedInsert r x xs).filter p = xs.filter p.
```

Let `F := xs.filter p` and `J := orderedInsert r x xs`.

1. Filter `List.sublist_orderedInsert (r := r) x xs` to obtain `F <+ J.filter p`.
2. Filter `List.perm_orderedInsert r x xs`. By `p x = false` and `filter_cons`,
   this is a permutation from `J.filter p` to `F`.
3. Its length equality, reversed, supplies the premise for
   `List.Sublist.eq_of_length` on the first sublist. Symmetry gives the desired
   equality.

The proof does not need to inspect the insertion branches, and neither
sortedness nor any order law enters. It preserves the complete filtered
subsequence, not merely its set or permutation class.

### 5.4 Positive filtering

Schema, with `[DecidableRel r] [IsTrans α r]`:

```text
xs.Pairwise r → p x = true →
  (orderedInsert r x xs).filter p = orderedInsert r x (xs.filter p).
```

Let `F := xs.filter p`, `I := orderedInsert r x F`, and
`J := orderedInsert r x xs`.

1. `List.filter_sublist` gives `F <+ xs`. Apply
   `List.Sublist.orderedInsert_sublist (r := r) x` with this sublist and the
   original `xs.Pairwise r`, obtaining `I <+ J`.
2. Every member of `I` passes `p`: `mem_orderedInsert` reduces membership to
   the inserted `x` or a member of `F`; use `p x = true` or `mem_filter`.
   Thus `List.filter_eq_self` gives `I.filter p = I`.
3. Filter the sublist from step 1 and rewrite its left side to get
   `I <+ J.filter p`.
4. `orderedInsert_length r F x` gives `I.length = F.length + 1`.
   Filtering `perm_orderedInsert r x xs` and simplifying with `p x = true`
   gives `(J.filter p).length = F.length + 1`.
5. Apply `Sublist.eq_of_length` and take symmetry.

This route needs **no `Std.Total r`, reflexivity, antisymmetry, payload
equality, or key equality decision**. The exact existing sublist theorem
requires transitivity because an insertion can stop at an old head that the
filter discards; pairwise order and transitivity force the same stopping
order relative to surviving tail elements. For a key relation, transitivity
of the key `≤` relation suffices for this helper. The source linear order is
a lawful specialization, not a necessary payload structure.

### 5.5 Exact supporting signatures

These primary Lean APIs, rather than remembered theorem names, were checked:

| API | Actual relevant shape and location |
|---|---|
| `List.Pairwise.sublist` | `l₁ <+ l₂ → l₂.Pairwise R → l₁.Pairwise R`; `Init/Data/List/Pairwise.lean:47`. |
| `List.pairwise_map` | `(l.map f).Pairwise R ↔ l.Pairwise (fun a b => R (f a) (f b))`; `Pairwise.lean:128`. |
| `List.filter_cons` | The cons filter is `if p x then x :: xs.filter p else xs.filter p`; `Lemmas.lean:1267`. |
| `List.filter_eq_self` | `l.filter p = l ↔ ∀ a ∈ l, p a`, with Bool-to-Prop coercion; `Lemmas.lean:1286`. |
| `List.mem_filter` | `a ∈ xs.filter p ↔ a ∈ xs ∧ p a`; `Lemmas.lean:1310`. |
| `List.filter_sublist` | `l.filter p <+ l`; `Lemmas.lean:1423`. |
| `List.Sublist.filter p hs` | Filters both sides of `hs : l₁ <+ l₂`; `Sublist.lean:312`. |
| `List.Perm.filter p hp` | Filters both sides of a list permutation; `Perm.lean:233`. |
| `List.Perm.length_eq hp` | A permutation gives equality of lengths; `Perm.lean:142`. |
| `List.Sublist.eq_of_length hs hlen` | `l₁ <+ l₂` and `l₁.length = l₂.length` give `l₁ = l₂`; `Sublist.lean:257`. |

The critical orientations are explicit above: negative filtering first proves
`F = J.filter p`, whereas positive filtering first proves `I = J.filter p`.
Both are then reversed. No circular equality or assumed insertion/filter
commutation is used to obtain the length premise.

## 6. Actual conaled reuse and X002 cost boundaries

The following complete files were read at C1 candidate `07e480f...`:

| File | Bytes / lines | SHA-256 |
|---|---:|---|
| `Applications/Sorting/Stable.lean` | 3,704 / 87 | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| `Applications/Sorting/Sort.lean` | 5,922 / 128 | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| `Examples/StableSorting.lean` | 5,041 / 124 | `c894760e594cdc31d9dda54553eeff666156c81f7903dea82738c8a95faaf193` |
| `Applications/Selection/Rank.lean` | 3,713 / 91 | `4a82df75593d909e2968bf1e27cbfea52c9795abfe81250bb2385e7dfc16f965` |
| `Examples/RankSelection.lean` | 5,085 / 121 | `641a752cdee9b2ab30e66bb2f7feda2548cffebfe6733460b52ff5f7e119520e` |
| `Applications/Huffman/SourcePriority.lean` | 2,142 / 58 | `de80cc229d7854a18efcf6901cc166a41a258d7371ddfef54ac603884eb9af4c` |

`Applications.Sorting.insertionOn` (`Sort.lean:17–18`) takes arbitrary payloads
and a key function, with `[LE κ] [DecidableLE κ]`. The actual
`insertionOn_spec` (`94–110`) additionally takes `[Std.IsLinearPreorder κ]`
and `[DecidableEq κ]`, returning `StableSort key xs (insertionOn key xs)`.
The equality decision belongs to the equal-key filter observation in
`Stable` (`Stable.lean:17–19`), not to payloads or raw insertion. If only
permutation and sortedness are needed, use the canonical theorems directly
instead of importing the whole stable package's equality premise.

Its existing stability proof builds an equal-key filtered input as a sorted
sublist, uses `List.sublist_insertionSort`, and applies `stable_of_sublist`
(`Stable.lean:27–34`). That last proof is already a local precedent for the
filter/sublist/equal-length route. `sortOn_eq_insertionOn` (`113–115`) uses the
stronger linear-order uniqueness contract; it equates outputs, not algorithm
costs. Existing tagged-record and noninjective payload-map examples exercise
these public contracts. `sorted_permutation_not_stable` in
`Examples/StableSorting.lean:114–122` already separates sorted permutation
from exact equal-key stability.

At the **exact initial c80 prefix**, the complete retained X002 files are:

| File | Bytes / lines | SHA-256 |
|---|---:|---|
| `Applications/Resources/InsertionSort.lean` | 7,257 / 178 | `385ea0ba077ac05a10547bc95cd37eb4fa80ef8fe826c6e2c250cca33f2b4aad` |
| `Examples/InsertionCosts.lean` | 3,862 / 101 | `f808254936f1757e639b4f49d94904056b92c84802d9a887a16d31c861c7ff37` |

`Resources.InsertionSort.insertRun` (`19–26`) is the actual branch-dependent
measured computation. Nil and immediate-head insertion cost one invocation;
the recursive branch costs the actual child plus one. `insertRun_value`
(`28–32`) erases to `List.orderedInsert`. Existing cost contracts are
`insertRun_cost_bounds`, `insertRun_cost_of_head`, `insertRun_cost_of_all`,
and `insertRun_cost_of_all_not` (`35–65`). The all-members **cost** theorem
does not itself discharge source (2.36)'s value equality.

`sortRun` (`68–70`) composes the actual tail-sort result with actual insertion.
It already has erasure, length, exact cons-cost, lower, triangular and square
upper bounds, sorted/reversed-range cases, and `sortRun_stable` (`171–176`).
`Examples/InsertionCosts.lean` contains immediate-head/full-traversal/tied-head
cases, arbitrary-payload keyed correctness, equal-key stability and an actual
sorting-to-occurrence-rank connection. In particular, `sorted_result_has_rank`
at 75–84 consumes `Applications.Selection.pairwise_ranked`, and
`small_rank_with_sort_budget` at 96–99 combines it with the sorting-only budget
21 for lists of length at most five. Indexing and the rest of selection are
not charged by that statement.

The X002 record names original candidate
`697bcf242ce65d74815b5639bddb1c6e754dd10f` on base
`1aabd512284fe86254278ac631eda061d311050b`, with historical focused compilation
results and full verification/reviews still pending. This report neither
reruns those checks nor converts focused evidence into acceptance. It also
does not describe X002 as never compiled merely because this task is read-only.

These are invocation observations. An empty insertion has one call and zero
comparisons; an immediate nonempty insertion has one call and one comparison.
There is no universal insertion `entries = comparisons + 1` law analogous to
ordinary merge. Computing a key, a predicate, a filter, or a map is not charged
by the value lemmas or automatically by X002. None of the proposed filter
equalities states equality of the measured observations.

## 7. Connected cases and genuine consumer assessment

The following discriminating cases support the mathematical statement design;
they are not new required source files or compiled results.

- **Negative helper on raw input:** insert `(2,false)` by first component into
  `[(1,true),(3,false),(0,true)]`, then filter by second component. The old list
  is unsorted, yet the result is exactly `[(1,true),(0,true)]`, as before the
  insertion. No order law or sortedness is needed for this negative case.
- **Positive keyed helper:** insert `(2,false)` into
  `[(0,false),(1,true),(3,true),(4,false)]` and retain false second components.
  Both value routes return `[(0,false),(2,false),(4,false)]`. Existing
  `insertRun` costs are three on the original list and two on the filtered
  list. This is a concrete failure of cost equality, even though the value
  commutation is lawful. It does not price the filter itself.
- **Sortedness cannot be omitted:** under Nat `≤`, insert `2` into `[3,0]`
  and filter even values. The two outputs are `[2,0]` and `[0,2]`.
- **Transitivity cannot simply be omitted while retaining totality:** on
  labels `A,B,C`, use equality plus `A r B`, `B r C`, `C r A`. The relation is
  total; `[B,C]` is pairwise ordered. Inserting `A` and retaining `A,C` gives
  `[A,C]`; inserting into the filtered `[C]` gives `[C,A]`. Also `¬ r A C`,
  so forward sortedness fails. The law-free sublist converse still holds.
- **Empty and tie boundaries:** nil insertion and sorting use their existing
  equations; an explicit inserted payload is needed but no default is. Lists
  over `Empty` have the genuine empty-sort case. Equal keys do not imply equal
  payloads, and insertion stops before a tied old head even if its tail is
  unsorted. Existing arbitrary-payload and tied-head X002 examples already
  connect these distinctions to the actual computation.

The tracked-project search at `07e480f...` found insertion uses in
`Sorting.Sort`, `Examples.StableSorting`, and `Examples.RankSelection`, with
the X002 additions inspected separately at c80. None consumes the two missing
filter equalities. Rank selection uses sortedness/permutation and existing
sort-output agreement; it is not a reason to import a selection algorithm into
the value-law layer.

The stopped source assessment supplies the later-book comparison. Its claims
were checked against the actual local Huffman passages at 836–839, 1743–1750
and 2052–2076:

- `insortTree` is exactly ordinary insertion by `cachedWeight ≤`, preserving
  occurrences and putting a new tie first. Existing `orderedInsert_length`,
  permutation, forward sortedness and mapping are relevant reuse.
- `sortedByWeight_insortTree` instead concludes order by **computed** weight
  and explicitly assumes `height t = 0` and `height_F ts = 0`. The all-leaf
  qualification and cache/computed-weight distinction are already retained
  in C26-026/081; a raw cached-key theorem does not discharge them.
- `cachedWeight_splitLeaf` preserves the insertion key. The subsequent two
  `splitLeaf_F_insortTree` theorems preserve consistency, symbol-membership and
  frequency premises for a forest transformation. This is a mapping route,
  not filtering, and supplies no additional use of the missing XI01 laws.
- Current conaled `Huffman.SourcePriority` is an actual leftist specialization
  of the existing queue algorithm, using two removals and insertion. Its full
  file contains no ordinary ordered-list insertion. Do not identify it with
  the source cached-tree-list recurrence or transfer X002's invocation tariff
  to the queued Huffman comparison bound C26-088.

The primary Huffman file is
`book-source/afp-Huffman-2026-10-26/Huffman/Huffman.thy`, 101,517 bytes/2,363
lines, SHA-256 `7bdc838bbdf7347fb78440a5b3c8dadaf6b7c228e6e3cae6f2d1fb49582837bf`.
It came from <https://isa-afp.org/release/afp-Huffman-2026-10-26.tar.gz>, archive
SHA-256 `229ba4f3037d9f02dff7df8836d8a5a95f91c8463c8572cb0ae1a93dea2bfd77`.
No new download or finite-enumeration campaign was performed.

The source assessment also distinguishes Chapter 5's duplicate-suppressing
`ins_list` and Chapter 17's carrying/linking `ins_tree`; neither is this
occurrence-inserting operation. The chosen Chapter 14 sorted-list queue is a
later concrete client of existing insertion laws, not already implemented by
current `exactList`, and not evidence that a new generic filter theorem is a
cross-cutting prerequisite. All those algorithm, invariant and cost bridges
remain in their original chapters.

## 8. Smallest later implementation route and limits

No new base is selected here. The semantic ingredients are already present at
the current C1 candidate; measured connected clients additionally belong to
the unchanged c80 prefix. There is no reason to depend on the later potential
addition or any unrelated unaccepted shared draft for these value statements.

When Chapter 2 becomes active, the minimal work is:

1. Use the canonical nil/cons equations to record exact ordinary/keyed source
   correspondence, the source sortedness iff and all-members cons observation.
2. Prove the two missing filter equalities with the sublist/length routes above,
   then specialize to the book's key order. Keep the generic sufficient
   hypotheses distinct from the source specialization.
3. Connect existing permutation, membership, mapped-key order and
   `insertionOn_spec.stable` to all the retained C02-094–098 statements.
4. Add only meaningful clients/counterexamples in that chapter's then-approved
   source scope. If a measured client is used, consume `insertRun_value` and
   its actual cost laws; do not infer cost transport from value equality.

For placement, `Mathlib.Data.List.Sort` already supplies the semantic proof
ingredients. Thin additions could live with the existing sorting value layer;
the historical suggestion of `Applications/Sorting/Insertion.lean` is not a
frozen requirement to create another module. A later chapter implementation
may choose that grouping if its actual coverage makes it useful. No wrapper
that only renames `orderedInsert`, `insertionSort`, `map_orderedInsert` or the
existing stable contract is justified. The thin value layer needs no resource,
selection or probability import. An explicit multiset presentation may use the
existing Multiset quotient modules, without changing the operational carrier.

The principal remaining elaboration work is ordinary Lean proof construction:
making the implicit relation argument at `sublist_orderedInsert` explicit when
needed, applying the two explicit sublist/filter arguments in the pinned
order, and rewriting Bool filter branches and length orientations. The exact
support APIs were inspected; the displayed proof routes have not been run
through Lean and are not compiler predictions. No concrete mathematical or
API obstruction was found. The unknown outcome of any pending project gate
is not filled in by this source assessment.

Mathlib/Lean code carries Apache-2.0 notices. Source adaptation from
`Sorting.thy` must retain Tobias Nipkow's attribution and the applicable
Isabelle BSD notice in `book-source/ISABELLE-COPYRIGHT`; the Huffman theory
credits Jasmin Christian Blanchette and is covered by the retained AFP BSD
notice in `book-source/AFP-LICENSE`. This original report references those
sources and does not redistribute the whole book. No new licensing choice
or copied implementation is introduced.

All original sorting algorithms, exercises, stability/termination/value
claims, source comparison and invocation metrics, exact/asymptotic bounds,
natural-run/builder assertions and later selection/Huffman/ADT obligations
remain queued. This report changes none of them, none of the existing plans,
and no gate. Only this permitted API-preflight file was written.
