# Priority queue observation, minimum, and merge: case preflight

Prepared 2026-11-02 for a possible bounded cross-cutting unit. This is source-only
case preparation, not a requirements freeze, implementation, review approval,
or Chapter 14 activation. The complete Chapter 14 reading and obligation note
were read, together with the actual interfaces and implementations below.

The inspected worktree is `conaled-ch01-cost-models`, the existing directory
identified by the parent's `conaled-ch01-cost-models07e` shorthand. The parent
reports baseline `07e480f6ec9958d4975bb90151005b84f2907614`; no Git/ref command was
used to recheck it. File identities below pin the actual source read. The sole
Chapter 1 checker remains the parent's session 83124. The unaccepted XA01
commit `20a5b55` and checkpoint 0049 supply no dependency to these cases.

## 1. Sources and the existing contract

The full [Chapter 14 text](../../book-source/chapter14.txt) covers printed
pp. 179–182. Its seven base laws preserve occurrences and specify deletion and
minimum only on valid nonempty queues. The two merge extension laws permit
overlapping multisets. The companion `Priority_Queue_Specs.thy` adds `is_empty`
and its law.
The [chapter obligation note](chapter14-obligations.md) already records that
distinction, the empty-type decision, and later algorithm/cost obligations;
this note does not repeat that inventory.

The actual [ExactPriority](../../conaled-ch01-cost-models/Applications/Search/ExactPriority.lean)
interface supplies `ExactQueue` and `ExactLaws` over the
[PriorityInterface](../../conaled-ch01-cost-models/Applications/Search/PriorityInterface.lean)
`Operations`. Operations are `empty`, batch `add`, and
`remove : Carrier → Option ((α × π) × Carrier)`. The selected `entries`
observation and `Valid` predicate are separate from the operations.

| Actual public result | Exact premise boundary and use |
|---|---|
| `Q.empty_entries`, `Q.empty_valid` | The designated empty state has no occurrences and is valid. They do not identify every state having empty contents with that state. |
| `Q.add_exact xs q` | Unconditionally gives `entries (add xs q) ~ xs ++ entries q`, even for an invalid raw state. Singleton `xs` is source insertion. |
| `Q.add_valid xs q hq` | Propagates an actual input validity proof. Exact occurrence insertion alone does not imply this invariant. |
| `Q.remove_none q` | Unconditionally equates `remove q = none` with `entries q = []`. An invalid nonempty raw state cannot return `none` under this contract. |
| `Q.remove_spec q e r hq hr` | Requires `Valid q` and the actual equation `remove q = some (e,r)`; concludes residual validity, `entries q ~ e :: entries r`, and `e.2 ≤ a.2` for every input entry `a`. |
| `LeftistQueue.combineQ_entries a b` | The actual merge preserves the concatenated occurrence list up to permutation without either validity premise. |
| `LeftistQueue.combineQ_valid a b ha hb` | Both actual input states must be valid. This supplies the independent merge-invariant law. |

Neither `Operations` nor `ExactQueue` contains a merge field. For these cases,
supply the existing `combineQ` and the two stated laws against the existing
observation. A parallel queue hierarchy or new ADT syntax is unnecessary.

In the rest of this note, `ν(q)` means the multiset coercion of `Q.entries q`,
and `μ(q)` means the multiset coercion of `(Q.entries q).map Prod.snd`. These are
mathematical abbreviations for the case discussion, not names of existing or
newly written Lean declarations. `ν` retains items and priorities; `μ` retains
all priority occurrences. The source element-only queue is the specialization
`ExactQueue Unit π`, with source observation `μ`.

The read Mathlib bridges are `List.Perm.map`, `Multiset.coe_eq_coe`,
`Multiset.coe_add`, `Multiset.singleton_add`, and `Multiset.mem_coe`.
After a successful valid removal, the permutation law yields
`μ(q) = {e.2} + μ(r)` without decidable equality. If the source subtraction
notation is desired, `Multiset.sub_singleton` and `Multiset.erase_cons_head`
give `μ(r) = μ(q) - {e.2}` with decidable equality on priorities. This removes
one occurrence. A source linear order supplies that decidable equality.

## 2. Empty observations and empty types

The smallest positive empty case uses the actual `exactLeftist` with
`α = Unit`, `π = Nat`: its state is `emptyQ = PQ.null`, `entries = []`,
`deleteQ = none`, and `nullQ = true`. The corresponding actual `exactList`
state is `[]`, and `listRemove [] = none`. The generic connection is
`Q.empty_entries` followed by `Q.remove_none`, with `Q.empty_valid` establishing
the separate invariant. No default minimum is involved.

A semantic optional priority can be observed by
`(Q.remove q).map (fun z => z.1.2)`. Its empty value is `none`, and on a valid
nonempty observation it is `some` of a least priority. This expression uses
the supplied removal operation. It proves no cheap-access claim: leftist
`deleteQ` also calls `combineQ`, and `listRemove` sorts before selecting a head.
A direct root/head observer would need its own agreement proof if later added.

| Boundary | Independently expected conclusion and connection |
|---|---|
| Empty item type: `ExactQueue Empty Nat` | Every `entries q : List (Empty × Nat)` is empty, so `Q.remove_none q` forces `remove q = none` for every raw state. Both existing realizations can support this; the item type needs no `Inhabited` instance. |
| Empty priority type: `ExactQueue Unit Empty` | Every entry list is again empty. An order/comparison on `Empty` is vacuous and may be supplied locally. `Option Empty` still has `none`; a total priority getter into `Empty` would be impossible even at `Q.empty`. |
| Empty carrier | `Operations.empty : Carrier` rules out an empty carrier. This is different from permitting an empty item/priority type. |
| General observational emptiness | From `entries q = []` one obtains `remove q = none`, not `q = Q.empty`. The raw carrier may retain hidden state. For the concrete leftist carrier, the actual constructor equations do identify an empty entry list with `PQ.null`. |

If a separate carrier-valued deletion view is later introduced, its `none`
branch must be stated. Returning the same state or the designated empty state
would both require a deliberate definition; the current combined `remove`
already returns `none`. The book's concrete empty-tree deletion is the identity,
whereas its abstract deletion law has a nonempty premise.

### Finite observation realizations

Every finite entry multiset has a valid realization in any supplied
`ExactQueue`: for a representative list `xs`, take `Q.add xs Q.empty`.
`Q.add_valid xs Q.empty Q.empty_valid` supplies validity; `Q.add_exact` and
`Q.empty_entries` identify its entry multiset with that of `xs`. To phrase
this for an arbitrary `Multiset (α × π)`, the inspected
`Multiset.toList`/`Multiset.coe_toList` provide a representative, using choice.
The list-input construction itself uses the existing executable `add`.

For priority multisets, supply an explicit payload `a : α` and add the list
`xs.map (fun p => (a,p))` to `Q.empty`. Mapping the resulting exact occurrence
law by `Prod.snd` gives priority multiset `xs`, with validity propagated as
above. `Unit` supplies `a = ()`; the list `[1,1,3]` is the concrete positive
instance reused in the next section, with all three occurrences present.

The empty multiset needs no payload witness: `Q.empty` realizes it. A
nonempty target priority multiset does need an available payload. For
`exactLeftist` or `exactList` at `Empty` items and `Nat` priorities, every
priority observation is empty, so `{1}` has no realization. Thus arbitrary
priority-surjectivity cannot be claimed without the appropriate domain
condition. This introduces no global `Inhabited` constraint or infinite-map
model; all target multisets here are finite by their existing type.

## 3. One duplicate minimum and a connected merge–insert–remove client

All priorities in this section are naturals and all payloads are `()`.
For independently checking actual shapes, write `E = PQ.null`,
`N k p l r = PQ.fork k () p l r`, and `S p = N 1 p E E`.
These abbreviations describe the existing raw constructor; smart `fork`
may exchange the children according to their ranks.

### Duplicate minimum

Take `D = makeQ [((),1),((),1),((),3)]`. The right fold in `makeQ` builds

```text
D = N 1 1 (N 1 1 (S 3) E) E
deleteQ D = some (((),1), N 1 1 (S 3) E).
```

The priority occurrence list changes from `[1,1,3]` to `[1,3]`; its size
changes from 3 to 2 and the multiplicity of `1` changes from 2 to 1.
The returned priority is 1 and the remainder remains nonempty. Removing every
occurrence of 1, returning `[3]`, would drop two occurrences instead of the
specified one.

Connect the input through `makeQ_spec`, the actual removal equation through
`exactLeftist.remove_spec` (or the underlying `deleteQ_spec`), and the source
multiset through `List.Perm.map` and `Multiset.coe_eq_coe`. Establish the
concrete expected values separately from that public connection. `Nodup` is
neither true for this input nor part of the exact queue invariant.

### Main nonempty sequential client

Use the actual operations in this order:

```text
A = makeQ [((),1),((),3)]
B = makeQ [((),1),((),2)]
M = combineQ A B
I = exactLeftist.add [((),2)] M
deleteQ I = some (((),1), R).
```

The singleton batch operation is definitionally `insertQ () 2 M`.
The independently calculated shapes and observations are:

| Stage | Actual leftist shape | Actual `entries` priorities | Multiset and count |
|---|---|---|---|
| `A` | `N 1 1 (S 3) E` | `[1,3]` | `{1,3}`, size 2 |
| `B` | `N 1 1 (S 2) E` | `[1,2]` | `{1,2}`, size 2 |
| `M` | `N 2 1 (S 3) B` | `[1,3,1,2]` | `{1,1,2,3}`, size 4 |
| `I` | `N 2 1 (N 2 1 (S 2) (S 2)) (S 3)` | `[1,1,2,2,3]` | `{1,1,2,2,3}`, size 5 |
| `R` | `N 2 1 (S 2) (N 1 2 (S 3) E)` | `[1,2,2,3]` | `{1,2,2,3}`, size 4 |

The two merge operands share priority 1. The merge doubles its multiplicity;
no disjointness premise is available or wanted. Insertion retains both copies
of 2, and removal deletes one of the two copies of 1. In particular the inserted
2 survives the final removal. This exercises each of merge, insertion, and
deletion without assuming that the result state is determined by its multiset.

The proof connection must carry the actual intermediate validity:

1. Obtain `Valid A` and `Valid B` from the respective `makeQ_spec` calls.
2. Feed those proofs to `combineQ_valid A B`; use `combineQ_entries A B` for
   the independent exact-content equation.
3. Feed `Valid M` to `exactLeftist.add_valid [((),2)] M`; use
   `exactLeftist.add_exact [((),2)] M` for insertion content.
4. Feed `Valid I` and the actual successful-removal equation to
   `exactLeftist.remove_spec`. Its residual-validity component establishes
   `Valid R`; its permutation component yields the exact remaining multiset;
   its lower-bound component certifies the returned minimum 1.

The observations have independently nonzero sizes at both the initial merge
and removal stages, so the client is not an empty-state or impossible-premise
specialization. If a general observation bridge is added, this case should
consume that bridge as well as the existing operational laws.

For a small second realization, existing `exactList` with supplied merge
`List.append` has invariant `True` and exactly the same multiset addition law.
Its corresponding raw lists are `[1,3]`, `[1,2]`, `[1,3,1,2]`, and after `add`,
`[1,3,1,2,2]`; removal sorts to `[1,1,2,2,3]` and leaves `[1,2,2,3]`.
This is an optional specialization of the same semantic client, not a new
sorted-list queue algorithm. In particular it does not discharge the book's
constant-time minimum/deletion exercise.

## 4. Tied payloads, priority agreement, and order hypotheses

For the smallest payload-sensitive case use `PQ Bool Nat`. Let
`F = PQ.fork 1 false 1 PQ.null PQ.null` and
`T = PQ.fork 1 true 1 PQ.null PQ.null`. Both are valid singleton heaps.

| Actual expression | Independently expected result |
|---|---|
| `combineQ F T` | Root `(false,1)`, left child `T`, right child empty |
| `deleteQ (combineQ F T)` | `some ((false,1), T)` |
| `combineQ T F` | Root `(true,1)`, left child `F`, right child empty |
| `deleteQ (combineQ T F)` | `some ((true,1), F)` |

Both inputs to removal have pair multiset `{(false,1),(true,1)}`. They return
the same priority but different payloads, and their residual pair multisets
are `{(true,1)}` and `{(false,1)}`. The actual `combineQ` branch `p ≤ q`
selects its first root at this tie; no mergeSort stability result is needed.
Singleton validity plus `combineQ_valid` establishes both removal hypotheses;
`combineQ_entries` and `remove_spec` connect all observations.

Under the source `Unit` specialization, the two payloads are unavailable:
only their priority occurrences remain, and both results remove one 1 from
`{1,1}`. Even for general payloads, observing only priorities yields `{1}`
for both remainders. This loss of payload information is deliberate; it
cannot justify equality of general item observations.

A useful generalized consequence to expose, without a new queue framework,
is the following **priority-only removal observation agreement**. For two
existing `ExactQueue` law packages with a common priority type, possibly
different item types, carriers, and universes, suppose both input states are
valid, their priority multisets `μ` agree, and the priority relation is
antisymmetric. Then these optional observations agree:

```text
(Q.remove q).map (fun (e,r) => (e.2, μ_Q(r)))
(Q'.remove q').map (fun (e,r) => (e.2, μ_Q'(r))).
```

This is a proposed consequence of the inspected laws, not an existing named
theorem. The proof outline uses the actual returned states throughout:

1. Split on the two actual `remove` results. `remove_none` identifies an empty
   entry list, which is equivalent to `μ = 0` because mapping preserves list
   length. Equal input multisets rule out either mixed `none`/`some` case,
   independently of validity.
2. For two successful results, apply each `remove_spec` with its own input
   validity and actual result equation. The permutation gives membership of
   the returned pair in the original entries, hence membership of its priority
   in `μ`. Transfer each such membership through equality of input `μ`.
3. Apply each minimum lower bound to the other selected priority, obtaining
   `p ≤ p'` and `p' ≤ p`. The explicit antisymmetry premise yields `p = p'`.
4. Map both exact decompositions to priorities. After substituting `p = p'`,
   equal inputs give `{p} + μ(r) = {p} + μ(r')`. The read
   `Multiset.add_right_inj` cancels the common singleton without a decidable
   equality assumption. Pair and `Option.some` congruence complete the result.

No equality of selected payloads, residual pair multisets, raw states, or
entry-list order follows. With `Unit` payloads, priority observations also
determine pair multisets.

The swapped-combine case is already a connected positive specialization of
this exact observation: both sides equal `some (1,{1})`, while its full-item
and residual-pair equality conclusions are false. A case should derive the
agreement through the proposed general theorem using `combineQ_valid` and
`combineQ_entries`, then connect one concrete returned result, rather than
merely evaluating both results independently.

The main sequential client supplies a second direct use with different
realizations: the leftist state `I` and the `exactList` state with priorities
`[1,3,1,2,2]` have the same `μ` and actual propagated validity. Both atomic
observations must equal `some (1,{1,2,2,3})`. Construct the list inputs through
`exactList.add` from `exactList.empty`; use `empty_valid` and `add_valid`, the
supplied append merge's `True` invariant and multiset law, and final singleton
`add_valid`/`add_exact`. Feed that evidence and the leftist client's evidence
to the general agreement consequence. This connection does not rely on a
tie-stability claim about `mergeSort`.

Order assumptions should stay at the claim that consumes them:

| Claim or actual implementation | Necessary information versus sufficient existing assumptions |
|---|---|
| State a least-priority observation from `remove_spec` | The law already supplies membership and every lower bound. An `IsLeast` conclusion needs only the given `LE` relation. This does not construct a lawful queue for every arbitrary relation. |
| Equality of two selected priorities from equal support | The two lower bounds plus an explicit antisymmetry premise suffice. Transitivity and totality are not additional requirements for this consequence of already supplied laws. A `PartialOrder` or source `LinearOrder` is a convenient stronger package. |
| Identify the source `Min_mset` value | Under a linear order, the finite support minimum is `Finset.min'` on a proved nonempty support. Read public routes are `min'_mem`, `min'_le`, and `isLeast_min'`; antisymmetry compares that witness with the selected priority. |
| Run `combineQ`, `insertQ`, `deleteQ`, or `listRemove` | Existing executable definitions compare priorities using `LE` and `DecidableLE`. Content permutations and emptiness laws do not need totality, transitivity, or payload equality. |
| Package `exactLeftist` or `exactList`, or use `combineQ_heap`/`combineQ_valid` | Existing public statements require `Std.IsLinearPreorder π` together with executable comparison. This is sufficient for their heap/minimum proofs and does not require antisymmetry. |

A compact boundary for antisymmetry uses two Boolean priorities with the local
indiscrete relation `p ≤ q := True`. It is decidable, reflexive, transitive,
and total, so the existing leftist realization's linear-preorder requirements
are satisfiable. Merge the valid singletons `((),false)` and `((),true)` in
either order. Both priority multisets are `{false,true}`, but actual deletion
returns respectively `false` and `true`. Both are least; they are distinct
Boolean values. The failure is priority-value agreement, not lawfulness or
existence of a minimum. This case must use a local order interpretation.

There is already cross-realization tie evidence in
[Examples/Huffman](../../conaled-ch01-cost-models/Examples/Huffman.lean):
`tied_leftist_output` and `tied_list_output` produce the distinct trees
`tiedLeft` and `tiedList`, while the subsequent `costResult_eq` application
equates their optimum costs. That is contextual reuse, not another Huffman
proof obligation for this unit. Its message matches the tiny queue case:
the specified observation can agree while tied concrete choices differ.

## 5. Keyed replacement is insufficient for exact insertion

The actual
[PrioritySearchQueue](../../conaled-ch01-cost-models/Applications/Search/PrioritySearchQueue.lean)
already provides the sharp two-element witness:

```text
add (fun x : Nat × Nat => x.1)
  [((3,10),7), ((3,20),7)] [] = [((3,10),7)].
```

This is the existing theorem `exact_same_key_tie`, proved for the actual
right-fold `add` and replacement `insert`. The second entry is processed first;
the first then replaces it at equal key and priority. The result has length 1,
whereas exact insertion must retain length 2. Hence no permutation to the
inserted batch is possible. Keyed coverage still holds: the retained item has
key 3 and priority 7, which covers both inputs; it originates in the batch;
the length bound is satisfied; key uniqueness is preserved.

Connect this witness to the actual lawful `PrioritySearchQueue.keyed` package
and its `add_covers`/`add_length` contract. `ExactQueue.keyed` supplies the
forward weakening from exact to keyed for any key under priority reflexivity.
There is no reverse implication. Existing `Examples/Huffman` also retains the
exact duplicate-insertion case of length 2 and the public `add_exact` use;
neither keyed set support nor the name "priority queue" replaces that law.

## 6. Malformed raw leftist states distinguish independent guarantees

The following tiny raw states use the same Unit/Nat notation as the main
client. They are built with `PQ.fork`, bypassing smart rank repair.

| Raw state | Invariant calculation | Actual removal and what fails |
|---|---|---|
| `C = N 9 1 E E` | Heap order holds; rankedness would require `9 = 1`, so `Valid C` is false. | `deleteQ C = some (((),1),E)`. Minimum, exact content, and residual validity all happen to hold. Invalidity alone does not imply incorrect results. |
| `H = N 1 3 (S 1) E` | Rankedness holds; heap order fails because `3 ≤ 1` is false. | `deleteQ H = some (((),3),S 1)`. Exact one-occurrence deletion and residual validity hold, but the selected priority is not a minimum. |
| `K = N 1 0 C E` | Heap order holds; rankedness fails in child `C`. | `deleteQ K = some (((),0),C)`. The selected priority is a minimum and exact deletion holds, but the residual state is invalid. |

For all three examples, raw occurrence correctness follows by the actual
root equation and `combineQ_entries` on the children. The same reasoning
shows the stronger raw deletion permutation for every successful leftist
removal, although the existing packaged `deleteQ_spec` requires `Valid` for
its combined statement. Do not silently generalize this to arbitrary
`ExactQueue` implementations: the abstract removal permutation is promised
only for valid input states.

The unconditional insertion law also remains meaningful on `C`:
`insertQ () 0 C = N 1 0 C E`, with entries priorities `[0,1]`; the result
still contains the corrupt-ranked child and is invalid. `insertQ_entries`,
or `exactLeftist.add_exact` for the singleton batch, supplies exact content
without repairing validity. Merging `C` with `E` is the identity and preserves
its occurrences, while `combineQ_valid` cannot apply to `C`.

These cases separate cached ranks, heap order, occurrence preservation, and
minimum selection. They also prevent adding a validity premise to already
unconditional `add_exact`, `remove_none`, or `combineQ_entries` consequences.

## 7. Scope, universes, and statement boundaries

`Operations` separates item universe `u`, priority universe `w`, and carrier
universe `z`. `ExactLaws` and `ExactQueue` keep those parameters. Neither
payload order, payload decidable equality, global inhabitation, nor finite
enumerability is justified for the observation bridge. The existing concrete
leftist/list realizations determine their own carrier universes; this is not
a reason to restrict the shared contract to `Type 0`. Multiset observation
and permutation transport are available without decidable equality; explicit
erasure/subtraction and conversion to a finite support `Finset` introduce it
only where used. Boolean/Nat/Unit instances make the concrete calculations decidable,
not the generic interface.

The following strongest claims must not be made:

- Set equality suffices for the book's insertion/deletion semantics, duplicate
  minima are removed all at once, or merge requires disjoint operands.
- Equality of occurrence multisets determines raw states, entry-list order,
  tied payload selection, a stable insertion order, or residual pair contents.
- Every priority multiset has a realization even when the item type is empty.
  Entry-multiset realizability and priority-multiset realizability have
  different domain boundaries.
- A linear preorder forces equality of different least priority values.
- The exact abstract removal guarantees, especially residual validity and
  minimum selection, apply to all malformed states. Conversely, malformed
  rank data necessarily corrupts contents or necessarily selects a wrong minimum.
- The weaker keyed insertion laws imply exact occurrence insertion.
- A priority obtained by projecting `deleteQ`/`listRemove` has constant-time
  access, or a sorted residual list makes removal constant-time.
- Existing rank-swapping `combineQ` implements the plain-node naive merge
  printed in Chapter 14, or this bridge covers Exercises 14.1–14.4, later
  leftist/skew/pairing algorithms, balance bounds, or cost models.
- XA01's unaccepted Set/Map/refinement work is available as an implicit import.

No mathematical inconsistency was found in the inspected book contracts or
existing queue APIs. The substantive boundaries are the empty-result extension,
validity-scoped removal law, the missing merge field in the exact interface,
and equality of priorities versus equality of tied payloads. The intended
scope can be met by thin observation/minimum/merge compatibility results over
the existing interfaces, with the connected cases above. No Lean elaboration,
compilation, proof audit, or implementation acceptance is claimed by this note.

## 8. Read-source identities

Identities use ordinary SHA-256 of file bytes. Complete reads were performed
for the following book/control and project sources; relevant snippets of
Mathlib's multiset, finite-minimum, bounds, and list-sort modules were also
read. Project guidance read includes AGENTS, domain/glossary/ADR guidance,
research skill, and example-driven skill with its worked example.

| Source | Bytes | SHA-256 |
|---|---:|---|
| `book-source/chapter14.txt` | 4,808 | `b566830b6c95d218e3fe8095914a336a35d45e0f51df8203588c02b36589fe3a` |
| `fdsa-control/research/chapter14-obligations.md` | 20,885 | `9222adc24498e1f0e8df361c1a936cc5656fce0f2b4caf7570bc0515a5e4434d` |
| `book-source/Priority_Queue_Specs.thy` | 1,654 | `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a` |
| `book-source/Heaps.thy` | 2,946 | `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe` |
| `Applications/Search/PriorityInterface.lean` | 3,992 | `8c1b6d6a08c8d0be52efe211affa7032d02b52e383e8bbdd4a4af82b22ee18a6` |
| `Applications/Search/ExactPriority.lean` | 5,912 | `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879` |
| `Applications/Search/LeftistQueue.lean` | 13,036 | `14a0d1130e04e2576dea2abb452823b5504cdbac9dbc1010f15a2f327c6bc378` |
| `Applications/Search/PrioritySearchQueue.lean` | 10,913 | `e1fce1ccb69db8f9b384584367f9a967fd9efb111a08a67554d82f230538c59f` |
| `Examples/Huffman.lean` | 8,655 | `2048293f7f37f1dd1b6ff8e3ded5c34c4a5be21d91a29fb8fa0dc382010a1a38` |

The actual consumer `Applications/Huffman/Priority.lean` was additionally
read through `insert_cached` and the start of `step_spec`. Its `insert_entries`,
`delete_size`, `two_deletions`, `step_size`, and `delete_cached` show existing
public uses of exact insertion, the actual residual validity witness, and
observation mapping. No change or additional Huffman obligation is proposed.
