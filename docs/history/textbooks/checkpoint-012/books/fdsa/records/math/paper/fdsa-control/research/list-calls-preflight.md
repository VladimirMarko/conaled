# FDSA-XB01: bounded list call-count preflight

Prepared 2026-11-02. Independent mathematical/architecture preflight only;
**not** a Standards/Spec review or acceptance result. Inspected the local
`FDSA-XB01` ticket, the pinned Appendix B.1 equations summarized in
`appendix-b-obligations.md`, existing resource helpers, and
`Examples/ListLibrary.lean` at candidate
`333f900d04be3153518e68cc8c10920f40a08e05`. No Lean edits, builds, acceptance
changes or new review loop were performed.

**Finding:** the plan matches the source. No blocking mathematical or
architectural defect was found. Two useful additional boundary examples are
an invalid lookup in a nonempty list and filtering a discarded head before
retained elements. The exact witnesses and implementation cautions follow.

## Existing primitives: exact signatures and recurrences

Names below are in `Resources.SymmetricCosts`, with `α : Type u` arbitrary.

| Existing declaration | Exact behavior and reuse |
|---|---|
| `lengthRun : List α → Nat × Nat` | `[] ↦ (0,1)`; on cons, obtain the recursive `(n,c)` and return `(n+1,c+1)`. No payload capabilities. |
| `lengthRun_exact xs` | Joint equality `lengthRun xs = (xs.length, xs.length+1)`. This is stronger than separate value and count projections; reuse it directly. |
| `splitRun : Nat → List α → (List α × List α) × Nat` | Count zero returns `(([],xs),1)`; successor count on empty returns `(([],[]),1)`; successor count on cons recurses, conses the head to the first returned list, retains the second, and adds 1. |
| `splitRun_value n xs` | `(splitRun n xs).1 = (xs.take n,xs.drop n)`. |
| `splitRun_work n xs` | `(splitRun n xs).2 = min n xs.length+1`, including zero, empty and overlarge counts. |

Append uses the already existing
`Resources.ListReversal.appendRun_nil`, `appendRun_cons` and `appendRun_exact`.
The last gives `(xs++ys,xs.length+1)`. No new append or length algorithm is
needed merely to give all the helpers one namespace.

Take/drop should be zero-charge projections of the measured split result.
`bind (splitRun n xs) (fun halves => pure halves.1)` and the corresponding
second projection express the intended observation preservation. Their
recursive equations must still be stated/proved explicitly: zero and empty
cost 1; successor/cons take adds the head and one charge; successor/cons drop
retains the recursive value and adds one charge. Do not add a `tick` around
these projection adapters.

The comparison with a fused split executes both adapters on the **same
original input**. Bind the take result as the first output component, then run
drop on the original `xs` for the second component. Running drop on the taken
prefix is a different value-level computation, even when one small example
happens to have the same total count. Separate take/drop pays both charges.

## Measured map and filter

Use independently polymorphic input/output payloads for map:
`α : Type u`, `β : Type v`, callback `α → Measured β Nat`. Filter's callback is
`α → Measured Bool Nat`. Neither operation needs `Inhabited`, `DecidableEq`,
order, or algebraic instances on payloads. Providing a Boolean callback already
provides its branch decision; only a separate Prop-predicate adapter needs
decidability.

For either operation, the cost recurrence is:

```text
empty cost = 1
cons cost = callback(head).cost + recursive(tail).cost + 1
total cost = (xs.map (fun x => (callback x).2)).sum + xs.length + 1
```

These equalities need no condition about retained elements or distinctness.
Every original occurrence pays its callback cost. The filter's actual returned
Boolean chooses whether to prepend the original element, and **both** branches
still use the recursive filtered tail. Bind the callback and recursive result
once in the measured expression; add exactly one entry charge around the cons
body. Empty input has one entry charge and no callback invocation. No extra
charge belongs to list construction, `pure`, projection, or the Boolean test.

Erasure should first give `List.map (fun x => (f x).1)` and
`List.filter (fun x => (p x).1)` directly. A caller can then rewrite a separately
proved callback-value contract to its independent intended function/predicate.
Do not replace an arbitrary callback's output with a presumed value merely
because its cost follows the expected formula.

The ticket's calculations are correct: costs `[2,2,3]` sum to 7, with 4 list
entries, hence 11; zero-cost callbacks on length three give 4; unit costs give
7. Knapsack's `sourceMapRun` instead has `headCost+tailCost+2`; retain that
existing model unchanged. Output equality with Knapsack's map is insufficient
for exact count reuse.

**Suggested connected filter case:** callback
`fun x : Nat => (decide (x≤2),x)` on `[3,2,2]` returns `([2,2],11)`.
This checks a discarded head followed by kept values. The ticket's `[2,2,3]`
case discards only the final occurrence and should not be its only mixed-branch
witness. This is a concrete contract example, not a request for a larger test
suite.

## Optional sequential lookup

Retain the actual list traversal:

```text
lookup [] k       = chosen explicit failure result/count
lookup (x::xs) 0  = (some x,1)
lookup (x::xs) (k+1) = recursive lookup xs k, with one added charge
```

The standard erasure witnesses are `List.getElem?_nil`,
`getElem?_cons_zero` and `getElem?_cons_succ`; the valid-domain bridge is
`List.getElem?_eq_getElem`. For `k<xs.length`, the source count is exactly
`k+1`, independently of the chosen invalid-input extension, because valid
execution stops at a nonempty zero-index clause.

If the extension chooses `lookup [] k=(none,1)`, its total count is
`min k xs.length+1`. This is a new, explicitly totalized model result;
the book supplies no empty-input nth equation. Last valid index in a nonempty
list costs its length; the first invalid index costs length plus one, and later
invalid indices saturate at that count. Do not use `min (k+1) xs.length`, which
loses the failing empty call.

**Suggested boundary pair:** position 2 in `[4,4,9]` returns `(some 9,3)`, while
position 3 returns `(none,4)` under that extension. The arbitrary-payload empty
case, including `List Empty`, needs no default value. Record both the valid
source theorem and the invalid extension convention separately.

## Minimal dependency direction

A source-level starting point for the new measured-helper module is direct
imports of `Applications.Resources.CallCount` and
`Applications.Resources.SymmetricCosts`. They provide the existing measured
vocabulary and split reuse; the latter already reaches standard List lemmas
through `Sequences.Symmetric.Core` and `SquareKit.ListFusion`. Ordinary list
map/filter/sum recurrences and natural arithmetic suffice for these proofs;
sorting, selection, minimum, interval, real-analysis and logarithm imports are
not required by these statements. Append clients can import `ListReversal`
where they actually use its witnesses.

This is dependency advice, not a claim that a minimal import set was compiled.
Add a direct standard-list theorem import only if elaboration exposes a real
missing declaration. A broad `Mathlib` import, duplicate measured framework, or
extraction/refactoring of the existing symmetric-list primitives is not needed
for this bounded work. Keep checked clients in Examples importing the public
Applications interfaces.

## Appendix A candidate correspondence

No source-correspondence defect was found in `Examples.ListLibrary` at the
stated candidate. Its range equations preserve inclusive/exclusive endpoints;
the drop-last condition tests list shape without payload equality; optional
head/index and proof-domain bridges preserve valid results; out-of-range update
is explicitly unchanged; repeated-value updates distinguish positions.

Minimum's associative right-recursive law, weaker valid-result bridge,
linear-order leastness client, and empty-domain `Min` example have the right
separate assumptions. Sum's literal equations correctly need only `Add` and
`Zero`. `Pairwise` is retained for arbitrary relations, with a meaningful
counterexample to replacing it by adjacent `IsChain`. The accompanying source
map explicitly distinguishes propositional observations from executable Bool
views and explicitly excludes execution-cost claims for these value equations.

No change to this candidate's value-level examples is required by the
preflight. Root retains implementation choices, final candidate identity,
coordinated reviews and all acceptance gates.
