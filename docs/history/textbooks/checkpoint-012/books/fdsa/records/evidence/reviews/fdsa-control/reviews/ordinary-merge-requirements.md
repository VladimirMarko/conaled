# Frozen requirements — FDSA-XM01 ordinary-list merge observations

Frozen before source authoring on 2026-11-02. This is one bounded shared
component under the user's cross-cutting exception. Chapter 1 remains active;
no chapter, appendix or shared unit is accepted. The whole-book request in
`../REQUEST.md`, all original chapter inventories, and all retained scope
corrections remain in force.

## 1. Original base, source evidence and fixed boundary

- Original review base and intended immediate parent:
  `07e480f6ec9958d4975bb90151005b84f2907614`.
- Clean isolated checkout: `conaled-ordinary-merge`; branch:
  `work/fdsa-ordinary-merge`.
- `ordinary-merge-clean-start.json` records the actual clean HEAD/status,
  untouched main checkout, original source/pin/checker identities, absent new
  paths and dependency-package symlink. No project build directory exists.
- Root read all three complete stopped preflights. Their exact identities and
  the preserved bounded documentation correction are recorded in
  `ordinary-merge-preflight-identities.json`.
- Source report: 23346 bytes / 319 lines, SHA-256
  `42552545b9b6e2a1836ef12288c41a655dd5c44e34885c285cd4f191da167a69`.
- API report: 28099 bytes / 243 lines, SHA-256
  `7f4c38df7a2cba111f24a3b7fa684e04922ca0ef7327e3e33ee05a39fb2e5f26`.
- Corrected case report: 24208 bytes / 469 lines, SHA-256
  `5df99d21ef97da7eb0ddc4cb21f80a21653dc07406f8eda6369ab1f307418e92`.
  Its original 24170-byte/c87170cc snapshot is retained. XM01-PRE-DOC01 only
  clarifies that the initial C2 prefix still awaits combined validation/review
  and fixes punctuation; all numerical expectations and mathematics remain.

Primary evidence is the July 27, 2026 FDSA PDF, printed pp.17–18 and chosen
exercise reuse on pp.180–181. PDF SHA-256:
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The corresponding Isabelle `Sorting.thy` is pinned at
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, SHA-256
`dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.
That companion revision postdates the manuscript and is not represented as
its generation revision. The source preflight supplies exact positions,
other source hashes and the applicable license notice.

The component directly supports only C02-025, the merge portion of C02-027,
C02-028/029/031/033/035/037. Keyed stability is a reusable ingredient, not
completion of C02-107. Chapter 14 reuse concerns chosen solutions of Exercises
14.1/14.3, with their full concrete implementations and costs still queued.
The complete historical 107-row C2 requirements and current 112-row inventory,
including C02-108–112, remain unchanged and mandatory.

The ordinary operation consumes exactly one head at each nonterminal step.
Binomial forest merge's equal-rank link/carry is a different operation and
tariff; no correspondence to it is claimed. No second pure merge hierarchy,
general merge framework, source translator or whole-sort/tree algorithm is
part of this scope.

## 2. Exactly six source paths

| Path | Responsibility |
| --- | --- |
| `Applications/Sorting/Merge.lean` | Add the two input-sublist laws and their arbitrary-relation converse/input-local keyed iff. Preserve every existing definition, theorem statement, assumption and proof. |
| `Applications/Resources/ListMerge.lean` | One branch-sensitive dual-Nat measured merge, exact projection equations, erasure, entry relation, bounds and exact input-local map transport. |
| `Examples/MergeCosts.lean` | Connected general and concrete uses, including real bind/reweight, source/key adapters, positive/zero tariff boundary and the actual raw queue node body. |
| `SquareApplications.lean` | Add one public import of `Examples.MergeCosts`; preserve all existing imports. |
| `docs/research/fdsa-list-merge.md` | Source/license note, declared observations, public-claim correspondence, statement assessment and honest remaining scope/status. |
| `docs/research/fdsa-reconstruction-map.md` | Append the source/public-claim map and explicit downstream limits; preserve the original complete content. |

Keep `SourceMerge`, `Stable`, `Sort`, `Measured`, `CallCount`, `CallComparison`,
`LeftistQueue`, all existing examples and all tooling/pins unchanged. No XH01,
tree, insertion, probability, builder or other unaccepted shared branch is a
source dependency. The resource core imports the existing sorting/source and
call-count/measurement APIs; queue and cost-comparison clients belong only in
the examples. No new verification root, warning relaxation or environment
configuration is authorized.

## 3. Small additive value layer

In namespace `Applications.Sorting`, expose the following intended names and
contracts for arbitrary `α : Type u` and `cmp : α → α → Bool`:

1. `sublist_merge_left cmp xs ys`: `xs <+ List.merge xs ys cmp`.
2. `sublist_merge_right cmp xs ys`: `ys <+ List.merge xs ys cmp`.
3. `pairwise_of_merge`: for an arbitrary independent relation `R`,
   `(List.merge xs ys cmp).Pairwise R → xs.Pairwise R ∧ ys.Pairwise R`.
4. `merge_sorted_compatible_on_iff`: combine the converse with the existing
   `merge_sorted_compatible_on` forward direction to obtain
   `KeySorted key (List.merge xs ys cmp) ↔ KeySorted key xs ∧ KeySorted key ys`.
   Retain exactly the existing key preorder and input-local comparator
   compatibility premise; require no payload order or equality.

The first three claims need no order, decidable relation, comparator law,
distinctness, inhabitant or finiteness assumption. Use the actual recurrence
for the sublists and existing `List.Pairwise.sublist` for the converse. At this
pin the nondeprecated constructors are `Sublist.cons_cons` and `Sublist.cons`.
Do not replace ordered occurrences with a set or permutation argument.

A separate keyed-iff library wrapper is unnecessary. The examples must
instantiate the generic iff at the actual source/key comparator and connect
the existing source adapter. Preserve weaker forward input-local hypotheses;
do not impose a global linear order on the arbitrary-comparator interface.

## 4. One actual measured execution and exact observations

Use namespace `Resources.ListMerge` and the existing
`Measured (List α) (Nat × Nat)`. The public operation is `run`, with costs
ordered **(head comparisons, recursive merge invocations)**. It accepts an
explicit arbitrary Boolean comparator, independently of every typeclass.

The actual recurrence must be extensionally:

```text
run cmp [] ys = (ys, (0,1))
run cmp xs [] = (xs, (0,1))
run cmp (x::xs) (y::ys) =
  if cmp x y then
    Resources.bind (run cmp xs (y::ys)) (fun zs => (x::zs, (1,1)))
  else
    Resources.bind (run cmp (x::xs) ys) (fun zs => (y::zs, (1,1))).
```

One recursive branch runs, and the output cons uses that branch's actual
returned list. Termination is by the sum of input lengths. The two-empty case
is one invocation. Observation addition may equivalently put the same Nat
charge before the child; no event-order trace is claimed. Do not construct an
unrelated pure result and attach an independently chosen counter.

Expose `comparisons cmp xs ys := (run cmp xs ys).2.1` and
`entries cmp xs ys := (run cmp xs ys).2.2`, or equivalently transparent
abbreviations with these exact meanings. One execution suffices; no independent
recursive scalar executors or extra tariff/trace carrier is needed.

Required public facts, with names agreed before authoring:

- The two whole-pair base equations and the actual selected-branch equation.
- `run_value`: `(run cmp xs ys).1 = List.merge xs ys cmp` for all inputs.
- Exact comparison equations: either empty side gives zero; two nonempty sides
  give `1 +` the comparison observation of the selected recursive arguments.
  These equations are the source handwritten `C_merge` correspondence. A
  second analytical recursion is unnecessary and must not replace this link.
- Exact entry equations: either empty side gives one; a nonterminal step gives
  `1 +` the selected child's entry observation. Include the scalar `reweight
  Prod.snd` recurrence as `CallCount.tick` of the actual selected child and an
  uncharged cons, reusing the existing entry convention.
- `entries_eq_comparisons_add_one`: `entries = comparisons + 1` on all inputs.
- `comparisons_le`: `comparisons cmp xs ys ≤ xs.length + ys.length`.
- `entries_le`: `entries cmp xs ys ≤ xs.length + ys.length + 1`.
- A usable both-nonempty positivity fact, e.g. `comparisons_cons_pos`, so that
  the actual positive-cost C1 application needs no invented premise.

No sortedness, comparison law, decidable payload equality, finite carrier or
inhabitant belongs to these declarations. These are deliberately loose bounds,
not tight worst-case formulas. Comparisons count invocations of the supplied
comparator, not its internal evaluation work. The comparison projection adds
no charge for function entries, cons, lengths, untouched suffix traversal,
keys or external preparation. The entry projection counts this logical merge's
calls, not every Lean helper or the tail-recursive compiled implementation.

Source and key clients must compose `run_value` with existing
`sourceMerge_eq_merge`/`mergeBy_source`. Source specialization needs only the
actual operation's `LE` and `DecidableLE`; sortedness/stability assumptions are
supplied only when those properties are claimed. Use existing length, membership
and permutation-to-multiset laws after erasure rather than a parallel value
theory in the resource module.

## 5. Exact map/key transport with a connected use

Include one public `run_map` theorem for independent universes `α : Type u`,
`β : Type v`, any `f : α → β`, the two Boolean comparators, and input-local
agreement

```text
∀ a ∈ xs, ∀ b ∈ ys, cmp a b = cmp' (f a) (f b).
```

Its full conclusion is

```text
run cmp' (xs.map f) (ys.map f)
  = ((run cmp xs ys).1.map f, (run cmp xs ys).2).
```

The same actual branches establish values and both counts; pinned
`List.map_merge` alone establishes only values. Require no injectivity,
payload equality, order or same-universe restriction. The tagged-to-key
consumer below must use this theorem, including duplicate keys/noninjective
erasure. This is an equality between declared executions, not a claim that
performing `List.map` in a caller has no runtime or separately modeled work.
No general map framework or additional container is required.

## 6. Required connected applications and independent expectations

The complete three preflights retain the independent calculations. Use the
following compact families; optional numerical alternatives in those reports
need not all be implemented. Expected observations below are `(comparisons,
entries)`. A concrete equality may end by reduction after applying the public
operation/theorem; an unrelated literal calculation alone is insufficient.

### Raw and source families

- Generic empty-side equations, including arbitrary `xs ys : List Empty`,
  return the remaining list with `(0,1)`. Do not supply an inhabitant.
- Natural `≤`: `[0]` with `[1,2]` returns `[0,1,2]`, `(1,2)`; `[2]` with
  `[0,1]` returns the same list, `(2,3)`.
- Natural `≤`: `[0,2,2]` with `[1,2,3]` returns `[0,1,2,2,2,3]`, `(4,5)`.
  Connect length, occurrence/multiset preservation and support through actual
  erasure and existing merge laws; retain all three occurrences of 2.
- For arbitrary `α : Type u` and `a b c : α`, always-true merge of `[a,b]`
  with `[c]` returns `[a,b,c]`, `(2,3)`; always-false returns `[c,a,b]`, `(1,2)`.
- `[1,1]` with `[1]` under the same natural `≤` comparator gives `(2,3)`;
  swapped operands give `(1,2)`, although both return `[1,1,1]`. Connect this
  as a failure of inferring count equality from value/length/content equality.
- `[3,1]` with `[2,1]` under `≤` returns `[2,1,3,1]`, `(2,3)`; apply the
  generic cost bound without sorting assumptions. Consume both public sublist
  facts. For **every** Boolean comparator, its merge is not natural-order
  pairwise-sorted, using the left sublist/converse, not just literal evaluation.

### Source order, keyed stability and map use

- Give a general source/key sortedness iff application of the new value
  layer, with the exact existing order premises and source adapter. The
  output-to-input direction remains the arbitrary-relation public result.
- Reuse the existing signed-record `Examples.StableSorting.expected` and
  `expected_spec`: merge `[(2,"first")]` with
  `[(-1,"negative"),(2,"last")]` by the first key. The actual result is
  `[(-1,"negative"),(2,"first"),(2,"last")]`, `(2,3)`. Connect new erasure
  and counts with existing `mergeBy_spec`/filter/stability (and uniqueness
  where useful), establishing the actual sorted-block hypotheses.
- For arbitrary `β : Type u` and `a b c : β`, merge
  `[(1,a),(1,b)]` with `[(1,c)] : List (Nat × β)`. The result retains
  left records first and costs `(2,3)`; the swapped version costs `(1,2)`.
  Use `run_map` with `Prod.fst` to connect these actual tagged executions to
  the unlabelled key executions, preserving counts without payload equality,
  ordering or injectivity. Retain independent value/key universes.
- On distinct concrete tags with all keys one, always-false comparison is
  compatible with sortedness and preserves occurrences but takes right tags
  first. Show the actual merge violates the existing stable-filter contract.
- With tagged unsorted inputs `[(3,"A"),(1,"B")]` and
  `[(2,"C"),(1,"D")]`, actual key merge returns the right pair followed by
  the left pair, `(2,3)`. Its key-1 filter order differs from concatenation.
  This preserves the substantive sorted-input premise of `mergeBy_filter`.

### Actual two-stage bind and projection

Use `Resources.bind (run cmp xs ys) (fun first => run cmp zs first)` directly,
with the second merge receiving the first execution's actual returned list.
Give a general erasure/observation application showing total entries are total
comparisons plus **two**, and the derived bounds

```text
Ctotal ≤ 2 * (xs.length + ys.length) + zs.length
Etotal ≤ 2 * (xs.length + ys.length) + zs.length + 2.
```

Consume the existing additive coordinate homomorphisms and `reweight_bind`
for scalar projections of this actual sequencing. The affine single-merge
shift `C ↦ C+1` is not an additive homomorphism.

The concrete discriminator is `[2]` with `[0]` → `[0,2]`, `(1,2)`, then
`[1]` with that actual result → `[0,1,2]`, `(2,3)`. Total: `([0,1,2],(3,5))`.
The erroneous continuation fed concatenation `[2,0]` instead gives
`([1,2,0],(2,4))`; retain this boundary as a checked unequal observation/value
or equivalent explicit actual-input dependency witness. No enclosing wrapper
entry is silently charged.

### Actual queue node body, without whole-enumeration costs

For arbitrary payload/priority universes, `[LE π] [DecidableLE π]`, raw rank
`k`, entry `(x,p)` and raw subtrees `l,r`, measure the ordinary priority merge
of actual values `toListQ l` and `toListQ r`, then an uncharged cons `(x,p)`
using existing `bind`/`pure`. Prove that body's value is the existing
`toListQ (PQ.fork k x p l r)`. No `Heap` or `Ranked` hypothesis is allowed on
this raw value law. Its two costs equal that single merge's observations.
Use `toListQ_perm.length_eq` and `entries_length` to give merge-only bounds
`C ≤ size l + size r`, `E ≤ size l + size r + 1`.

Retain the actual fixture: raw leaves `PQ.fork 0 () 1 null null` and
`PQ.fork 0 () 2 null null`, beneath raw root `PQ.fork 99 () 9 l r`.
The body returns `[((),9),((),1),((),2)]` with merge-only observation `(1,2)`.
The result is unsorted; do not apply heap-dependent sortedness. A separate
rank-counterexample theorem is unnecessary. Child enumerations, their actual
recursive sequencing, the enclosing tree entry, the ordinary-tree/carrier
bridge and the full quadratic bound remain outside this local observation.

### Qualified C1 cost comparison, on the actual executions

Both nonempty inputs give positive C, hence `C ≤ E ≤ 2*C` by the new exact
relation and existing `CallCount.cost_le_add_entry` / `add_entry_le`.
The singleton-winning case attains `C=1,E=2`. For an empty-side execution,
`C=0,E=1` refutes `E ≤ K*C` for every Nat K via existing
`CallCount.zero_cost_entry_matters`. Import `CallComparison` only in the
examples for these real uses. No new asymptotic/resource framework is needed.

## 7. Source documentation and preserved later work

The note must distinguish prescribed C2 merge/comparison equations from the
separate invocation interpretation and chosen C14 exercise implementations.
Retain exact primary source/version/hash references and the complete applicable
Isabelle BSD-3-Clause attribution, conditions and disclaimer. Existing Lean
and Mathlib definitions are imported under their pinned provenance; do not
copy the book manuscript or claim its companion revision is a build identity.

Map public statements to the limited source rows, describe actual connected
cases and all domain/ordering/count qualifications, and state compilation and
final-review limits honestly. Source-only author assessment closes no gate.

All top-down floor-left recursion, termination, actual sorted-child cost
composition, all-length/real-log and printed power-of-two theorems, bottom-up
and natural sorting, scanner/builder work, exercises and stability obligations
remain mandatory in Chapter 2. Standard ceil-left sort value equality gives
no cost transfer. All concrete sorted-list queue laws/direct costs, full heap
enumeration/carrier correspondence/quadratic theorem, other C14 exercises and
later binomial carry/invariant/amortized work remain mandatory. No deferred
scope disappears because this component is reusable.

## 8. Release, validation, integration and recovery

Before source release, root must preserve this full frozen scope, three stopped
preflights and their readback, original/clean starting-state identities and all
local tracking in checkpoint **0052**, expose it and save it successfully.
All authors remain stopped until root communicates that concrete receipt.
Each author then writes only its assigned source path. The Chapter 1 attempt-2
gate remains the sole validation run; no XM01 compiler/checker/project hash
helper or project build-cache modification is authorized during it.

Root must review the statements, actual definitions, assumptions and public
connections of all complete files, preserve findings/corrections and stop all
writers before source capture. Commit all non-main worktree edits locally,
then create/expose/save the complete draft checkpoint with all control history.
No GitHub mutation, push or remote ticket update is authorized.

Accepted repaired Chapter 1 is a prerequisite to XM01 integration/acceptance.
The initial Chapter 2 prefix stays exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; XM01 is not added to that first
candidate. The original `shared-integration-preflight.md` remains unchanged:
its section 7 already permits reuse of the idle isolated normal-cache checkout
for successive immutable candidates, with every prior result preserved.
After the initial prefix's own gates, XM01 can be reconciled when its merge
consumer is needed. Record any incorporated base and full conflict resolution,
preserving this original base/scope and all accepted predecessor changes.

Required acceptance evidence remains matching applicable focused checks,
clean immutable-candidate full `./check.sh --candidate HEAD`, both integrity
passes, source/public coverage and pinned compiler/dependency checks, complete
integrated build and exhaustive transitive axiom audit, both independent
Standards and Spec axes on the full scope, and immediate
`./check.sh --verify-candidate HEAD`. Fresh mode remains governed by concrete
README/runbook triggers. No focused success, cache reuse, branch ancestry,
preflight or draft checkpoint substitutes for those gates. Preserve all failed
and superseded attempts with their honest identities and outcomes.
