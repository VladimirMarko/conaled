# Ordinary list merge: bounded API and architecture preflight

Prepared 2026-11-02 for proposed FDSA-XM01. **Read-only source/API preparation, not frozen scope, implementation, compilation, final review, chapter activation or acceptance.** The sole new artifact is this report. The unchanged Chapter 1 attempt-2 gate remains the coordinator's only compiler/checker. The original initial Chapter 2 integration prefix `c80eec92f5458eccfd1c34c8314d666c2a1e3847` and all prior requirements remain unchanged.

## 1. Recommendation

A small shared unit is justified. Keep ordinary `List.merge` as the value operation, add its two missing input-sublist observations to the existing `Applications/Sorting/Merge.lean`, and use one new branch-sensitive execution returning `Resources.Measured (List α) (Nat × Nat)`. The observation components are **element comparisons** and **recursive merge invocations**. Empty-side calls return `(0,1)`; a nonempty comparison chooses exactly one recursive call and adds `(1,1)` to that call's observation. This fits the existing pair, `bind`, projection homomorphisms and `reweight` APIs without a new carrier, syntax, executor framework or observation hierarchy.

The proposed resource operation must construct its output from the actual recursive result. Prove value erasure, the two exact recurrences, `entries = comparisons + 1`, and the source length bounds from those branches. Defining an execution by pairing an unrelated `List.merge` call with a separate count would omit that connection. A separate analytical counter is unnecessary: the first projection can be the source counter with proved equations. If a separately named recursive source counter is retained for correspondence, it needs an explicit branch-by-branch equality to that first projection.

This supports Chapter 2's prescribed ordinary merge and local components of chosen Chapter 14 exercise solutions. It does not supply the complete sorter, sorted-list queue, heap enumeration or their whole-program costs. Binomial forest merge is a different operation. No dependency on another unaccepted shared branch, XH01, or a new tree unit is needed; all reusable code inspected here is in the coordinator-designated repaired Chapter 1 checkout at `07e480f6ec9958d4975bb90151005b84f2907614`.

## 2. Reading scope and evidence

All local paths in this report are relative to `/workspace/scratch/845aa1048b05`, unless explicitly described as paths inside a checkout. Actual project source was read in `conaled-ch01-cost-models`. No Git command was used to re-establish its identity; the base above is the coordinator's recorded identity. This report describes actual inspected source, not a newly validated build.

The complete governing `AGENTS.md`, architectural-quality/domain guidance, glossary, ADR index and relevant ADRs 0001/0010 were read. Their separation of operations, observations and laws is satisfied by reusing existing lists, measured pairs and composition, with a bounded additive value extension. This task does not change a preservation family, interpretation interface or global universe policy.

Pinned primary sources used:

| Source | Exact revision / local location |
| --- | --- |
| Lean list definitions and laws | Lean 4.35.0, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; retained `book-source/LeanListSort-Basic.lean`, `LeanListSort-Lemmas.lean`, `LeanList-Basic.lean`, `LeanList-Pairwise.lean`. Original paths are `src/Init/Data/List/Sort/{Basic,Lemmas}.lean` and the corresponding `Init/Data/List` files. |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; `conaled-ch01-cost-models/.lake/packages/mathlib/Mathlib/Data/List/Sort.lean` and `Mathlib/Algebra/Group/Prod.lean`. |
| Batteries search boundary | `66e469188fe07963e5cf666c7d4433f45b8131c5`; the pinned list modules were searched for existing ordinary merge/sublist support. No Batteries operation is needed by the recommendation. |
| Isabelle ordinary merge and comparison counter | `book-source/Sorting.thy`, revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, original `src/HOL/Data_Structures/Sorting.thy`: merge at 79–82; handwritten `C_merge` and bound at 148–156. This revision postdates the July 27, 2026 manuscript and is not asserted to be its generation revision. |
| FDSA scope and source correspondence | Existing `fdsa-control/research/chapter02-obligations.md` plus the completed `fdsa-control/research/ordinary-merge-source-preflight.md`. The source report preserves exact source hashes, licensing, prescribed-versus-chosen exercise scope and all downstream obligations. The current chapter inventory has 112 rows, not merely the frozen original 107-row snapshot. |

The source report was read completely before this handoff: 23,346 bytes, 319 lines, SHA-256 `42552545b9b6e2a1836ef12288c41a655dd5c44e34885c285cd4f191da167a69`. Its comparison/invocation and source-domain qualifications agree with this API assessment. No manuscript material is being copied into repository deliverables.

## 3. Existing value APIs: retain their actual assumptions

Paths in this section are inside `conaled-ch01-cost-models`.

### 3.1 Ordinary and keyed merge

`Applications/Sorting/Merge.lean` imports `Applications.Sorting.Stable`; its namespace is `Applications.Sorting` and it has independent payload/key universes.

| Existing declaration | Actual contract and hypotheses |
| --- | --- |
| `mergeBy [LE κ] [DecidableLE κ] (key : α → κ) (xs ys : List α)` | Abbreviation for `List.merge xs ys (fun x y => decide (key x ≤ key y))`. No payload order, equality or inhabitant. |
| `mergeBy_perm key xs ys` | The output is a permutation of `xs ++ ys`, with only the preceding operation assumptions. |
| `merge_sorted_compatible_on [LE κ] [Std.IsPreorder κ] key cmp xs ys hc hx hy` | Forward key-sortedness. `hc` quantifies only over `a ∈ xs`, `b ∈ ys` and requires both `(cmp a b = true → key a ≤ key b)` and `(cmp a b = false → key b ≤ key a)`. `hx` and `hy` are the two input `KeySorted` proofs. |
| `merge_sorted_compatible` | Same conclusion with a stronger global comparator-compatibility premise; use the input-local theorem where possible. |
| `mergeBy_sorted [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] key xs ys hx hy` | Convenient forward sortedness for the actual key comparator. No antisymmetry is required. |
| `mergeBy_filter` and `mergeBy_stable` | Exact left-before-right equal-key observation on two **sorted** blocks. Require `[LE κ] [DecidableLE κ] [Std.IsPreorder κ] [DecidableEq κ]`; key equality decides the filter, not payload equality. |
| `mergeBy_spec` | Packages sortedness, permutation and stability as `StableSort key (xs ++ ys) (mergeBy key xs ys)`, under the linear-preorder operation assumptions plus `DecidableEq κ` and sorted input blocks. |

`Applications/Sorting/Stable.lean` defines `KeySorted key xs` as `xs.Pairwise (fun a b => key a ≤ key b)`, and `Stable` by equality of equal-key filters. The comparator laws needed for sortedness do not force stable tie handling. An arbitrary compatible comparator can choose the right equal-key record first. The exact source comparator chooses the left head on equality; existing stability proofs should be reused for that specialization.

`Applications/Sorting/SourceMerge.lean` contains the literal source recurrence, with `[LE α] [DecidableLE α]`, and `termination_by xs ys => xs.length + ys.length`. Its public bridge is:

```lean
sourceMerge_eq_merge (xs ys : List α) :
  sourceMerge xs ys = List.merge xs ys (fun x y => decide (x ≤ y))
```

`mergeBy_source key xs ys` recovers this source by locally pulling back key order to records; it does not require an existing order on the record type. These are value correspondences. They do not presently prove a count equality. The new resource value theorem can compose with them without changing their definitions or proofs.

### 3.2 Exact pinned standard names

The explicit comparator makes `List.merge xs ys cmp` available for arbitrary `α : Type u` with no typeclass requirement. The pinned verification recurrence is the two empty-side cases followed by `if cmp x y then x :: ... else y :: ...` (`LeanListSort-Basic.lean:39–47`). `[]/[]` matches one base invocation.

Relevant exact declarations in the saved Lean sources:

| Declaration | Useful statement / location |
| --- | --- |
| `List.nil_merge ys` | `List.merge [] ys cmp = ys`, Basic:49. |
| `List.merge_right xs` | `List.merge xs [] cmp = xs`, Basic:50. The actual name is `merge_right`, not `merge_nil`. |
| `List.cons_merge_cons cmp x y xs ys` | The selected-head equation, Lemmas:149. `cons_merge_cons_pos`/`cons_merge_cons_neg` also exist. |
| `List.length_merge cmp xs ys` | Output length is `xs.length + ys.length`, Lemmas:161. No order laws. |
| `List.mem_merge` | `a ∈ List.merge xs ys cmp ↔ a ∈ xs ∨ a ∈ ys`, Lemmas:176. |
| `List.merge_perm_append cmp` | `List.merge xs ys cmp ~ xs ++ ys`, Lemmas:260. No order or equality premise. |
| `List.pairwise_merge trans total xs ys hx hy` | Forward sortedness for the Boolean comparator itself; transitivity and totality are explicit, Lemmas:218. The local project theorem above is preferable for a distinct key relation and input-local compatibility. |
| `List.map_merge hl` | For `f : α → β`, `r : α → α → Bool`, `s : β → β → Bool`, and `hl : ∀ a ∈ l, ∀ b ∈ l', r a b = s (f a) (f b)`, proves `(l.merge l' r).map f = (l.map f).merge (l'.map f) s`, Lemmas:496–513. Neither injectivity nor equal universes is required. |

The full relevant merge section, local merge modules and scoped Lean/Mathlib/Batteries list searches exposed no existing theorem that **each input is a sublist of one ordinary merge**. This is a scoped absence finding, not a claim to have searched every theorem in the dependency graph. `List.sublist_mergeSort` and `pair_sublist_mergeSort` concern a whole sort; they cannot replace the two input-sublist facts.

### 3.3 Small additive value layer

The following are **proposed statements/names**, not existing declarations or frozen requirements:

```lean
sublist_merge_left (cmp : α → α → Bool) (xs ys : List α) :
  xs <+ List.merge xs ys cmp
sublist_merge_right (cmp : α → α → Bool) (xs ys : List α) :
  ys <+ List.merge xs ys cmp
```

The proof follows the actual merge recurrence with the same sum-of-lengths decrease. If the left head is emitted, use `List.Sublist.cons_cons x` on the left induction result and `List.Sublist.cons x` on the right result. Exchange the roles when the right head is emitted. The empty cases use reflexivity and the empty sublist fact. At this pin `Sublist.cons₂` is deprecated; use `cons_cons` (`LeanList-Basic.lean:1089–1100`).

For any independent relation `R : α → α → Prop`, the source converse is then immediately available:

```lean
(List.merge xs ys cmp).Pairwise R → xs.Pairwise R ∧ ys.Pairwise R
```

The existing theorem is exactly `List.Pairwise.sublist : l₁ <+ l₂ → l₂.Pairwise R → l₁.Pairwise R` (`LeanList-Pairwise.lean:47`). It needs no reflexivity, transitivity, comparator compatibility, decidable relation or payload equality. Preserve that weaker direction rather than deriving it from a globally ordered specialization.

A small semantic iff can combine this converse with `merge_sorted_compatible_on` under its existing input-local hypotheses. Its keyed source specialization follows from `mergeBy_sorted`. No duplicated sortedness induction, second source merge operation, new pairwise theory or whole-sort wrapper is justified. Whether the generic converse and keyed iff receive public names or are short clients can be fixed later; the two sublist observations are the actual reusable missing facts.

## 4. Existing observation and composition APIs

`Applications/Resources/Measured.lean` imports `Mathlib.Algebra.Group.Prod` and defines these ordinary operations with independent value/observation universes:

```lean
Measured (α : Type u) (C : Type v) := α × C
Resources.pure [Zero C] (a : α) : Measured α C
Resources.bind [Add C] (r : Measured α C)
  (f : α → Measured β C) : Measured β C
Resources.reweight (h : C → D) (r : Measured α C) : Measured α D
```

`bind` uses the actual first result as the second input and adds observations in sequence: `(s.1, r.2 + s.2)` for `s = f r.1`. Existing `bind_value`, `bind_erases`, `bind_assoc`, `reweight_value` and

```lean
reweight_bind [AddMonoid C] [AddMonoid D]
  (h : C →+ D) (r : Measured α C) (f : α → Measured β C) :
  reweight h (bind r f) =
    bind (reweight h r) (fun x => reweight h (f x))
```

already express the required value and observation composition. No new square, monad instance or executor is required.

The pinned projection homomorphisms are `AddMonoidHom.fst Nat Nat` and `AddMonoidHom.snd Nat Nat`. They are generated by `@[to_additive]` from `MonoidHom.fst`/`snd` in `Mathlib/Algebra/Group/Prod.lean:323–341`; the additive definitions take `[AddZeroClass A] [AddZeroClass B]`. The concrete Nat instances already satisfy `reweight_bind`'s stronger additive-monoid hypotheses.

There is an exact local precedent: `Resources.Thinning.thinMeasured` records a pair of natural observations in one execution (`Applications/Resources/Thinning.lean:111–176`), and `Examples.Resources.composed_thinning` applies the projection homomorphism to actual sequential executions (`Examples/Resources.lean:25–39`). Reuse this interface, not its separate scalar algorithms: XM01 does not need several independent recursive merge executors.

`Resources.CallCount.tick` is Nat-specific and adds one after the body; `tick_value`/`tick_cost`, `primitive_rule`, `let_rule` and `if_rule` are already available from `Applications/Resources/CallCount.lean`. The invocation projection of a nonempty step should agree with a `tick` around the actual selected recursive invocation and uncharged cons. There is no need to generalize `tick` to a product or charge every Lean helper call. Qualify `Resources.bind`/`Resources.pure` in proof scripts where generic monadic names could be ambiguous; this is source guidance, not a prediction of a compiler failure.

## 5. Proposed measured operation and exact proof route

Use namespace `Resources.ListMerge` in proposed `Applications/Resources/ListMerge.lean`. A compact operation name such as `run` is sufficient. The following is a **design sketch**, not new Lean source or a frozen public API:

```text
run cmp [] ys = (ys, (0,1))
run cmp xs [] = (xs, (0,1))
run cmp (x::xs) (y::ys) =
  if cmp x y then
    bind (run cmp xs (y::ys)) (fun zs => (x::zs, (1,1)))
  else
    bind (run cmp (x::xs) ys) (fun zs => (y::zs, (1,1))).
```

The actual Boolean comparison controls the actual recursive call; only that call runs. The first output component is constructed from its returned list. Termination uses the strictly decreasing input-length sum, including unsorted inputs, duplicate elements and arbitrary Boolean comparators. It needs no typeclass on `α : Type u`. Counting charges after the selected recursive result agrees arithmetically with the source `1 + C_child`; these observations are commutative natural counts, not an event-order trace.

Let `C cmp xs ys = (run cmp xs ys).2.1` and `E cmp xs ys = (run cmp xs ys).2.2` for the following statements. These are explanatory abbreviations; public scalar definitions are optional.

| Intended statement | Concrete proof route and boundary |
| --- | --- |
| `(run cmp xs ys).1 = List.merge xs ys cmp` | Functional or length-sum induction; split the exact same Boolean branch, use `List.cons_merge_cons` and the actual child erasure. No sortedness premise. |
| Exact base and selected-branch equations for both projections | Unfold the same run and `Resources.bind`; the first projection has base zero and `1+C_child`, the second base one and `1+E_child`. This is the exact analytical correspondence, including nil/nil. |
| `E cmp xs ys = C cmp xs ys + 1` | The same induction, preserving one terminal invocation. Do not infer it from a separately chosen output list. |
| `C cmp xs ys ≤ xs.length + ys.length` | The child bound and strict one-head decrease; simple Nat arithmetic. Order, distinctness and stability are irrelevant. |
| `E cmp xs ys ≤ xs.length + ys.length + 1` | The preceding two results. No claim that this deliberately loose bound is attained. |
| Projection to `CallCount.tick` recurrence | Apply `reweight Prod.snd`; at a nonempty step identify the result with `tick (bind projectedChild (fun zs => Resources.pure (head :: zs)))`. Base is `(suffix,1)`. This reuses the existing entry convention directly. |
| Source specialization | Instantiate `cmp = fun x y => decide (x ≤ y)` and compose erasure with `sourceMerge_eq_merge`; the first projection equations coincide with handwritten `Sorting.C_merge`. Keyed specialization uses `mergeBy_source`, without ordering records. |
| Length/occurrences/sortedness/stability clients | Rewrite the actual returned value through erasure, then consume the existing `length_merge`, `merge_perm_append`, membership, sortedness and stable-key contracts. Do not copy those proofs into a parallel resource hierarchy. |

A general Nat base/step tariff core is possible, but materially less direct here: comparison and entry metrics require separate instantiations, followed by an additional parameter law. One pair execution already records both and composes using an existing interface. A scalar model `c*C + e*E` can be ordinary reweighting if a concrete client later needs it. No tariff record, general tally language or separate framework belongs in this bounded unit.

This is a comparator-invocation count. Evaluating an arbitrary `cmp`, computing a key, constructing a cons, measuring input lengths, allocating cells and scanning an untouched suffix have no extra charge in the source comparison projection. The invocation projection charges the model's merge calls, not all Lean function calls. The standard source explicitly says `List.merge` is replaced at runtime by a proven-equivalent tail-recursive version (`LeanListSort-Basic.lean:18–37`); value equivalence to that implementation does not transfer these counts, stack usage or allocations.

### 5.1 A justified optional exact key/map transport

One additional theorem has a concrete use if the connected examples erase tagged records to keys. With `f : α → β` in an independent universe and

```lean
hc : ∀ a ∈ xs, ∀ b ∈ ys, cmp a b = cmp' (f a) (f b)
```

prove the **whole measured pair** identity

```text
run cmp' (xs.map f) (ys.map f)
  = ((run cmp xs ys).1.map f, (run cmp xs ys).2).
```

The hypothesis matches pinned `List.map_merge`. It restricts comparison agreement only to the actual cross-input members; recursive tails inherit it. Each branch agrees, so an induction preserves both result and counts. No injectivity, decidable payload equality, ordering or same-universe constraint is required. Instantiating `f=key` yields an exact tagged-execution/key-execution bridge, including duplicate keys. Existing `List.map_merge` alone gives only the result equality and is not enough for counts.

This is a bounded proposal, not justification for a public map framework or an uncharged-runtime claim about executing `List.map`. It may be stated using an exact pair as above, or existing `bind` with a zero-observation value map. Add it only with that actual connected use.

## 6. Actual composition clients

### 6.1 Two sequential merges

The appropriate client is existing `Resources.bind`, not a new executor. For example, first merge `xs` with `ys`, then merge a supplied `zs` with the actual first returned list:

```text
bind (run cmp xs ys) (fun first => run cmp zs first).
```

Erasure is `List.merge zs (List.merge xs ys cmp) cmp`. Total comparisons and entries are the sums of the two actual observations. Because each merge has its own terminal invocation, **the bound execution has `E_total = C_total + 2`, not `+1`**. Projection homomorphisms preserve this actual sequencing by `reweight_bind`. With `m=length xs`, `n=length ys`, `k=length zs`, the existing output-length theorem gives `C_total ≤ 2*(m+n)+k` and `E_total ≤ 2*(m+n)+k+2`. No outer wrapper-entry charge has been silently added.

The independent case contributor calculated a useful argument-dependence witness: first merge `[2]` and `[0]` using `≤`, obtaining `[0,2]` with `(1,2)`; merge `[1]` with that actual result to obtain `[0,1,2]` with `(2,3)`, hence total `(3,5)`. Substituting the unrelated concatenation `[2,0]` into the second call instead produces `[1,2,0]` with `(1,2)`, hence `(2,4)`. The proposed client should consume the real bind and generic contracts, not merely state these independent numbers.

A useful existing positive-domain connection is `Resources.CallCount.add_entry_le (T : Nat) (positive : 1 ≤ T) : T+1 ≤ 2*T` (`CallComparison.lean:95`). Both nonempty inputs imply `1 ≤ C`, so it applies to one merge. At an empty-side base `C=0,E=1`, and `zero_cost_entry_matters K` rejects `E ≤ K*C` for every natural coefficient. This is an optional short client of the same metrics, not a new asymptotic unit. Keep `CallComparison` out of the minimal resource import unless used there; its client can import it separately.

### 6.2 Actual existing `LeftistQueue.toListQ` body

`Applications/Search/LeftistQueue.lean` is an existing independent client; it imports `Std`. The relevant namespace is `Search.LeftistQueue`, with payload `α : Type u` and priority `π : Type v`. Under `[LE π] [DecidableLE π]`:

```lean
mergeOn (key : β → π) (xs ys : List β) :=
  List.merge xs ys (fun x y => decide (key x ≤ key y))
toListQ (.fork k x p l r) =
  (x,p) :: mergeOn Prod.snd (toListQ l) (toListQ r)
```

These are the actual definitions at lines 165–170. `mergeOn_equations key x y xs ys` and `mergeOn_perm key xs ys` are already public at 172–180. `toListQ_perm q` (317) needs no `Std.IsLinearPreorder`, `Heap` or `Ranked`; `toListQ_sorted q hq` (323) needs `Std.IsLinearPreorder π` and `hq : Heap q`, not `Ranked`. `entries_length q` (59) gives `(entries q).length = size q`.

An actual body client can perform the measured priority merge on the two already obtained child-list values, then bind an uncharged `(x,p)` cons. Its returned list equals the existing raw-node `toListQ` definition for **every** cached rank and both raw subtrees. The merge-only bounds become `C ≤ size l + size r`, `E ≤ size l + size r + 1` through `toListQ_perm.length_eq` and `entries_length`. Actual arbitrary-rank examples can consume this bridge.

This measures only that ordinary merge. Computing `toListQ l` and `toListQ r`, traversing their trees, and entering the enclosing enumeration call are separate work, not made free by a value theorem. A whole enumeration executor and quadratic theorem are later Chapter 14 obligations. The raw body equation is not a sortedness assertion: reuse `toListQ_sorted` only with the entire node's `Heap` proof, which also controls the root relative to the children. Sorted children alone do not justify prefixing an arbitrary root priority.

A concrete proposed boundary has root priority 9, raw cached rank 99, and raw singleton children of priorities 1 and 2. Its body value has priorities `[9,1,2]` and merge-only observation `(1,2)`. It is neither a ranked nor heap-ordered witness, but it still illustrates the unconditional body value/cost connection. This is a chosen exercise realization component, not a claim that the book prescribed conaled's exact queue carrier or this local tariff.

## 7. Minimal proposed file/import scope

The coordinator's six-path outline is sufficient; all are future proposals, not edits made by this task:

| Path inside the future candidate | Bounded responsibility |
| --- | --- |
| Existing `Applications/Sorting/Merge.lean` | Add the two order-free input-sublist observations and the genuinely useful sortedness-converse/iff consequence; preserve existing definitions, assumptions, statements and proofs. |
| New `Applications/Resources/ListMerge.lean` | One actual measured merge, exact projections/source correspondence, entry relation and bounds; optional exact map/key transport only with the connected use above. Imports can be `Applications.Sorting.SourceMerge` and `Applications.Resources.CallCount`; those transitively provide value laws, Measured and product homs. Do not import the queue here. |
| New `Examples/MergeCosts.lean` | Actual two-stage bind/reweight, keyed/tie/Empty/unsorted boundaries, and actual existing queue-body connection. Import `Applications.Search.LeftistQueue` here; use current CallComparison only if its positive/zero-domain client is included. |
| `SquareApplications.lean` | One public example import through the existing root. No new entrypoint or verification setting. |
| `docs/research/fdsa-reconstruction-map.md` | Append source-to-public-contract and remaining-scope correspondence. |
| One new source-use note | Exact prescribed/chosen algorithm provenance, declared metrics, license attribution and current uncompiled status. No copied manuscript or optional new hierarchy. |

The new operation and all universal raw observations work for `Empty` payloads, since the empty case needs no inhabitant. The operation takes an explicit Boolean comparator; order/decidability belongs only to source/key specializations, sortedness assumptions only to sortedness/stability laws. Natural observations live in `Type 0` independently of arbitrary payload/key universes. No index/set finite-carrier assumption is involved.

Specific case boundaries worth preserving are equal-key left preference; same untagged result with different comparator-path counts (for example `[1,1]` and `[1]` under `≤` versus `<`); arbitrary-comparator sublist preservation; sortedness converse even when forward order laws fail; empty-side zero comparisons/one invocation; and actual intermediate-result dependence. These are connected examples for the proposed contracts, not a separate new review campaign.

## 8. Remaining work and limits

The full source comparison recurrence for floor-left top-down merge sort, actual sorted child arguments, termination, stability, ceiling-log/all-length bounds and the printed power-of-two theorem remain in the retained Chapter 2 plans. Standard Lean merge sort splits an odd list ceil-left (`LeanListSort-Basic.lean:55–63`); one shared merge theorem does not identify its source costs. Bottom-up/natural run ordering and whole-sort stability likewise need their actual algorithms and counts. C02-108–112 remain in the reconciled scope.

The sorted-list priority-queue ADT and its direct minimum/deletion costs, the complete node-labelled heap enumeration and its quadratic bound remain queued Chapter 14 work. XH01 is not a dependency or a substitute for these concrete algorithms. Binomial equal-rank carry/link/insertion is not ordinary list merge; neither value nor tariff is transferred to it.

No genuine mathematical blocker was found for this bounded unit. The only identified reusable value gap is the two input-sublist observations and their converse consequence; the actual measured merge is the missing resource operation. The suggested implementation proof order is: additive value facts; one measured recursion and exact equations; value/source bridge; projection relation and bounds; optional exact key transport; actual bind and queue-body clients. Pinned names and recurrence hypotheses have been inspected, but Lean elaboration, termination script syntax, simplifier behavior and warnings remain untested until the coordinator authorizes compilation of an immutable candidate. No claim is validated by this report.

Only this report was written. No repository source, old report, requirements, ticket, reference, cache, configuration or gate was changed. No Lean/Lake/compiler/checker, project hash helper, Git, remote operation or acceptance action ran. Ordinary SHA-256 identifies this report after final readback; the coordinator owns its checkpoint persistence.
