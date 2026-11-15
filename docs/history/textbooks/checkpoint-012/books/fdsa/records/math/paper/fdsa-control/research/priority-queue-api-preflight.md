# Priority-queue occurrence, minimum, and merge API preflight

Prepared 2026-11-02. **Read-only source/API preparation; no implementation, compilation, chapter activation, or acceptance.** This note concerns a possible small shared observation bridge. It leaves the complete Chapter 14 inventory, Chapter 1 gate, initial Chapter 2 integration prefix, current queue consumers, and all other requirements unchanged. Names explicitly marked *proposed* below are not existing declarations or frozen requirements.

## 1. Recommendation and inspected identities

The existing `Search.PriorityInterface.Operations`, `ExactLaws`, and `ExactQueue` already provide the appropriate operations, exact occurrence observation, separate invariant, and laws. A second queue carrier or an Isabelle-locale-shaped Lean hierarchy is unnecessary. The genuine remaining shared work is a small collection of checked observation adapters: list permutations to multisets, actual removal to an optional minimum/residual observation, its agreement across lawful implementations, and source minimum/deletion notation on its valid nonempty domain. A supplied merge needs its own occurrence and validity laws, not a new hierarchy.

The strongest useful central observation is the proposed
`popObs Q q := (Q.remove q).map (fun (e, r) => (e.2, priorityMultiset Q r))`.
For two valid queues whose initial priority multisets agree, these observations agree under explicit antisymmetry of priority comparison. This result needs neither payload nor priority decidable equality: compare the two selected least priorities, then cancel the common multiset cons. It does not equate selected payloads, raw residual states, list order, or tie-dependent Huffman trees.

| Evidence | Identity and role |
|---|---|
| Current conaled source | `/workspace/scratch/845aa1048b05/conaled-ch01-cost-models`, root-designated base `07e480f6ec9958d4975bb90151005b84f2907614`. Read source directly; no Git, compiler, or project checker was run in this task. |
| Mathlib | Existing pinned dependency `56a005855ea17e0b0958f73ec801ae140b0a1679`, under this checkout's `.lake/packages/mathlib`. |
| Batteries / Lean | Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0, source commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Existing pins only; nothing fetched or changed. |
| Book and scope | Entire `book-source/chapter14.txt`; `fdsa-control/research/chapter14-obligations.md`, C14-001–040. July 27, 2026 book, printed pp. 179–182; PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Primary Isabelle support | `Priority_Queue_Specs.thy` and `Heaps.thy`, read in full at revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`. This support revision postdates the manuscript; no assertion that it built this PDF. |
| Governing project guidance | `AGENTS.md`, `docs/agents/architectural-quality.md`, `docs/agents/domain.md`, glossary/ADR material, source policy, and relevant implementation guidance. Operations, observations, invariants, and work remain separate; existing source algorithms and consumers are preserved. |

The companion source assessment is `fdsa-control/research/priority-queue-source-preflight.md`, separately owned and stopped at 29,031 bytes / 416 lines, SHA-256 `79fff00277221c6c5279841a5eb88517f57a2e52cf8b0f1ac393492a87bdec79`. This report uses no XA01 declaration: the saved, uncompiled/unaccepted ADT draft is unnecessary for this bridge.

## 2. Exact existing project surface

All paths in this section are relative to the inspected conaled checkout. These are existing declarations, not proposals.

### 2.1 Operations and law strength

`Applications/Search/PriorityInterface.lean:18–45`, namespace `Search.PriorityInterface`, separates universes for payload `α : Type u`, priority `π : Type w`, and carrier `Type z`:

```lean
structure Operations (α : Type u) (π : Type w) where
  Carrier : Type z
  empty : Carrier
  add : List (α × π) → Carrier → Carrier
  remove : Carrier → Option ((α × π) × Carrier)
```

This operation record needs no order, equality decision, inhabitance of payloads/priorities, or finite carrier. A particular `Operations.Carrier` has an element because `empty` is supplied; that does not require either payload type to be inhabited.

`Applications/Search/ExactPriority.lean:12–34` adds the separate law package:

```lean
structure ExactLaws [LE π] (ops : Operations.{u,w,z} α π)
    (entries : ops.Carrier → List (α × π))
    (Valid : ops.Carrier → Prop) : Prop where
  empty_entries : entries ops.empty = []
  empty_valid : Valid ops.empty
  add_valid : ∀ xs q, Valid q → Valid (ops.add xs q)
  add_exact : ∀ xs q, (entries (ops.add xs q)).Perm (xs ++ entries q)
  remove_none : ∀ q, ops.remove q = none ↔ entries q = []
  remove_spec : ∀ q e r, Valid q → ops.remove q = some (e,r) →
    Valid r ∧ (entries q).Perm (e :: entries r) ∧
      ∀ a ∈ entries q, e.2 ≤ a.2
```

`ExactQueue (α : Type u) (π : Type w) [LE π]` extends these same `Operations` with `entries`, `Valid`, and `lawful : ExactLaws ...`. Its existing projection abbreviations have calls `Q.add_exact xs q`, `Q.add_valid xs q hq`, `Q.remove_none q`, and `Q.remove_spec q e r hq hremove`.

Two scope facts must survive any adapter:

- `add_exact` and `remove_none` are unconditional on raw states. `add_valid` and `remove_spec` require validity. Moving validity into the former two would weaken an existing contract.
- The source abstraction laws constrain valid states (and constrain minimum/deletion only on nonempty valid states). The exact interface therefore yields a **one-way source-law adapter**. An arbitrary source law package need not imply this stronger raw-state exact interface.

The weaker `PriorityInterface.Laws` also contains `add_origin`, key/priority `add_covers`, and `add_length`, which permit replacement. `ExactQueue.keyed Q key` at `ExactPriority.lean:37` retains the actual operations and needs only `[LE π]` plus `[Std.Refl (fun a b : π => a ≤ b)]`. There is no converse from keyed coverage to occurrence preservation.

### 2.2 Existing concrete realizations

| Existing declaration | Exact operation and useful hypotheses |
|---|---|
| `exactLeftist` (`ExactPriority.lean:54`) | Under `[LE π] [DecidableLE π] [Std.IsLinearPreorder π]`, uses `LeftistQueue.PQ α π`, `emptyQ`, `addListQ`, `deleteQ`, `entries`, and `Valid`, unchanged. No payload order/equality/inhabitance. |
| `listRemove xs` (`ExactPriority.lean:74`) | Sorts `xs` with `List.mergeSort (fun a b => decide (a.2 ≤ b.2))`, then returns `none` or the first entry and tail. Definition needs `LE`/`DecidableLE`; `listRemove_none xs` explicitly omits `Std.IsLinearPreorder`. |
| `listRemove_spec xs a rest h` (`ExactPriority.lean:93`) | Under the linear-preorder assumptions, proves `xs.Perm (a :: rest)` and `∀ b ∈ xs, a.2 ≤ b.2`. |
| `exactList` (`ExactPriority.lean:123`) | Carrier `List (α × π)`, `empty := []`, `add := fun xs q => q ++ xs`, `remove := listRemove`, `entries := id`, and `Valid := fun _ => True`. It sorts at removal, so it is not Exercise 14.1's sorted-list representation with constant-time head/tail. |

`Applications/Search/LeftistQueue.lean` is the real existing carrier, not Mathlib's ordinary `BinaryTree` and not a leaf-labelled Bracketing tree. Its raw constructor is `PQ.fork rank value priority left right`; `entries` is root followed by left and right entries. The smart `LeftistQueue.fork x p l r` may swap children to enforce rank order. Consequently its `combineQ` is a leftist merge, not the book's Chapter 14 naive plain-node merge.

Useful exact argument orders from this module:

```lean
entries_length q : (entries q).length = size q
nullQ_iff q : nullQ q = true ↔ q = .null
size_zero_iff q : size q = 0 ↔ q = .null
fork_entries x p l r :
  (entries (fork x p l r)).Perm ((x,p) :: entries l ++ entries r)
combineQ_entries a b :
  (entries (combineQ a b)).Perm (entries a ++ entries b)
combineQ_valid a b (ha : Valid a) (hb : Valid b) : Valid (combineQ a b)
deleteQ_spec q e r (hq : Valid q) (hd : deleteQ q = some (e,r)) :
  Valid r ∧ (entries q).Perm (e :: entries r) ∧
  (∀ z ∈ entries q, e.2 ≤ z.2) ∧ size r + 1 = size q
addListQ_entries xs q :
  (entries (addListQ xs q)).Perm (xs ++ entries q)
makeQ_spec xs : Valid (makeQ xs) ∧ (entries (makeQ xs)).Perm xs
```

Locations: `entries_length`/`nullQ_iff`/`size_zero_iff` at 59/67/70, `fork_entries` at 95, `combineQ_entries` at 182, `combineQ_valid` at 257, `deleteQ_spec` at 272, insertion at 287–299. `combineQ_entries` and `addListQ_entries` require executable comparison (`LE`, `DecidableLE`) but no validity, heap invariant, rankedness, or linear-order laws. `combineQ_valid` needs both inputs valid and the linear-preorder laws. It does not need disjoint entries.

`Heap` and cached-shape `Ranked` are already separate; `Valid q := Ranked q ∧ Heap q` (`:133–137`). `root_all k x p l r h` (`:238`) proves the heap root is below all entries from `Heap`; its existing signature retains the section's `Std.IsLinearPreorder π` and explicitly omits `DecidableLE π`. The root step itself uses reflexivity. No rankedness premise is required. `toListQ_perm q` (`:317`) is unconditional, while `toListQ_sorted q hq` (`:323`) needs only `Heap q`, not `Ranked q`. These distinctions should not be erased by a stronger-than-needed generic wrapper.

## 3. Pinned multiset and minimum APIs

The following signatures were inspected in the pinned Mathlib source. They do not require a finite payload or priority type: the observation itself is a finite list/multiset.

| Module and declaration | Exact bridge or hypothesis boundary |
|---|---|
| `Data/Multiset/Defs.lean:100`, `Multiset.coe_eq_coe` | `(l₁ : Multiset α) = l₂ ↔ l₁.Perm l₂`. No equality decision. |
| `Defs.lean:124,224`, `mem_coe`, `coe_card` | Membership is list membership; `(l : Multiset α).card = l.length`. |
| `Data/Multiset/ZeroCons.lean:71–112` | `coe_eq_zero l : (l : Multiset α) = 0 ↔ l = []`; `cons_coe a l`; `cons_inj_right a : a ::ₘ s = a ::ₘ t ↔ s = t`. Cons cancellation has no `DecidableEq` premise. |
| `Data/Multiset/AddSub.lean:58` | `coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α)`. Note the orientation; conversion of a permutation to a sum normally rewrites with its reverse. |
| `Data/Multiset/MapFold.lean` | `map_coe f l`, `map_cons f a s`, `map_add f s t`, `map_singleton f a`, `card_map f s`; source/target universes independent. No injectivity or equality decision for these laws. |
| `MapFold.lean:61,109` | `forall_mem_map_iff : (∀ y ∈ s.map f, p y) ↔ ∀ x ∈ s, p (f x)`; `map_eq_zero : s.map f = 0 ↔ s = 0`. |
| `AddSub.lean:156,354` | Under `[DecidableEq α]`, `erase_cons_head a s : (a ::ₘ s).erase a = s` and `sub_singleton a s : s - {a} = s.erase a`. The decision is needed at this operation boundary, not for occurrence decomposition or cancellation. |
| `Data/Finset/Dedup.lean`, `Data/Finset/Basic.lean:473–477` | Under `[DecidableEq α]`, `Multiset.mem_toFinset`, `toFinset_eq_empty`, `toFinset_nonempty : s.toFinset.Nonempty ↔ s ≠ 0`. Finite support, not global finite type. |
| `Order/Bounds/Defs.lean`, `IsLeast` | Under `[LE α]`, membership plus lower-bound predicate. No reflexivity, transitivity, totality, antisymmetry, or decidability is built into this definition. |
| `Order/Bounds/Basic.lean`, `IsLeast.unique` | Under `[PartialOrder α]`, two least elements of the same set are equal. An explicit antisymmetry hypothesis suffices for the particular comparison proof without packaging a stronger order. |
| `Data/Finset/Max.lean:134–172` | Under `[LinearOrder α]`, dual-generated `Finset.min' s hs`, `min'_mem s hs`, `min'_le s x hx`, `le_min' s hs x h`, `isLeast_min' s hs`, and `min'_eq_iff s hs a`. |

The relevant dual-generated statements are `s.min' hs ∈ s`, `s.min' ⟨x,hx⟩ ≤ x`, `IsLeast (↑s) (s.min' hs)`, and
` s.min' hs = a ↔ a ∈ s ∧ ∀ b ∈ s, a ≤ b`.
The names are generated from the corresponding maximum declarations by `to_dual`, not missing merely because a text search sees `max'` at the definition. `Finset.min : Finset α → WithTop α` is also available, but the nonempty `min'` or direct `IsLeast` contract is the smaller source bridge. Neither requires `Inhabited α` or a bottom/top element of `α`.

There is no inspected `Multiset.min` API to reuse in the scoped pinned Multiset files; a remembered `Mathlib.Data.Multiset.MinMax` module would be incorrect at this pin. The actual finite-support route above is sufficient. `LinearOrder π` supplies `DecidableLE π`, `DecidableEq π`, and the Std order instances used by the existing concrete queues; none of these must be imposed on payloads.

## 4. Proposed smallest observation and source-law route

The following are **proposals**, not new source declarations. At the unbundled law level, write
`E q := (entries q : Multiset (α × π))` and `P q := (E q).map Prod.snd`.
If ordinary named helpers are useful for several clients, `entryMultiset`, `priorityMultiset`, and `popObs` could live beside `ExactPriority`; they need no new record. These definitions themselves need no order beyond whatever is already required by a bundled `ExactQueue` argument.

### 4.1 Preserve actual occurrence information first

Given `h : ExactLaws ops entries Valid`, the existing laws yield:

1. `E ops.empty = 0` and `Valid ops.empty`.
2. Unconditionally, `E (ops.add xs q) = (xs : Multiset (α × π)) + E q`; singleton insertion is the actual call `ops.add [e] q`. Validity is a separate consequence when `Valid q`.
3. Unconditionally, `ops.remove q = none ↔ E q = 0`, hence also iff `P q = 0` by `Multiset.map_eq_zero`.
4. If `Valid q` and the actual result is `ops.remove q = some (e,r)`, then
   `Valid r`, `E q = e ::ₘ E r`, and `IsLeast {p | p ∈ P q} e.2`.
   The selected entry's membership comes from the permutation and the cons head; the lower bound is exactly `remove_spec` transported through `Prod.snd`.
5. Mapping the cons equation gives `P q = e.2 ::ₘ P r`, with no payload equality decision and no loss of multiplicities. Cardinality decreases by one; an empty result never supplies a fictitious selected element.

This proof sequence uses the actual returned state and entry. It does not infer an operational correspondence from two unrelated scalar or multiset sequences. It also does not use support inclusion as a substitute for multiplicity equality: `Multiset` membership and `Subset` forget counts, while the cons equation retains them.

### 4.2 Central observed-removal agreement

**Proposed theorem shape:** let `Q : ExactQueue.{u,w,z} α π` and `R : ExactQueue.{v,w,z'} β π`, with independently chosen payload/carrier universes. Assume `[LE π]`,
`hantisymm : ∀ p q : π, p ≤ q → q ≤ p → p = q`, `Q.Valid q`, `R.Valid r`, and `priorityMultiset Q q = priorityMultiset R r`. Then

```text
(Q.remove q).map (fun (e,q') => (e.2, priorityMultiset Q q'))
  = (R.remove r).map (fun (e,r') => (e.2, priorityMultiset R r')).
```

Proof route: match the two actual `Option` results. A none/some mismatch contradicts raw `remove_none` and the observed cons decomposition; both none is immediate. In the some/some case, each selected priority belongs to the common starting multiset, and each minimum law bounds the other selected priority. `hantisymm` identifies them. Rewrite the two starting-multiset decompositions and use `(Multiset.cons_inj_right p).mp` to identify the residual priority multisets; map equality follows. This requires no global linear order, reflexivity, transitivity, totality, `DecidableEq π`, or `DecidableEq α/β` beyond the explicit laws already supplied. Concrete realizations can retain their stronger construction assumptions.

This is the appropriate observation-level agreement across `exactLeftist` and `exactList`, including ties and duplicate priorities. Different payload choices at the same priority are allowed. Full-entry residual equality would require more information about the selected entry; raw state equality is not meaningful across distinct carriers. Without antisymmetry, two distinct priorities equivalent under a preorder can both be least, so the selected-priority equality is not justified.

### 4.3 Source minimum and deletion notation

For the source's element-only interpretation use payload `Unit` and priority type `σ`; insert `x` by `ops.add [((),x)]`. Observe `P`, not a set of entries. Under `[LinearOrder σ]`, nonempty `P q` has the existing minimum
`(P q).toFinset.min' (Multiset.toFinset_nonempty.mpr hnonempty)`.
The least-priority theorem identifies the actual removed priority with this value by `Finset.min'_eq_iff` or `IsLeast.unique`.

At this local linear-order boundary, `DecidableEq σ` is available. The priority cons equation and `sub_singleton`/`erase_cons_head` yield `P r = P q - {e.2}`. There is no reason to require equality decisions for arbitrary payloads merely to obtain this source statement. For full entries, the stronger equality-free cons equation remains the preferred basic result.

Nonempty observation implies existence of an actual some result simply by matching `ops.remove q` and using `remove_none`; this existence fact does not require validity. Validity supplies the minimum and residual-validity conclusions. A total optional observation is `(ops.remove q).map Prod.fst`; a proof-domain minimum may instead extract from that established some result. Both avoid arbitrary inhabitants of empty types. If a separate source-style state-valued deletion adapter is useful, the ordinary match `none => q | some (_,r) => r` explicitly chooses identity on empty observation; the abstract source law imposes no such choice on empties. This adapter is a proposal, not a reason to add a second queue executor.

The figure's seven laws, plus the companion `is_empty` reflection, follow one way from these facts and the existing invariant laws. Empty get-min is left optional or proof-restricted. Do not reinterpret source HOL underdefinition as an arbitrary Lean value of a possibly empty priority type.

### 4.4 Finite-observation realizability is derived, not assumed

For every finite entry multiset `m : Multiset (α × π)`, the existing laws imply
`∃ q, Q.Valid q ∧ entryMultiset Q q = m`. Use `Quotient.inductionOn' m` to choose a list representative `xs` for this proposition, then use the actual state `Q.add xs Q.empty`. Its validity is `Q.add_valid xs Q.empty Q.empty_valid`; `Q.add_exact xs Q.empty` and `Q.empty_entries` identify its observation with `xs`. This proof uses no equality decision, payload inhabitance, classical default, or new surjectivity assumption. It does not construct a representation-independent inverse or assert uniqueness of raw states.

Priority-only realizability is different. With an explicit payload witness `a0 : α`, apply the entry result to `m.map (fun p => (a0,p))` for any `m : Multiset π`, and project back. The pinned `Multiset.map_map g f s` and `map_id` in `MapFold.lean:150–158` establish the projection equation. The source `Unit` specialization supplies `a0 := ()`. With payload `Empty`, all entry observations are empty; for a nonempty priority type a nonempty priority multiset cannot be realized. Thus unconditional surjectivity onto priority multisets would be false, although surjectivity onto finite entry multisets still holds. No infinite-map non-surjectivity argument from the separate ADT task applies here.

## 5. Concrete peek and emptiness: small missing access bridge

There is no direct-root optional peek in the inspected `LeftistQueue` module. A **proposed** ordinary `peekQ?` needs only the existing constructor match:
`null ↦ none`, `fork _ x p _ _ ↦ some (x,p)`.
It needs no order, decision, or validity. Case analysis proves the exact raw-state correspondence
`(deleteQ q).map Prod.fst = peekQ? q`, with only `deleteQ`'s `LE`/`DecidableLE` parameters. On a heap, the selected priority is least by `root_all`/`all_iff`; rankedness is not needed for this root fact. The generic exact-queue validity law is still retained as written.

Likewise existing `nullQ_iff`, `entries_length`, `size_zero_iff`, and `Multiset.coe_eq_zero` connect actual `nullQ q = true` to `E q = 0`, and then to `P q = 0`, on all raw leftist states without any heap validity. This supplies the companion source's weaker valid-state reflection without inventing another emptiness operation.

The projection equation is **value semantics only**. Evaluating `deleteQ` on a nonempty tree invokes `combineQ`; evaluating direct-root `peekQ?` would not. A semantic peek defined by projecting removal cannot be assigned the direct-root access cost. No cost theorem is proposed in this preflight, even for the small pattern match, until an actual measured operation/tariff is selected.

Existing Batteries provides useful evidence that this shape is conventional, not a reason to replace the carrier. `Batteries/Data/PairingHeap.lean:64,272` has `Batteries.PairingHeapImp.Heap.head?` and
`Heap.deleteMin_fst : ((s : Heap α).deleteMin le).map (·.1) = s.head?`.
`Batteries/Data/BinomialHeap/Lemmas.lean:20` has the corresponding `Batteries.BinomialHeap.Imp.Heap.deleteMin_fst`, whose right side is `s.head? le`. These are different heap representations and proof invariants. Their existing optional APIs do not impose `Inhabited`; the separate unsafe/default-taking style accessors are unnecessary here.

## 6. Merge is an ordinary operation with two independent laws

`Operations` and `ExactQueue` deliberately have no merge field. For a supplied `merge : C → C → C`, the source obligations are occurrence compatibility and invariant preservation, separately:

```text
∀ q r, Valid q → Valid r →
  (entries (merge q r)).Perm (entries q ++ entries r)
∀ q r, Valid q → Valid r → Valid (merge q r).
```

Convert the first result to `E (merge q r) = E q + E r` and map priorities to obtain the same equation for `P`. A particular implementation's stronger unconditional occurrence theorem should remain unconditional. Neither law implies the other. Both input-validity premises matter for the source-validity result. No disjointness premise is justified; `merge q q` doubles every occurrence, and overlapping inputs are ordinary supported cases.

Two actual existing implementations connect this without a new queue family:

- `LeftistQueue.combineQ`: `combineQ_entries a b` supplies unconditional occurrence equality, while `combineQ_valid a b ha hb` separately preserves both parts of `Valid`. This uses actual smart constructors and actual recursive merge, with existing tie direction and argument order untouched.
- `List.append` on the existing `exactList` carrier: its `entries` is identity and `Valid` is `True`, so the list observation equation is direct. This is a compatible merge for the existing unsorted-list realization; it does not make its deletion constant time or turn it into Exercise 14.1's sorted-list queue.

There is no need to add merge to every queue instance: the pinned Braun interpretation in Chapter 16 is only a base priority queue. A small theorem with an ordinary supplied operation and two proof arguments is sufficient unless future concrete uses independently justify bundling. No ownership, destructive-consumption, persistent amortized, or execution-cost conclusion follows from the multiset sum law.

## 7. Connected cases and failure boundaries

These are proposed ways to exercise the small bridge using real operations, not new frozen cases or an implementation campaign.

| Connection | Meaningful claim and required boundary |
|---|---|
| Duplicate minima on actual realizations | Start from actual `add [((),1),((),1),((),3)] empty` for `exactLeftist` and `exactList`; use validity and actual removals. Priority observation is `{1,1,3}`, then one removal gives priority 1 and residual `{1,3}`. A second minimum remains 1. The generic `popObs` agreement consumes both implementations. |
| Actual merge with overlap | Build two valid queues and use actual `combineQ`; include common priorities or self-merge so the client distinguishes multiset addition from deduplicating union. Connect `nullQ` and optional peek on the resulting real queue. |
| General payload ties | Keep two distinct payloads at priority 1. Exact removal deletes one returned full entry, but different implementations may select different payloads. A standalone priority-minimal peek and standalone priority-minimal remove can select different tied entries; that alone does not prove deletion of the full peeked entry. Direct-root/actual-removal agreement remedies that local implementation issue. |
| Existing Huffman consumer | `Applications/Huffman/Priority.lean:22–33,54,88` already supplies actual singleton `insert`, `contents`, `extract`, `delete_size`, and `delete_cached`. `delete_cached Q w q a r hq hd` maps the actual remove permutation through payload projection and uses the cache equations to relate priority to tree weight. A new observation bridge can be consumed on this same actual state or step without changing that algorithm or its interface. |
| Existing independent universes | `Examples/Huffman.lean:173–179` already uses `ULift.{1} Nat` payloads; the queue and observation lemmas should retain that freedom. Empty payload or priority types still support an empty queue and optional none without introducing global `Inhabited`. |
| Existing tie-divergent results | `Examples/Huffman.lean:69–86` proves different tied leftist/list tree outputs with the same optimum cost. Priority observation agreement is compatible with these results; raw output equality would be false. |
| Key-replacing boundary | `Applications/Search/PrioritySearchQueue.lean:108,299–304` has `equal_priority_replaces` and concrete `exact_same_key_tie`, where two same-key entries leave one. Its weaker keyed `Queue` must not be used to prove source occurrence insertion. |
| Validity boundary | A raw leftist-shaped tree with priority 5 at the root and priority 1 below can return 5. The unconditional content/permutation facts still hold; the minimum theorem requires `Heap` or the exact interface's `Valid`. Cached rankedness is a separate concern. |
| Empty and order boundaries | Empty removal is none, not a chosen default. Under a non-antisymmetric preorder, equally least priorities need not be equal. These are substantive reasons for the Option and antisymmetry boundaries, not extra restrictions on arbitrary payloads. |

No finite enumeration, new example, source declaration, or compilation was performed to establish this preflight. Existing compiled status is not inferred from reading a source file; all eventual new clients must be checked on their immutable candidate.

## 8. Dependencies, placement, and work that remains

A possible small observation module is `Applications/Search/PriorityMultiset.lean` importing `Applications.Search.ExactPriority`; alternatively a carefully bounded theorem section could be added to the existing module. This is a placement proposal only. Keep `Search.PriorityInterface` as the existing namespace/domain and leave all old public fields and consumers unchanged. Avoid importing generic ADT refinements, new tree carriers, or a separate queue hierarchy merely to express these elementary observations.

Direct useful Mathlib imports are `Mathlib.Data.Multiset.MapFold` for projected occurrences (with its existing AddSub/ZeroCons dependencies), `Mathlib.Order.Bounds.Defs` for the weak least predicate, and the finite-support/minimum modules only where the source selector is needed: `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Finset.Max`, and optionally `Mathlib.Order.Bounds.Basic` for `IsLeast.unique`. This is a source-inspected dependency route, not a compiled minimal-import claim. The central cons-cancellation agreement can use explicit antisymmetry and avoid the stronger order/selector import. No measured-resource module is needed for these value facts.

The current scope does **not** discharge the following already retained book work:

- C14-014–017 / Exercise 14.1: actual sorted-list representation, insertion and merge, invariant laws, and actual constant-time head/tail observations. Existing `List.orderedInsert`, `Applications.Sorting.mergeBy`, `mergeBy_perm`, and `mergeBy_sorted` are reusable; `exactList` is not the required implementation.
- C14-018–032: ordinary node-labelled heap carrier/predicate/multiset bridge, naive plain-node merge, its termination and two laws, derived insertion/deletion, and maximally unbalanced family. A leftist smart-constructor implementation is not this source algorithm merely because its contents coincide.
- C14-033–036 / Exercise 14.3: actual heap-to-list execution and quadratic upper work bound. `toListQ_perm`/`toListQ_sorted` help after a checked ordinary-tree/carrier bridge but provide no cost correspondence.
- C14-037–040 / Exercise 14.4: inorder-preserving Cartesian heap existence, actual constructor, uniqueness under distinct labels, and repeated-label counterexample. Sorting the list first would not solve the stated inorder obligation.
- Chapters 15–18 and 22–23: their actual heap algorithms, balance/shape/caches, generated or otherwise specified operation costs, logarithmic/amortized bounds, and model correspondence. A semantic minimum or merge bridge proves none of these time bounds.

This possible unit is neither a Chapter 2 prerequisite nor Chapter 14 activation. Source extraction also preserves the precise seven figure laws, the companion's additional `is_empty` law, two merge laws with both validity premises, and the stronger `Heaps.Heap` helper premise for empty deletion. None is silently altered to fit an existing interface.

## 9. Provenance, license, and handoff limits

Primary book URL: <https://fdsa-book.net/functional_data_structures_algorithms.pdf>. The local Chapter 14 inventory pins the manuscript and extracted chapter; this report contains original analysis and short mathematical/API descriptions, not a manuscript copy.

Pinned companion source URLs:

- <https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Priority_Queue_Specs.thy> — 1,654 bytes, SHA-256 `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a`, authors Tobias Nipkow and Peter Lammich.
- <https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Heaps.thy> — 2,946 bytes, SHA-256 `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe`, author Tobias Nipkow.

The pinned Isabelle distribution is BSD-3-Clause (`ISABELLE-COPYRIGHT` SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`). A later translated source unit must retain appropriate provenance/notices. The inspected Mathlib/Batteries files carry Apache-2.0 notices; they are existing pinned dependencies, not new vendored code. No additional license for conaled is invented here.

The concrete shared gap is small and justified by actual exact queue, Huffman, and source occurrence clients. The source route, assumptions, and cons-cancellation proof are sound at statement level; syntax, imports, implicit universe arguments, generated declaration elaboration, and warning cleanliness of any eventual implementation remain untested. No compiler/checker/hash helper, Git/ref/cache action, remote write, chapter acceptance, or new final-review loop occurred. Only this new control report was written; edits stop after full readback and ordinary file-identity reporting.
