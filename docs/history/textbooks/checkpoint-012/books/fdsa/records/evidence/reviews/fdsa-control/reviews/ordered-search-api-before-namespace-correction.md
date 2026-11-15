# Ordered binary-tree search: API and architecture preflight

Recorded 2026-11-02. **Bounded source/API preparation only. No implementation scope is frozen, no Lean source is written or compiled, and no chapter or shared draft is accepted.** This is the sole new file written for this assignment. All declaration names in the proposal sections are proposals, not exported APIs.

The resumed task reports Chapter 1 guarded attempt 3, launched at 22:08:37 UTC on `07e480f6ec9958d4975bb90151005b84f2907614`, as the sole authorized compiler/checker. The earlier attempts' unknown outcomes remain unknown. The stopped source report records its own earlier recovery state; this note does not revise that historical evidence. Original chapter order, the Chapter 1 prerequisite, the initial Chapter 2 prefix `c80eec9`, all frozen requirements and all existing gates remain unchanged.

## 1. Recommendation

There is a small genuine gap: **one selected-path search that returns the actual stored label**, with heterogeneous key queries supplied by an ordinary label-to-`Ordering` function. Existing `BinaryTree.indexOf` and `BinaryTree.get` supply useful path/value operations but do not already supply this one-pass operation, its heterogeneous correctness, or its source-style invocation count. The existing tree carrier, strict-key invariant, comparison predicate and measured-value pair suffice; no new tree, comparator-law record, search machine, query signature language or Set/Map hierarchy is justified.

The smallest implementation candidate is one actual recursive `Resources.TreeSearch.run`, returning `Measured (Option α) Nat`. Its Nat observation is **E, search invocations including a terminal empty call**. Expose the Option result and E as projections, and derive the visited-node observation V from E and the returned option. Prove V's own branch equations and the exact hit/miss identity; do not add an independent recursive V executor. This is smaller than a dual-Nat run for this particular operation, because the result already determines the only difference between E and V.

The direct operation must choose one child at each node. Executing a whole-tree fold, materializing inorder, mapping all labels to keys first, or following an index with a second `get` pass is not the same execution. Those expressions may serve as value specifications or separately measured programs. No cost equality follows from their value equality.

A first unit can remain one new resource/search module plus its connected examples and documentation. It does not need a separate recursively defined unmeasured search merely to supply an erasure target: the returned Option projection is already the ordinary query. A later pure-module extraction can be considered if an actual dependency need appears; it is not necessary to introduce another recursion now. Keep the operation, invariant/comparison assumptions, semantic laws and resource consequences distinct within the public statements.

## 2. Exact inspected inputs and retained status

Read the complete current `tickets/FDSA-XS01.md`, complete `research/ordered-search-interim-notes.md`, and complete stopped `research/ordered-search-source-preflight.md` (29,001 bytes / 410 lines, SHA-256 `71fe9b69807db736c0d6319995a61bf72b1b5ff508c085d128de96c07b589c21`). The source report owns the detailed book/theory correspondence and source-license receipt; its contents are not modified here.

Applicable guidance was read in the existing workflow: `AGENTS.md`, `docs/agents/architectural-quality.md`, `docs/agents/domain.md`, the glossary, ADR index and the relevant provenance/implementation guidance. The architectural requirement is to reuse ordinary constructions, separate operations and laws, expose only necessary capabilities, and preserve useful specializations. No preservation-family or language-interface change is proposed.

The retained tree candidate is `66eae34815a177c6b4bf5120e05202ebb8876c91`, original parent `28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2`, with XT01 ancestor `64c6b777d828ecfe83234fc2aed94600a1f24297`. The removed tree worktree was not recreated. Read-only `git show`/source inventory access used the required pinned Nix shell from the main checkout. All these inherited tree drafts remain uncompiled and unaccepted.

| Actual retained file | Read scope and identity |
|---|---|
| `Applications/Trees/Ordered.lean` at `66eae348` | Complete 126 lines, 5,817 bytes; SHA `26549e623acdce3ac29e3fdd30858eb068c1bf7cd5f223468bbcbb30ecffbe66` |
| `Applications/Trees/Observations.lean` at `66eae348` | Complete 107-line fold/inorder/map interface; 4,119 bytes, SHA `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Cached.lean` at `66eae348` | Complete 135-line erasure/reader/recursive-validity interface |
| `Applications/Trees/OrderedRotations.lean` at `66eae348` | Complete 43-line invariant transport; SHA `c610556b727e7ddd35187c9302649948a203c0d0076e8bf3758fcfc95da50c89` |
| `Examples/OrderedTrees.lean` at `66eae348` | Targeted existing printed-tree, strict-key/duplicate, key-injectivity and tag-map clients; not a new full review of all examples |
| `Applications/Resources/Measured.lean` | Complete 71 lines, 2,906 bytes; SHA `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| `Applications/Resources/CallCount.lean` | Complete 58 lines, 2,447 bytes; SHA `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |

The last two resource files were compared as ordinary bytes: current main, `66eae348` and corrected C1 commit `07e480f6` contain identical versions. This comparison is provenance evidence, not a project hash gate or validation result.

Pinned dependencies: Lean 4.35.0 at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries at `66e469188fe07963e5cf666c7d4433f45b8131c5`. Exact local primary-source reads include:

| Pinned source | Read scope; SHA-256 |
|---|---|
| `Mathlib/Data/Tree/Basic.lean` | Complete; `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |
| `Mathlib/Data/Tree/Get.lean` | Complete 72 lines; `773d67e99f76e26c96e2d718d88203396fdacba3506d2e42476823440e5aa4bd` |
| `Mathlib/Data/Ordering/Basic.lean` | Complete 56 lines; `8add9a4a99dd00271f4f50a73171d5a0f4af31e971c73a807da90a93e0aac89a` |
| `Mathlib/Order/Compare.lean` | Complete 209 lines in the bounded comparison inspection, with relevant signatures reread; `2a1b09abbc7d20f75a832fc47d1b6014f606938ad1b3db8c9e2bf545fdaca0d4` |
| `Mathlib/Data/Ordmap/Ordnode.lean` | Header/carrier and actual `mem`/`find` definitions, not every balancing theorem; `b6d9b8fc2d8a3ea9ec0259babc3cf77066d0aea2658c15cdbdf752075c7c0668` |
| `Mathlib/Order/Defs/LinearOrder.lean` | Targeted comparison interface, including its section assumptions and existing equality theorem; `80b40cffbc66b648612bd1195941e30e52d8309701d280a23dc2fc48047a9209` |
| Lean `Init/Data/Ord/Basic.lean` | Actual literal comparator and relevant branch laws; `0e3a0b38ea902721b3cdaa49b65c87fbf53f9acc94ee783a82f342b5aaa9b630` |
| Lean `Init/Data/List/Find.lean` | Targeted actual find/lookup declarations, not a whole-file review; `a6c652c553d9752ce238f3943aa1a39c125148358a178240a84afe0524b22b0e` |
| Lean `Init/Data/Option/Lemmas.lean` | Targeted Option-map laws; `07352a5ba0376bb4b37f5cae891a4df439666cbd63aecd1abc00f7cfebee2586` |

Mathlib sources were read under `conaled/.lake/packages/mathlib/`. The pinned installed Lean source was read inside the existing Nix shell under `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`; no Lean executable was invoked. The initial un-escalated view's missing toolchain path was an access-view issue, not evidence of a pin change. No dependencies were downloaded or changed.

## 3. Existing operations and semantic interfaces

### 3.1 The actual carrier and path operations

`BinaryTree α` is universe-polymorphic, node-labelled, with constructors `.nil` and `.node a l r` (label first). The existing `map`, `height`, `numNodes`, `numLeaves` and `height_le_numNodes` are ordinary structural operations/laws. No payload order, equality or inhabitance is needed to construct a tree. Use `BinaryTree`, not the deprecated `Tree` aliases.

The exact signatures in `Mathlib/Data/Tree/Get.lean:33–65` are:

```lean
BinaryTree.indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α) :
  BinaryTree α → Option PosNum
BinaryTree.get : PosNum → BinaryTree α → Option α
BinaryTree.getOrElse (n : PosNum) (t : BinaryTree α) (v : α) : α
```

`indexOf` calls `cmpUsing lt x a`; LT maps the selected left result with `PosNum.bit0`, EQ returns `PosNum.one`, and GT maps the right result with `PosNum.bit1`. `get` interprets exactly those constructors. The file supplies definitions and deprecated aliases, **no search correctness, strict-order, map or cost theorem**. A scoped search of the relevant tree/search sources found no already exported heterogeneous one-pass stored-entry search.

The homogeneous index query cannot ask for a bare key `κ` in labels `κ × β` without supplying an entire label. Supplying a dummy payload would unjustifiably exclude `Empty`. Searching `t.map key` and using that index in the original tree avoids that default but adds a full mapping traversal and then a second path traversal.

A feasible **new value-only connection**, if useful as a checked specialization, is:

```lean
-- Proposed, not an existing theorem; no order laws are needed.
find? (fun a => cmpUsing lt x a) t =
  (BinaryTree.indexOf lt x t).bind (fun n => BinaryTree.get n t)
```

Prove it by structural induction, splitting the same `cmpUsing` result and then the recursive Option. The `bit0`/`bit1` equations of `get` discharge the branches. This confirms compatibility with the existing path convention; it does not identify counts or make `indexOf` followed by `get` a single traversal. It need not force the `Data.Num` dependency into the minimal core; a connected example can import `Tree.Get` separately.

`Ordnode.find` is also real existing code, in `Mathlib/Data/Ordmap/Ordnode.lean`: it takes a homogeneous label query with `[LE α] [DecidableLE α]` and routes using `cmpLE`. Its carrier stores a cached size in every node, and its order-equivalence treatment supports a different map/set construction. It is not the canonical ordinary `BinaryTree` and cannot be substituted here without a representation/operation bridge. Adding that bridge just to use its short find recursion would enlarge this task. Existing graph-search `Search.Heuristic.lookup` in `Applications/Search/HeuristicCore.lean:95–105` is a `List (V × Nat)` visited-cost store; `Applications/Search/Ordered/Exact.lean` searches increasing functions/intervals. Neither is this tree operation. Existing priority queues likewise remain separate.

### 3.2 Reuse the retained all-subtree invariant

At `66eae348`, `Trees.Ordered R (.node a l r)` means both children are ordered, every left label relates to `a`, and `a` relates to every right label. It is not merely an immediate-child-root test.

Useful exact calls are:

```lean
Trees.ordered_node R a l r
Trees.ordered_of_pairwise_inorder R t h
Trees.pairwise_inorder_of_ordered R hR t h
Trees.ordered_iff_pairwise_inorder R hR t
Trees.ordered_congr_inorder R hR t s hInorder
Trees.ordered_map_iff S f t
Trees.ordered_map_key_iff key key' f hf t
Trees.ordered_key_iff_pairwise key t
Trees.ordered_key_nodup key t h
```

The last two require only `[Preorder κ]` on the key type. `ordered_map_key_iff` requires only `[LT κ]` and pointwise key preservation. Full weak-order/nodup equivalence uses `[PartialOrder κ]` in `ordered_key_iff_nodup_sortedLE`; no such stronger premise is necessary for the proposed strict-key search theorem.

`Trees.inorder_node a l r` gives `inorder l ++ a :: inorder r`; `inorder_map f t` and `inorder_length t` provide the observation bridge. `Trees.Cached.erase` is label projection by `Prod.fst`; its map/inorder/shape laws do not require cache validity. A query ignoring outer annotations can therefore use raw label transport, independently of `Cached.Valid` or the annotation's correctness.

The retained `OrderedTrees.key_injective_on_labels` example at lines 227–230 already uses the exact pinned declaration
`List.inj_on_of_nodup_map (Trees.ordered_key_nodup key t h) ha hb hk`.
Thus uniqueness on the stored labels is derivable; a global injectivity premise on `key` is unnecessary. This example can guide a proof if needed, without moving unrelated old declarations or inventing another uniqueness record.

### 3.3 Existing comparison law, with its exact limit

`Ordering.Compares` in `Mathlib/Data/Ordering/Basic.lean:24–27` needs only `[LT κ]`: LT means `q < k`, EQ means actual equality `q = k`, GT means `k < q`. In `Mathlib/Order/Compare.lean:57–92`:

```lean
Ordering.Compares.eq_lt [Preorder κ] :
  o.Compares q k → (o = .lt ↔ q < k)
Ordering.Compares.eq_eq [Preorder κ] :
  o.Compares q k → (o = .eq ↔ q = k)
Ordering.Compares.eq_gt [Preorder κ] (h : o.Compares q k) :
  o = .gt ↔ k < q
Ordering.Compares.inj [Preorder κ] :
  o₁.Compares q k → o₂.Compares q k → o₁ = o₂
cmp_compares [LinearOrder κ] (q k : κ) : (cmp q k).Compares q k
Ordering.Compares.cmp_eq [LinearOrder κ] (h : o.Compares q k) : cmp q k = o
```

These exact existing laws support an ordinary, input-local premise, rather than a new comparison-law carrier. A `Preorder` instance alone does **not** calibrate an arbitrary route, nor does it make `cmpUsing` a lawful equality-key comparison: distinct incomparable keys, or distinct equivalent elements of a preorder, can produce EQ.

The book's `Cmp` is `<`, then `=`, then GT. **That literal operation already exists in pinned Lean** (`Init/Data/Ord/Basic.lean:317–320`):

```lean
compareOfLessAndEq {α} (x y : α)
  [LT α] [Decidable (x < y)] [DecidableEq α] : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt
```

Use this operation directly for the source specialization; do not add a wrapper that merely repeats it. Its definition requires only the displayed decisions, not a lawful order. Correctness still needs the semantic laws. Mathlib already supplies the precise result bridge in `Mathlib/Order/Defs/LinearOrder.lean:236–244`, under the section's `[LinearOrder α]` declared at line82:

```lean
cmp_eq_compare (a b : α) : cmp a b = compare a b
cmp_eq_compareOfLessAndEq (a b : α) :
  cmp a b = compareOfLessAndEq a b
```

The same file has `LinearOrder.compare_eq_compareOfLessAndEq`, `compare_lt_iff_lt`, `compare_eq_iff_eq`, `compare_gt_iff_gt` and `compare_iff`. The source route's local `Compares` proof can be obtained by `simpa only [cmp_eq_compareOfLessAndEq] using cmp_compares q (key a)`. There is no need to reconstruct an already existing comparator-agreement proof, instantiate a new `Ord` record, or introduce a comparison-law hierarchy.

Mathlib `cmpUsing` itself tests `<`, then reverse `<`, then EQ. The equality above identifies Ordering results on linear keys, not primitive programs. Even the existing canonical `compare` may use an instance's optimized implementation subject to its value law. Neither a branch-result equality nor using the literal `compareOfLessAndEq` supplies a primitive-test or runtime theorem; E/V below exclude that internal work.

## 4. Proposed minimum public operation and semantic statements

Names in this section are suggestions for later scope freezing. Let `α : Type u`, `β : Type v`, `κ : Type w` with independent universes. No global `Fintype`, order, equality decision or `Inhabited α` is needed.

```lean
-- One actual recursion; selected branch only.
run (route : α → Ordering) : BinaryTree α → Resources.Measured (Option α) Nat
-- nil:       CallCount.tick (Resources.pure none)
-- node/EQ:   CallCount.tick (Resources.pure (some a))
-- node/LT:   CallCount.tick (run route l)
-- node/GT:   CallCount.tick (run route r)

-- Transparent observations, not additional recursive executions.
find? route t := (run route t).1
entries route t := (run route t).2
visits route t :=
  let r := run route t
  r.2 - (if r.1.isNone then 1 else 0)
```

The `let` describes one observed result; no claim about evaluation sharing of separate calls to these projections is made. A client sequencing two measured queries must actually bind those computations and add their costs. Reusing an erased result or calling a projection repeatedly is not a memoization theorem.

The raw operation's useful positive contract is:

```lean
find? route t = some a → a ∈ Trees.inorder t ∧ route a = .eq
```

This needs no order or invariant. Adding local `Compares` under only `[LT κ]` gives key soundness for a hit, without needing a BST. Strict ordering and transitivity are needed for completeness and uniqueness, not for the fact that an honest EQ hit has the requested key.

The main proposed correctness statement can use `[Preorder κ]`, with:

```lean
hOrdered : Trees.Ordered (fun a b => key a < key b) t
hRoute : ∀ a ∈ Trees.inorder t, (route a).Compares q (key a)
```

and conclude:

```lean
find? route t = some a ↔ a ∈ Trees.inorder t ∧ key a = q
find? route t = none ↔ ∀ a ∈ Trees.inorder t, key a ≠ q
```

`hRoute` is over the actual input's stored labels, not all possible payloads or all possible queries. It is a proof premise, not an instruction to compute inorder before searching. The linear specialization `route a := cmp q (key a)` discharges it with `cmp_compares`; the literal source specialization uses the existing `compareOfLessAndEq q (key a)` and the already proved `cmp_eq_compareOfLessAndEq`. No payload order/equality or global key injectivity is added.

**Structural proof route.** Generalize the local route premise before induction. The node invariant supplies both child invariants and whole-subtree bounds. Restrict `hRoute` to the chosen child through `inorder_node`. On LT, `hRoute` gives `q < key root`; the root and all right labels cannot equal q, by irreflexivity/transitivity. The induction hypothesis handles exactly the left recursion. GT is symmetric. On EQ, q is the root key; the strict bounds exclude any same-key child label, so the returned full entry is uniquely determined. This proves the `some` iff directly, not only key membership. The `none` iff follows by Option cases and completeness.

### First-match and map observations

A minimally assumed first-inorder theorem can use the existing route's EQ Boolean:

```lean
find? route t =
  (Trees.inorder t).find? (fun a => decide (route a = Ordering.eq))
```

under the same strict-key/local-calibration premises. Only the existing decidable equality of `Ordering` is used. If the specification instead uses `decide (key a = q)`, its additional `[DecidableEq κ]` belongs to that observer, not the raw operation or its main correctness law.

The relevant pinned Lean declarations are `List.find?_eq_none` (239), `find?_eq_some_iff_append` (242), `find?_some` (297), `mem_of_find?_eq_some` (304), `find?_map` (358), and `find?_isSome` (289). Split the list find result: a `some a` supplies membership and the EQ predicate; local calibration plus the main search iff fixes the returned entry. A `none` supplies the universal predicate failure and hence query absence. There is no need to implement another list search.

For source maps, `List.lookup` already supplies first binding precedence. Its observer uses `[BEq κ]`, with `[LawfulBEq κ]` for actual key equality. `List.lookup_eq_findSome?` (1356), `lookup_eq_none_iff` (1366), `lookup_isSome_iff` (1370), `lookup_eq_some_iff` (1374) and `lookup_append` (1387) provide exact existing contracts. A local lawful key decision, available for the source linear-key specialization, supports:

```lean
-- Proposed value correspondence; β has no extra structure.
(find? route t).map Prod.snd = (Trees.inorder t).lookup q
```

for labels `κ × β`, the strict first-key invariant and calibrated route. A short list induction also connects `lookup` with projecting the first pair whose key matches; that is a specification lemma, not a measured traversal. The raw path does not compute that list. For augmented labels `((κ × β) × γ)`, the semantic payload projection is `fun a => a.1.2`, not the outer annotation.

The exact Option helpers inspected are `Option.map_eq_some_iff`, `map_eq_none_iff`, `isSome_map` and `isNone_map` in `Init/Data/Option/Lemmas.lean:291–300`. They support Bool membership and semantic-payload observations without inventing defaults or equating `some false` with absence. No Set/Map operation record or XA01 dependency is needed merely for these query clauses.

### Raw label transport

A useful single exact transport theorem, with no ordering premise, is:

```lean
-- Proposed; h is local to the actual tree.
h : ∀ a ∈ Trees.inorder t, route' (f a) = route a
run route' (t.map f) = ((run route t).1.map f, (run route t).2)
```

Here f may change universes and may be noninjective. Induct on the tree, use root decision equality to choose the same branch, and restrict h to the selected child. This simultaneously transports the Option result and E; `Option.isNone_map` transports derived V. The unconditional pullback special case takes `route := fun a => route' (f a)`.

This is stronger and more useful than deriving costs from equality of final results. It covers tag erasure, noninjective payload maps that preserve keys, and source comparator-result correspondence. It does not charge or erase the cost of actually constructing `t.map f` in a client. Existing `ordered_map_key_iff` separately transports the semantic invariant when the key is preserved.

## 5. Measurement choice, exact equations and bounds

The existing APIs needed are already small:

- `Resources.Measured α C := α × C`, with independent value/observation universes.
- `Resources.pure [Zero C] a := (a,0)` and `Resources.bind [Add C] r f := ((f r.1).1, r.2 + (f r.1).2)`.
- `Resources.CallCount.tick r := (r.1,r.2+1)`, with `tick_value` and `tick_cost`.
- `CallCount.primitive_rule` relates an actual bind through a zero-charge observation to its returned value and unchanged cost. `bind_value` and `let_rule` expose actual reached values in compositions.

The recommended executor uses these actual constructors. Its count is not paired with a separately computed result after the fact. Nil and EQ perform `tick (pure ...)`; LT and GT tick the actual selected recursive computation. Structural termination follows from the tree argument even though the query/route is unchanged.

Let F, E and V denote its projections/derived observation. The exact equations are:

| Case | F | E | V |
|---|---|---:|---:|
| nil | none | 1 | 0 |
| node/EQ | some root | 1 | 1 |
| node/LT | F on left | E(left)+1 | V(left)+1 |
| node/GT | F on right | E(right)+1 | V(right)+1 |

First prove `1 ≤ E` by structural cases. Since the terminal indicator is either zero or one, it is at most E; ordinary Nat subtraction then proves

`E = V + (if F.isNone then 1 else 0)`.

For a recursive branch, F is exactly the selected child result, so the indicator is unchanged. From `Echild ≥ 1`, `(Echild+1)−indicator = (Echild−indicator)+1`; this gives V's actual visited-node recurrence without another recursion. The short arithmetic can use direct Nat lemmas or existing `omega`; there is no need for a custom subtraction algebra or general resource carrier.

A paired `(V,E)` run would also be mathematically sound, but supplies redundant stored information and extra projection machinery here. It becomes justified only if an actual consumer requires an independently composed multi-observation run. Nothing in the current source/cases requires that. In contrast to ordinary merge, the terminal correction depends on success: **E=V on hits, E=V+1 on misses**. For two sequenced queries, the correction is the sum of their actual miss indicators, not a uniform one. V is not an additive reweighting of E alone, and the combined E together with only the last returned Option does not recover the first query's miss indicator. A composition needing both visit totals must retain the per-query observations; this does not require storing a redundant pair in every single-query run.

### Raw path bounds

For every raw route and finite tree, with no order/cache/balance premise:

```lean
1 ≤ E
V ≤ t.height
E ≤ t.height + 1
F = some a → 1 ≤ V ∧ E ≤ t.height
```

Proof route: induction with `height(node a l r) = max l.height r.height + 1`. The unconditional E bound uses the selected child's bound and the corresponding `le_max_left`/`le_max_right`. The successful bound uses that the actual selected child also succeeds; nil cannot satisfy the success premise. Then split F into some/none and use the exact terminal identity to obtain V ≤ height. All equations include empty trees: height0, E1, V0.

`BinaryTree.height_le_numNodes` can supply the weaker linear-in-size bound as an existing specialization; it is not logarithmic. No XT02 logarithm theorem or new growth wrapper is necessary for this raw component. Later balanced-tree bounds must combine actual query cost with their own valid-state height/cardinality relation and the empty-call constant.

### Source meaning and excluded primitive work

The stopped source inspection found no `time_fun`, `T_isin` or `T_lookup` declaration in the relevant query theories. E is an explicitly declared reconstruction of the source-style recursive invocation tariff, not a recovered generated theorem. Comparator internals, projections, Option construction and nonrecursive observation wrappers are uncharged. An arbitrary route may be expensive; the bound on E is not a bound on its total runtime.

V counts reached nonempty nodes/three-way route evaluations. It is not the literal source's primitive Boolean-test count. The book comparator uses one `<` test on LT and an additional equality test on EQ/GT. Mathlib's `cmpUsing` tests `<` in two directions instead. Equal Ordering outcomes under lawful order do not prove primitive-work equality; that needs a separately declared observation/correspondence. No such additional test-counter executor or comparator framework is recommended for this first boundary.

## 6. Feasible deepest-present-key tightness

The p.59 worst-height assertion must retain a lower witness, not only an upper inequality. A precise proposed theorem is:

```lean
-- Proposed, all universes independent.
[Preorder κ]
key : α → κ
route : κ → α → Ordering
t : BinaryTree α
ht : t ≠ .nil
ho : Trees.Ordered (fun a b => key a < key b) t
hc : ∀ a ∈ Trees.inorder t, ∀ b ∈ Trees.inorder t,
  (route (key a) b).Compares (key a) (key b)
-- conclusion:
∃ a ∈ Trees.inorder t,
  run (route (key a)) t = (some a, t.height)
```

This quantifies comparison calibration only for stored-key queries against stored entries. A simpler proposed source specialization takes `[LinearOrder κ]` and `route q a := compareOfLessAndEq q (key a)`; `cmp_compares` transported through the existing `cmp_eq_compareOfLessAndEq` supplies hc. The `cmp` specialization follows from that same existing equality. Either version avoids a global `Inhabited` label/key assumption, a depth datatype, a supremum over an empty query type or a probability construction.

**Concrete proof construction.** Induct on t with its nonempty/invariant/local-route premises generalized. At a leaf node, select its root. Calibration at that root against itself forces EQ by `Compares.eq_eq`; E=height=1. At any other node select a nonempty child whose height is maximal. This can be implemented by cases on the two child constructors and, when both are nodes, a Nat comparison of their heights; no separate height-zero characterization or new tree-shape dependency is required. Restrict ho and hc to that child and apply induction. Its witness a is a stored child label. The parent strict bound and `Compares.eq_lt` or `.eq_gt` force the parent search to enter exactly that child. The actual recursive equation adds one, and maximality rewrites the parent height to child height plus one. Thus the returned full entry and exact E are proved together. The hit relation then gives V=height.

This is present-key tightness. It does not assert that every query costs height, nor that the maximum E over all possible keys equals height: an absent query can cost height+1. With a nonempty lawful tree, the witness and the raw upper bound give the source's height-scale worst-case claim. At empty t no present-key witness exists, while the actual invocation still costs1. A source reconstruction that leaves this witness to Chapter5 must label the omission explicitly; the proof is economical enough to recommend including it with the shared path laws.

## 7. Concrete reuse and failure boundaries

The complementary case report owns independent numerical derivations. The following existing fixtures and theorem connections make the proposed interface reviewable without creating unrelated structures:

- `OrderedTrees.printedTree` and `printed_ordered` at retained lines64–85: six stored keys `[2,3,5,6,8,9]`, root6. Query8 gives a concrete deepest hit of height3; query4 distinguishes V3 from E4. Root and intermediate hits test the nonuniform terminal correction.
- `taggedTree`, `discardTag`, `discardTag_not_injective` and `discarded_ordered_iff` at lines249–283: consume the **raw** run-map theorem for counts/results and the existing invariant-map theorem separately. No cache validity or global payload injectivity is appropriate.
- `sameKeyRecords` at lines172–195 has root `(1,10)` and right child `(1,20)`. It is full-record nodup and lexicographically ordered but not strictly key ordered. Rotating it changes which payload a root hit returns while leaving inorder unchanged. Therefore full-entry lookup is not invariant under arbitrary same-inorder shape changes; the strict-key premise is material.
- A malformed distinct-key tree can store a key in the wrong child. Raw success-membership/height bounds remain true, but completeness fails. A strictly ordered tree with an always-EQ route separately shows why ordering does not replace calibration.
- A map value `false` must be observed as `some false`; missing keys return none. A map with semantic value type `Empty` supports every available key query on its only possible empty tree, with no default value.
- A cross-universe payload map or annotation erasure must instantiate the actual raw transport. This tests independent universes rather than assuming every label and key is `Type 0`.
- The retained C05-094 finite present-key example can evaluate actual searches at keys3,6,9: balanced visits/entries `[2,1,2]`, chain `[1,2,3]`, sums5 and6 and means5/3 and2. All hits justify E=V. A finite arithmetic client is sufficient; it does not require a uniform distribution on an infinite key type or a new probability dependency.
- A homogeneous instance may consume the proposed existing `indexOf`/`get` value bridge. It must explicitly withhold a cost correspondence for that two-pass expression.

For lawful trees with equal inorder and calibrated query routes, the full-entry result is determined by the main success/absence theorem. Existing rotation inorder and invariant transport can therefore supply a value client. Different shapes can have different E/V. No rotation cost preservation or balancing algorithm follows.

## 8. Smallest dependency and file boundary; unresolved obligations

A prospective minimal module is `Applications/Resources/TreeSearch.lean`, importing existing `Applications/Resources/CallCount`, retained `Applications/Trees/Ordered`, and `Mathlib/Order/Compare` for its semantic theorems. It contains one actual run, transparent observations and the ordinary laws above; no new carrier or executor layer is introduced. `Measured` is already an ordinary pair with the needed universe separation. A companion example module can reuse the retained ordered-tree fixtures and import `Mathlib/Data/Tree/Get` only for the optional path-value bridge. Documentation/root-map integration belongs to the later frozen scope, not this report.

This depends mathematically on XT01 observations and XT07 order laws, with C1 measured/call-count support. The saved XT07 ancestry includes XT06, but query mathematics does not require new rotation implementation work. Do not import tree-fold execution, shape logarithms, collection ADTs, probability, priority queues or another unaccepted branch merely to name a simple consequence. The saved drafts' unaccepted ancestry does not grant validation, and the original Chapter2 integration prefix is unchanged.

No concrete mathematical obstruction was found in this boundary. Genuine work still required if scope is frozen includes the actual structurally recursive run, all semantic/map/first-match proofs, derived V equations, raw bounds, the nonempty tightness proof, meaningful connected examples, source attribution and later matching compilation/review gates. The suggestions have not been elaborated. Likely implementation details to resolve through ordinary Lean checking include the exact implicit argument choices in list/Option proofs, input-local premise restriction at each node, and Nat subtraction normalization; none is presently a demonstrated failure.

Every concrete chapter algorithm remains queued: insert/delete and their invariant proofs, `split_min` and its nonempty domain, interval queries, Node3's conditional second comparator, all color/height/cache balancing, treap split/join and the C10-117 conditional work issue. A query theorem supplies only its query clause of a Set/Map interpretation. Neither the source `Lookup2` value bridge nor an annotation map gives free whole-tree conversion or the costs of updates. No arbitrary-BST logarithmic bound, compiler/runtime theorem, primitive-test bound or conditional probability result is claimed.

Licensing follows the retained source report: Mathlib source carries Apache-2.0 notices; any source-derived Isabelle adaptation must retain the full applicable BSD notice/attribution recorded in `book-source/ISABELLE-COPYRIGHT`, not just a license label. The official book and pinned companion identities are already recorded in that stopped report; no manuscript or new remote material is copied into a deliverable here.

## 9. Handoff limits

This report is an API/source design recommendation, not frozen requirements or source release. The complete source report and interim record were read. The separately owned case report was coordinated through its concrete findings; its author subsequently reported a stopped identity of 30,396 bytes / 536 lines, SHA `dec26d65e156f7ca381a4e49a653729fd4cc011e3fca56331c8468d6f6f7a754`. This API task does not claim a full read or independent review of that separate report. Root owns reconciliation and any later decision/checkpoint/release.

Only this new report was written. No Lean/source/worktree/ref/cache/toolchain configuration changed; no compiler, Lake, checker, project hash helper, enumeration campaign or remote operation ran. Source reads and ordinary SHA-256 identities are not validation. Stop report writes after complete readback and identity handoff.
