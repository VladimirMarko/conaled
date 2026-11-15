# Node-labelled binary trees: shared API and architecture preflight

## Status and recommendation

This is bounded read-only preparation while Chapter 1 remains active. It neither activates Chapter 4 nor accepts any later chapter or saved shared draft. The report path was absent before this write. No Lean source, compiler, checker, project hash helper, Git/ref/index state, dependency, cache, configuration, running gate or requirement was changed. No new implementation or final-review loop was started.

A small shared **observation and augmentation** unit is justified by concrete reuse. Its ordinary carrier should be Mathlib's existing `BinaryTree α`. The genuine gaps are a plain branching fold, node-labelled inorder and its mapping/shape bridges, followed by root-cache access, a smart constructor and an all-nodes cache-validity predicate over `BinaryTree (α × β)`. The fold takes an explicit empty value and ternary combining function; it needs no new algebra record, container typeclass, monoid, ordering or equality capability.

The strongest direct later clients are the interval-maximum cache in Chapter 5 and cached-height AVL trees in Chapter 9. Chapter 15 supplies a further reusable mathematical case, but already has a conaled priority-queue carrier and algorithms: preserve them and establish a representation bridge rather than replacing them with another heap implementation. A size/height product summary and an ordered-list summary give meaningful specialization and composition tests for the small shared interface.

Do not automatically add a whole-fold measured executor, a universal augmentation framework, every Chapter 4 exercise, or every later tree invariant to this unit. Exact local cached-node work may be the smaller resource result, provided its two cache reads, actual callback work and declared constructor/entry charge are retained. A source tariff must be chosen explicitly; the source's selective leftist-heap model charges its nonrecursive cache access and smart constructor zero. This preflight recommends a bounded design, not a requirements freeze or authorization to implement it.

## Governing guidance and inspected sources

Read for this investigation: `AGENTS.md`, `docs/agents/architectural-quality.md`, `docs/agents/domain.md`, `GLOSSARY.md`, `docs/adr/README.md`, ADR 0001 and ADR 0010, and the relevant construction/observation and preservation sections of `docs/language-direction.md`.

The resulting architecture constraints are concrete here:

- Reuse the existing carrier and ordinary recursor; separate an operation from its semantic observation and the laws it satisfies.
- Put hypotheses on the theorem that uses them. Cache access does not need a tree-order invariant; cache correctness does not require BST ordering; a full balanced-tree invariant requires additional shape laws.
- Preserve current representations and clients through checked adapters. Equality after erasing annotations is not injectivity, and it says nothing about work unless a measured execution is also related.
- Recover at least two real specializations and an independent composition, rather than introducing an abstraction only to restate its own definition.
- Keep application mathematics in `Applications`, compositions in `Examples`, and the original proof foundations unchanged. There is no new language frontend, universal interpreter or Felix-parity claim in this proposal.

Primary code was read in `conaled-permutation-joint`, the saved draft reported at `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e`. It is not revalidated by this inspection. Mathlib remains pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The main primary files are Mathlib `Data/Tree/Basic.lean`, `Data/Tree/Traversable.lean`, `Data/Tree/Get.lean`, the conaled files listed below, and the pinned Isabelle reading copies `book-source/Tree2.thy`, `AVL_Set_Code.thy`, `Interval_Tree.thy` and `Leftist_Heap.thy`. Book obligations and their detailed source receipts are already in `research/chapter04-obligations.md`, `chapter05-obligations.md`, `chapter09-obligations.md` and `chapter15-obligations.md`. The source contributor separately owns the broader execution/tariff assessment; this report does not duplicate that inventory. The independently prepared `research/binary-tree-shared-case-preflight.md` was also read; its fixtures remain expectations rather than compiled examples.

## 1. Exact existing carrier and APIs

Mathlib's carrier matches the book's empty-leaf, node-labelled shape:

```lean
inductive BinaryTree.{u} (α : Type u) : Type u
  | nil : BinaryTree α
  | node (value : α) (left right : BinaryTree α) : BinaryTree α
```

The constructor argument order differs from the Isabelle presentation `Node left value right`; make this ordinary syntactic bridge explicit. Do not introduce a second datatype merely to recover that order, or use the deprecated `Tree` aliases.

| Existing declaration | Exact useful meaning and boundary |
| --- | --- |
| `BinaryTree.map f` | Maps every node label and preserves the empty/node structure. `id_map t` states `t.map id = t`; `comp_map f g t` states `t.map (g ∘ f) = (t.map f).map g`. No injectivity is required. |
| `BinaryTree.numNodes` | Empty 0; node `numNodes left + numNodes right + 1`. This is the book's labelled-node count, not `sizeOf`. |
| `BinaryTree.numLeaves` | Empty 1; node sum of the two child leaf counts. These leaves are empty constructors and carry no payload. |
| `numLeaves_eq_numNodes_succ t` | `t.numLeaves = t.numNodes + 1`. |
| `numLeaves_pos t` | Positive empty-leaf count, including the empty tree. |
| `BinaryTree.height` | Empty 0; node `max left.height right.height + 1`. |
| `height_le_numNodes t` | A structural height bound for every tree. It does not imply logarithmic height. |
| `BinaryTree.left`, `right` | Return the indicated child; both return `nil` on `nil`. |
| `BinaryTree.traverse` | Existing applicative traversal evaluates the label action, left traversal and right traversal in that order. |
| `LawfulTraversable BinaryTree` | Provided by `Data/Tree/Traversable.lean`, with `comp_traverse`, `traverse_eq_map_id` and `naturality`. Reuse it for actual independent label effects. |
| `BinaryTree.get : PosNum → BinaryTree α → Option α` | Existing safe path lookup; `getOrElse` takes an explicit supplied default. No new globally inhabited payload is needed. |
| `BinaryTree.indexOf` | Search using a supplied decidable relation. Its definition assumes an appropriately organized tree for intended search behavior; the inspected file does not provide the book's BST correctness or a cost proof. |

The inspected tree modules contain no `fold`, `inorder`, preorder, element-set observation, recursive cache-validity family or required `numNodes_map`/`numLeaves_map`/`height_map` laws. A bounded search of the tree and Catalan files confirmed this local gap; it is not a claim that every possible external tree library was audited.

The datatype's own `Inhabited (BinaryTree α)` instance chooses `nil` and does not require `Inhabited α`. The generic tree API should preserve that distinction. The introductory retrieval-complexity wording in Mathlib's documentation is not a proved logarithmic bound for arbitrary tree shape; a long chain remains a counterexample to an unconditional logarithmic-depth claim.

### Why `traverse` does not replace the needed fold

The applicative label callback receives a label, not the summaries of its two children. It is well suited to shape-preserving label effects and already has lawful composition. The book's augmentation callback receives both child summaries and the node label. Size, height and minimum height are branching computations, and height is not determined by an ordered sequence of labels. There is no reason to force them through an applicative sequence-summary encoding merely to avoid naming a plain fold over the existing recursor.

## 2. Existing conaled interfaces and distinctions to preserve

| Existing component | Reuse | Why it is not the same carrier or full proposed contract |
| --- | --- | --- |
| `Bracketing.Tree` in `Applications/Bracketing/Basic.lean` | `fringeSpec`, `fringeAcc_eq`, arbitrary-suffix correctness and leaf-count/fork-count proof patterns. | Constructors are labelled `leaf` and unlabelled `fork`. There is no empty tree, `size` counts labelled leaves and the fringe is always nonempty. |
| `RandomAccess.Tree` in `Applications/Sequences/RandomAccess/Basic.lean` | Explicit cached-reader, erasure and validity discipline. `fromT_eq_fringe` connects the actual existing representation to bracketing. | Its payloads are at leaves; internal nodes carry cached sizes. `Perfect` and the power-of-two digit invariant must not become premises on arbitrary node-labelled trees. |
| `Bracketing.Cached` | `Triple`, `pack`, `forkT_pack`, `triple_eq_pack_mct` and `Cached` show independent meaning and cached computation. | This is a triple containing a whole leaf-labelled tree and top-level cost/weight summaries. It is neither a node-labelled carrier nor a recursive annotation invariant at every node. |
| `Resources.TreeFlattening` | Actual measured traversals, `cachedFromTWithCost_erasure`, value/work separation, and the flatten-then-sequence/query composition. | The tree is leaf-labelled. Its `appendWithCost` charges copied cells, with empty-append cost 0; that is distinct from FDSA's recursive append-call observation. |
| `Sequences.OrderedSummary` | `summary`, `summary_nil`, `summary_append`, `summary_singleton`, `Valid`, `summarySquare`, `batch_summary` and `batch_decode`. | It summarizes a decoded sequence into a monoid and validates an optional **outer** cache. It does not specify all internal tree annotations, and it cannot recover shape-dependent height from inorder alone. |
| `Resources.Measured`, `bind`, `bind_erases`, `reweight_bind` | Ordinary value/observation products, sequencing in execution order, value refinement and explicit reweighting. | A semantic equality or reweighting law alone does not establish a source execution's cost. |
| `Resources.CallCount` | `tick`, `tick_value`, `tick_cost`, `arguments_rule` and `let_rule`. | The one-unit tick is an explicitly chosen recursive-entry observation. It is not an automatic charge for every nonrecursive cache access or constructor. |
| `SquareKit.ListFusion` | The ordinary-operation and local-law style; reachable fold/scan transport where the actual carrier is a list. | A list fold is not a node-labelled branching fold. Do not flatten every tree merely to apply the list theorem and then claim that execution cost was preserved. |

No current `Applications` or `Examples` file in the inspected checkout uses `BinaryTree`. Thus the new observation names would not require a retrofit of an existing BinaryTree API. Existing leaf-labelled APIs and priority-queue APIs remain real clients to preserve, not interchangeable spellings for the new carrier.

## 3. Concrete chapter clients justify a small common core

| Client | Shared construction actually needed | Additional law or representation boundary |
| --- | --- | --- |
| Chapter 4, C04-062–072 | Product-labelled carrier; explicit zero and ternary fold; root cache; smart node; recursive validity; cached value equals independent structural fold. | This is the chapter's stated generic construction. The size instance must recover `BinaryTree.numNodes`, not define a competing size. |
| Chapter 5, C05-070–078 | Interval tree's root cache and smart node with `max (high a) (max left right)`, and all-node exact-cache validity. | The source endpoint type has a genuine bottom/order assumption at this specialization. Attainment of the maximum and BST ordering are separate later proofs; an upper-bound-only cache would be insufficient for pruning. |
| Chapter 9, C09-001–006 | `ht nil = 0`, root-cache read, and smart node storing `max (ht left) (ht right) + 1`. | Cache validity alone is weaker than AVL validity. The latter also requires recursive balance; BST ordering remains separate again. |
| Chapter 9, C09-095–100 | Later one-pass reconstruction can reuse the same smart node over already reconstructed valid children, or return height with the rebuilt tree. | `debal2`'s actual traversal and work must be proved separately from value equality with the repeated-height reference algorithm. This does not require a generic whole-fold resource executor now. |
| Chapter 15, C15-001–014 | The same minimum-height algebra and root-cache mathematics after an adapter from the existing queue. | The actual leftist smart constructor may swap children. Its content law is an occurrence/permutation law, not unchanged inorder. Preserve the existing queue implementation. |

Basic inorder and annotation-erasure laws are also used by the BST families of Chapters 5, 8 and 9. They are observations, not a reason to fold all later structures into one datatype. A 2–3 tree, a quadtree, a rose/binomial tree, or a general trie may have a different constructor arity or labelling discipline. Chapter 14's abstract priority-queue contract should remain representation-independent. Braun array and heap algorithms may use a matching binary shape but have their own sequence/interleaving or multiset observations; an inorder list is not automatically their array layout.

## 4. Small pure operation and law proposal

All names in this section are proposals, not existing declarations or frozen calls. Use independent universes `α : Type u`, `β : Type v` and `γ : Type w`.

### Branching fold

The common operation is simply:

```text
fold (empty : β) (combine : β → α → β → β) : BinaryTree α → β
fold empty combine nil = empty
fold empty combine (node a left right)
  = combine (fold empty combine left) a (fold empty combine right).
```

It is definable by `BinaryTree.rec`; a plain public function gives callers the source's familiar three-argument algebra. Supplying `empty` is all the capability needed for the empty result. It is not a reason to require an `Inhabited β` instance, a zero typeclass, a monoid or any algebraic laws on `combine`.

The useful small law set is:

- Constructor equations.
- A map equation: folding `t.map f` equals folding `t` with the node-label argument transformed by `f`.
- Fusion: if `h empty = empty'` and `h (combine l a r) = combine' (h l) a (h r)` for the supplied operations, then `h (fold empty combine t) = fold empty' combine' t`.

These laws need only the displayed equalities. A reachable-state variant can be added if a concrete later client needs a law only on reachable summaries; the present size/height projections and inorder transport do not require a new general invariant framework.

### Inorder and existing shape observations

Define one node-labelled inorder observation using the fold or direct structural recursion. Its constructor law is `inorder left ++ [a] ++ inorder right`. The equivalent `inorder left ++ a :: inorder right` is convenient for proofs. The value equation alone does not identify the work of two displayed appends with one append; any measured direct traversal must retain its chosen recurrence.

Required useful laws are:

```text
(inorder t).length = t.numNodes
inorder (t.map f) = (inorder t).map f
(t.map f).numNodes = t.numNodes
(t.map f).numLeaves = t.numLeaves
(t.map f).height = t.height.
```

They apply to arbitrary `f`, including noninjective functions and annotation erasure. The leaf-count map law can use the existing node/leaf identity. Keep `numNodes`, `numLeaves` and `height` as the canonical existing operations and prove fold specializations equal to them; do not introduce aliases with competing count conventions.

An element-set observation can be derived as `{a | a ∈ inorder t}` with no `DecidableEq α`. A multiset observation can use the ordinary list-to-multiset coercion when a client needs multiplicities. Neither requires a new tree-element container. Whether to expose both immediately should be driven by the first clients; inorder already carries their information, while its full ordering must not be replaced by equality of sets or multisets.

The arbitrary-suffix inorder accumulator from C04-017 and its source count are useful future Chapter 4 work, but not necessary to validate the generic fold/cache interface. Its proof pattern is already present as `Bracketing.fringeAcc_eq`, with a different carrier.

### Generic augmentation over the existing product-labelled tree

Use `BinaryTree (α × β)` directly. No augmented-tree datatype, cache record or invariant-carrying carrier is necessary.

For fixed `empty : β` and `combine : β → α → β → β`:

```text
read empty nil = empty
read empty (node (a, b) left right) = b

smartNode empty combine left a right
  = node (a, combine (read empty left) a (read empty right)) left right

Valid empty combine nil = True
Valid empty combine (node (a, b) left right)
  ↔ Valid empty combine left ∧ Valid empty combine right
      ∧ b = combine (read empty left) a (read empty right).
```

The central laws are:

```text
Valid left → Valid right → Valid (smartNode left a right)

Valid t → read empty t
  = fold empty combine (BinaryTree.map Prod.fst t).
```

Arguments suppressed in the last display are the same fixed `empty` and `combine`. The second statement connects the cached result to an independently defined structural observation; it does not define correctness as agreement with the cache itself.

Erasing a smart node yields the ordinary node built from erased children, unconditionally. Applying the inorder/map and shape-map laws then preserves payload inorder, node count, empty-leaf count and height under erasure. These facts do not require cache validity: malformed annotations are still erased to the same shape and labels. Only equality of the stored summary to the independent fold requires validity.

`Valid` is a Prop-valued all-node invariant. No decidable equality on `α` or `β`, no order, no `Inhabited α`, and no associativity or commutativity are needed. A Boolean checker would require appropriate decidability and would be a separate operation; it is not necessary for the shared proof interface.

If bottom-up annotation becomes a concrete client, it can itself be an ordinary instance of this same fold: use the annotated empty tree as the base and `smartNode` as the combining function. No second recursion framework is needed. Prove separately that erasure returns the original tree, every annotation is valid, and the root reader agrees with the original structural fold. These are value obligations; the definition alone supplies no whole-program runtime bound.

## 5. Existing leftist queue must be a preserved specialization

`Applications/Search/LeftistQueue.lean` already defines:

```lean
Search.LeftistQueue.PQ (α : Type u) (π : Type v)
  | null
  | fork (rank : Nat) (value : α) (priority : π) (left right : PQ α π)
```

It has ordinary `size`, cached `rank`, structural `shortPath` and `rightPath`, `Ranked`, `Heap` and `Valid`, plus the actual rank-based `fork` and recursive `combineQ`. Existing theorem names include `fork_ranked`, `fork_rank`, `fork_size`, `fork_entries`, `rank_paths`, `rank_size` and `rank_log`.

A later checked structural equivalence can connect this carrier to

```text
BinaryTree ((α × π) × Nat)
```

by mapping a queue fork to `node ((value,priority),rank)` and recursively translating its children. Both inverse laws and the reader/size/shape equations need proofs, but they require no payload equality, inhabitation or priority ordering. The book's element-only leftist heap can then use the existing `PQ Unit α` specialization as already planned in Chapter 15.

Minimum-height cache correctness corresponds to the algebra `empty = 0`, `combine l _ r = min l r + 1`. It is not the whole `Ranked` invariant: leftist orientation additionally orders the child ranks/shortest heights. The current `rank_paths` theorem already establishes both cached-to-shortest-path and cached-to-right-spine agreement under `Ranked`. The new generic family should compose with that result and the Chapter 4 minimum-height laws, not erase the stronger invariant or duplicate the queue algorithm.

The actual `fork` conditionally swaps the children. Its existing `fork_entries` conclusion is a `List.Perm` statement, deliberately not equality of entries in one fixed order. Therefore a generic noncommutative inorder-summary law cannot be transported across `fork` as if no swap occurred. The source content/multiset contract and the shape/cache contract have distinct proofs.

This adapter is a later concrete integration task. The bounded first generic unit need not include a migration of `LeftistQueue` or retroactively claim that its original proofs were derived from the new fold.

## 6. Specializations and compositions that should be checked with any candidate

These are proposed proof targets, not results newly compiled by this preflight. Reuse the independent asymmetric fixture from `binary-tree-shared-case-preflight.md`:

```text
node 1 (node 0 nil nil) (node 3 (node 2 nil nil) nil).
```

Its node count is 4, height 3 and inorder `[0,1,2,3]`; preorder is `[1,0,3,2]`. It detects child-order and traversal-order mistakes that a symmetric fixture could miss. The same note supplies a malformed four-node annotation with a correct and locally consistent root. The smaller three-node boundary below makes the same logical distinction independently of this asymmetric case.

### Size and AVL-height clients

Instantiate the fold and cache family twice:

```text
Size:   empty = 0, combine l _ r = l + r + 1
Height: empty = 0, combine l _ r = max l r + 1.
```

Prove the structural folds equal `BinaryTree.numNodes` and `BinaryTree.height`, respectively. Then instantiate the generic valid-smart-node and valid-reader theorems. The height case must not assume AVL balance; it is correct for skew trees as well. The later AVL invariant adds balance separately. Both cases work over arbitrary payload types, including an empty payload type for the empty-tree case.

### Product projection via fusion

Use a single pair summary:

```text
empty = (0,0)
combine (nl,hl) _ (nr,hr) = (nl+nr+1, max hl hr+1).
```

Apply the fold-fusion law with `Prod.fst` and `Prod.snd` to prove the two independent observations. Instantiate the cache theorem once for the pair and recover both reader contracts. This tests universes, composition and law reuse; it is more useful than two unrelated arithmetic examples. A one-pass execution claim still needs a measured recurrence if included.

### Ordered sequence and monoidal consumer

The list-valued inorder fold needs no monoid assumption on the generic combine. Its result can then feed the existing `Sequences.OrderedSummary.summary measure` for a caller-supplied `[Monoid M]`. Use its existing nil/append/singleton laws to prove the corresponding tree-fold equation with `combine l a r = l * measure a * r`, retaining multiplication order. A noncommutative word summary is the useful case; a commutative sum would fail to expose a reversed traversal or an unjustified child swap.

This is a composition between the new tree observation and an independently existing sequence library. It does not make every tree summary monoidal. In particular, two three-node trees can have the same inorder and different heights: a balanced root with two children has height 2, while the left chain has height 3. Even all three labels may be the same. Thus no function of inorder alone can recover general tree height.

### Malformed-cache boundary

Use the root-suggested three-node size-cache example. Both children are actual singleton trees, but their stored annotations are 0 and 2; the root annotation is 3. Then:

- The root annotation equals the actual total size 3.
- The local root equation also holds: `0 + 2 + 1 = 3`.
- Recursive validity fails at both children, whose actual sizes are 1.

This prevents replacing all-node validity by either root correctness or a local root equation. A smart constructor over the two corrupt children produces the same apparently correct root annotation and does not repair them. Annotation erasure still preserves inorder and shape. These are consequential distinctions to retain in the statements.

### Boundary of the maximum exercise

Chapter 4's maximum-cache exercise stores a raw `α` at each nonempty node but reads `Option α`, returning `none` on the empty tree. The generic family above stores and reads the same summary type `β`, with an explicit empty value. An optional-summary tree is a different raw representation from the source's raw-α cache. Do not force the exercise into this first unit by requiring `OrderBot α` or `Inhabited α`, or by broadening every cache into a new observation/encoding framework. Keep its source-compatible construction or explicit optional representation bridge as a later obligation. Chapter 5's actual endpoint-bottom assumption is a distinct, justified specialization and does not remove this boundary.

## 7. Resource interpretation: the smallest justified addition

The existing resource interface is already sufficient to instrument an actual local cached constructor. `Resources.Measured α C` is `α × C`; `bind` adds observations in execution order with only `[Add C]`, and its value types may occupy different universes. `CallCount.arguments_rule` exposes two argument observations plus the actual callback observation. No second executor or resource record is needed.

A prospective measured smart constructor must execute:

1. The actual root-cache read on the left child.
2. The actual root-cache read on the right child.
3. The supplied measured combine callback at those returned summaries and the node label.
4. The declared local constructor/entry charge, if that tariff assigns one.

For a left read result `L`, right read result `R`, measured callback `F`, and declared charge `c`, the exact Nat observation is

```text
L.cost + R.cost + (F L.value a R.value).cost + c,
```

with the chosen sequencing parentheses retained or justified by Nat associativity. The returned tree stores the actual callback value and keeps the supplied children. Reader value laws and callback value correctness connect that tree to `smartNode`; they do not bound any of these costs.

If both concrete cache reads have fixed charge `r` and the callback has a proved bound `K` on the reached summary values, the resulting bound is `2*r + K + c`. It is uniform in subtree sizes only because the reads inspect the root and the callback premise is explicit. Arithmetic on unbounded Nat summaries is not physically constant-time merely because a unit-cost source model treats it as primitive.

There is already a consequential nonconstant callback in the saved source. `Resources.ListReversal.appendRun leftSummary (a :: rightSummary)` is an actual measured append, and `appendRun_exact` gives exactly `(leftSummary ++ a :: rightSummary, leftSummary.length + 1)`. With two unit root reads and one unit local entry, the actual cached-node observation is therefore `leftSummary.length + 4`. It has the desired inorder value, also equal to `leftSummary ++ [a] ++ rightSummary`, but no constant callback bound for arbitrarily long summaries. This composes with an independently existing recursive computation and avoids inventing a synthetic expensive callback or a whole-fold executor. It is the chosen one-append callback, not a claimed exact execution of the book's displayed two-append direct inorder.

There are several distinct observations to preserve:

- Under a declared local-access model with each read charged once and one local constructor/entry charge, the overhead can be `3` beyond the callback. This is a model choice, not automatically the book's generated function-call count.
- The inspected `Leftist_Heap.thy` explicitly generates zero costs for its nonrecursive `mht` and `node` helpers and proves `T_mht_0`. Its recursive merge-only count must not acquire new positive helper charges by importing a differently named local-access result.
- `Resources.TreeFlattening.appendWithCost` counts copied cells; FDSA's append recursion counts its base entry as well. Their output equality is not their cost equality.
- An erasure theorem need not execute an erasure prepass. The existing `cachedFromTWithCost_erasure` is a useful example of a proof relating full measured results while the actual cached algorithm traverses its own carrier directly.

A whole-fold or whole-annotation measured traversal remains optional. A concrete later client such as AVL `debal2` may justify it, with separate call/callback recurrences and a stated evaluation order. The fact that a structural fold visits every node once does not make an arbitrary combining callback constant-time, nor make append-based inorder linear. Preserve that later obligation rather than making a broad unproved complexity claim in the first shared unit.

## 8. Placement, minimal imports and stopping boundary

A plausible source organization is a small `Applications/Trees` observation module over `Mathlib.Data.Tree.Basic`, followed by a small augmentation module over the same carrier. Exact public names and namespace are not frozen here. Use `BinaryTree` directly; avoid a second `Tree` alias or a new package. Keep the optional measured local constructor under the existing `Applications/Resources` domain, and independent sequence/summary or existing-queue compositions under `Examples`, consistent with ADR 0001/0010.

The pure fold and cache core require only the existing tree carrier, products, ordinary functions and propositions. Inorder uses standard List laws. Order/maximum and optional-default modules belong only to the specializations that need them. `Data/Tree/Traversable` and `Get` should not be imported merely because they are adjacent files if the new declarations do not use their capabilities. Likewise the generic pure core need not import a large probability, balancing, priority-queue or resource umbrella.

No mutation of the existing leaf-labelled libraries is justified by this proposal. A later queue bridge must preserve all current `LeftistQueue` contracts, and any optional resource composition must retain the original observations and assumptions. The chapter ledger must continue to track the actual Chapter 4 exercises and later balance/search algorithms separately; this common core is not their acceptance milestone.

The concrete gaps are sufficiently shared to justify considering the small pure fold/observation/cache family with the size, height, pair-fusion and ordered-summary cases. The maximum-cache representation bridge, a full measured fold, balance/heap/BST invariants, generic rotations, tree-enumeration/reconstruction and chapter-specific algorithms should remain outside that first proposal unless another concrete client makes them necessary. All implementation, matching-candidate validation and independent acceptance remain future work under root's existing workflow.
