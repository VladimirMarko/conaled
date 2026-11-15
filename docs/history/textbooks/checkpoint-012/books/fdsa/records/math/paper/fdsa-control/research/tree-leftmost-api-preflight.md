# Ordinary tree leftmost extraction: API and architecture preflight

Recorded 2026-11-02. **Read-only preparation for possible FDSA-XT08; no scope,
base, names, tariff or implementation is frozen.** No chapter is activated or
accepted. Root's Chapter 1 gate remains the sole authorized validation. This
report is not an independent Standards/Spec review or a compiler result.

Only this new report was written. No worktree, repository source, index, ref,
cache, requirement, prior report or remote artifact was changed. Project reads
used the pinned Nix shell; no Lean/Lake invocation, checker or project hash
helper ran. Ordinary byte hashing identifies inspected inputs and this report.

## 1. Recommendation and genuine shared gap

There is a small source-justified gap: **extract the first inorder label and
return the actual ordinary residual `BinaryTree`**, preserving arbitrary full
labels. `Tree_Map` really reuses `Tree_Set.split_min`; a key-only minimum or an
unrelated tree with the same set is insufficient. The operation should remain
separate from its ordered-key consequences and resource observations.

The scoped existing-source search did not find this operation on ordinary
`BinaryTree`. Mathlib's `Ordnode.splitMin` and Std's internal `minView` are real
minimum-removal operations, but use other cached/balanced carriers and rebuilders.
They do not supply the literal ordinary residual or its execution recurrence.
Existing conaled priority-list/heap removals likewise have different algorithms
and observations. Adding a tiny ordinary extractor would therefore not duplicate
an existing ordinary-tree operation.

The useful bounded value surface is the literal selected-left recursion,
failure exactly on nil, the one-way actual-result head/inorder law, arbitrary
label-map transport, one-node decrement and residual-height nonincrease. Existing
`Trees.Ordered` and list `Pairwise` supply the ordered consequences. A direct
arbitrary-relation residual-preservation lemma is feasible and weaker than the
minimum theorem; it needs no new hierarchy.

If resource work is selected, one actual measured recursion with one Nat
invocation observation and transparent value/count projections is sufficient.
There is no need for a second visit count, separately recursive analytical
counter, generic rebuilder executor, comparison machine, or new tree carrier.
The empty-input observation must be chosen explicitly at freeze; it is absent
from the ordinary source. Section 6 assesses a convention without selecting it.

## 2. Exact input identities and reading boundary

The applicable `AGENTS.md`, architectural-quality/domain guidance, glossary,
ADR index, ADR 0001, development-environment instructions and example-driven
statement-review guidance were read. This remains planning within the existing
workflow, not another implementation or acceptance loop.

The **complete stopped source preflight** was read:

- `research/tree-leftmost-source-preflight.md`: 30,462 bytes, 392 lines,
  SHA-256 `82fe82030581dc888d2165a0c7a236ec316a83b66906b9d7fcf32f6af18b3185`.
- Its pinned manuscript, Isabelle source, license and AFP receipts are retained
  there. This API pass additionally read all 119 lines of `Tree_Set.thy` and all
  58 lines of `Tree_Map.thy`, and the relevant C05/C06 inventory rows.
- Source `Tree_Set.thy:35–37,76–79` is the ordinary operation/head law;
  `Tree_Map.thy:5–8,23–28,41–43` is the literal full-pair reuse. The p.82
  reference to §5.6.4 remains the existing erratum: §5.2, p.61 is intended.

Pinned installed dependencies were read without download or modification:

| Dependency | Actual pin / location |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0`; installed source under `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/` |
| Mathlib | Actual dependency HEAD `56a005855ea17e0b0958f73ec801ae140b0a1679`, matching `lake-manifest.json`; under `conaled/.lake/packages/mathlib/` |
| Batteries | Actual dependency HEAD `66e469188fe07963e5cf666c7d4433f45b8131c5`, matching the manifest; under `conaled/.lake/packages/batteries/` |

The ordinary tree files are **`Mathlib/Data/Tree/Basic.lean` and
`Mathlib/Data/Tree/Get.lean`**, despite their namespace being `BinaryTree`.
There is no `Mathlib/Data/BinaryTree/` directory at this pin. The initial lookup
of that nonexistent directory was corrected; it was not evidence of a missing
carrier or missing dependency.

Retained project sources were read with `git show` through the pinned shell,
without restoring removed worktrees:

| Saved source | Exact commit | Bytes / lines / SHA-256 |
| --- | --- | --- |
| `Applications/Trees/Observations.lean` | XT01 `64c6b777d828ecfe83234fc2aed94600a1f24297` | 4,119 / 107 / `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Cached.lean` | Same XT01 | 5,668 / 135 / `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| `Applications/Trees/Ordered.lean` | XT07 `66eae34815a177c6b4bf5120e05202ebb8876c91` | 5,817 / 126 / `26549e623acdce3ac29e3fdd30858eb068c1bf7cd5f223468bbcbb30ecffbe66` |
| `Applications/Resources/TreeSearch.lean` | XS01 `863aedb924e922ac40747c0ef299701a7785488e` | 22,768 / 501 / `1924f95f0f4c912cdf4ab0661c8ef182f709b9bd82e7af67d1ae5b93df5dc7f6` |

The first three files were read completely in this pass. The saved XS01
operation/projection prefix was reread as an architectural comparison; its
complete source had already been read in the immediately preceding authoring
assignment. All these inherited drafts remain unaccepted. Existing
`Examples/OrderedTrees.lean` fixture definitions and public theorem names were
also inspected at XT07; its namespace is `OrderedTreeExamples`.

## 3. Existing APIs: reuse and non-substitutable alternatives

### 3.1 Canonical ordinary carrier

At the pinned `Mathlib/Data/Tree/Basic.lean`:

```lean
inductive BinaryTree.{u} (α : Type u) : Type u
  | nil : BinaryTree α
  | node (value : α) (left right : BinaryTree α) : BinaryTree α

BinaryTree.map {β} (f : α → β) : BinaryTree α → BinaryTree β
BinaryTree.numNodes : BinaryTree α → Nat
BinaryTree.height : BinaryTree α → Nat
BinaryTree.height_le_numNodes (t : BinaryTree α) : t.height ≤ t.numNodes
```

These are at lines 31–34, 79–81, 108–110, 128–130 and 143–147 respectively.
`numLeaves_eq_numNodes_succ` is at 136. `left`/`right` at 151/161 are total
child observations, not destructive extraction operations. `BinaryTree` itself
is inhabited by nil even when α is empty; no instance on α is needed.

The entire Basic/Get files, declarations of the other two BinaryTree namespace
files (Traversable and Catalan enumeration), scoped Mathlib/Batteries searches,
and retained XT07 Applications/Examples names were inspected. No ordinary
extractor was found. `BinaryTree.indexOf`/`get` in `Data/Tree/Get.lean:33–39,51–55`
produce a path/found value and never a residual tree. Building a path or list
and then separately deleting is not the literal one-pass recurrence.

### 3.2 Existing project observations and order laws

The exact useful existing names and assumptions are:

| Existing declaration | Usable statement / role |
| --- | --- |
| `Trees.inorder_node a l r` | `inorder (.node a l r) = inorder l ++ (a :: inorder r)`. |
| `Trees.inorder_length t` | `(inorder t).length = t.numNodes`. |
| `Trees.inorder_map f t` | `inorder (t.map f) = (inorder t).map f`, with independent label universes. |
| `Trees.numNodes_map f t`, `Trees.height_map f t` | Exact shape-observation transport, no injectivity premise. |
| `Trees.ordered_node R a l r` | Recursive child validity and all-left-to-root/all-root-to-right bounds. No relation law is built into the definition. |
| `Trees.ordered_of_pairwise_inorder R t h` | Pairwise inorder implies structural Ordered for any relation R. |
| `Trees.pairwise_inorder_of_ordered R hR t h` | Structural Ordered implies Pairwise inorder when `hR : Transitive R`. |
| `Trees.ordered_key_iff_pairwise key t` | Under `[Preorder κ]`, strict key Ordered iff the mapped key list is Pairwise `<`; no payload order or key decision. |
| `Trees.ordered_key_nodup key t h` | Strict key Ordered gives Nodup of the key observation. |
| `Trees.ordered_map_key_iff key key' f hf t` | Under `[LT κ]` and actual key preservation `hf`, arbitrary payload-map transport; no global key injectivity. |

`Trees.fold` supplies the existing inorder observation. It is not the desired
extractor executor: its displayed strict recurrence computes both child folds.
Making a final combine choose one child does not establish one-path execution
or its cost. Function-valued fold constructions would introduce an unnecessary
construction/invocation distinction here.

### 3.3 Existing minimum extraction on other representations

| Actual API inspected | Why it is not a direct source replacement |
| --- | --- |
| `Ordnode.splitMin' : Ordnode α → α → Ordnode α → α × Ordnode α`, `Ordnode.splitMin : Ordnode α → Option (α × Ordnode α)`; `Mathlib/Data/Ordmap/Ordnode.lean:477–491` | Ordnode carries a cached size at each node. Recursive extraction rebuilds with **`balanceR`**, not plain `BinaryTree.node`. The source file explicitly distinguishes its balancing preconditions. A conversion into/out of this representation would need a new proof and work correspondence and may change residual shape. |
| `Ordnode.splitMin_eq` at `Invariants.lean:499–502` | It identifies its own helper with `findMin'` plus `eraseMin` on Ordnode. It does not identify an ordinary BinaryTree residual. |
| `Std.DTreeMap.Internal.Impl.minView k v l r hl hr hlr`, `Internal/Operations.lean:73–83` | Requires `l.Balanced`, `r.Balanced`, `BalancedAtRoot l.size r.size`; returns a dependent `View α β (l.size+r.size)` and uses `balanceRErase`. The carrier is cached `Impl`, not BinaryTree. |
| `Std.DTreeMap.Internal.Impl.toListModel_minView`, `Internal/WF/Lemmas.lean:118–125` | A genuine full-entry head/list theorem, but for the above balance-constrained operation. Its induction is a useful proof pattern, not a theorem transferable without a representation/algorithm bridge. |
| `Std.TreeMap.minEntry?`, `Std.TreeMap.minEntry`; `Std/Data/TreeMap/Basic.lean:187–192` | Optional and nonempty-proof minimum observers on a size-balanced map; neither returns the ordinary residual. The `!` alternative requires Inhabited and is unnecessary here. |
| `Lean.RBNode.min`, `Lean/Data/RBMap.lean:37–40` | Correctly stops before a left leaf, but returns only an optional dependent entry on a colored RBNode carrier, no residual. |
| Existing `Search.PrioritySearchQueue.takeMin`, `Applications/Search/PrioritySearchQueue.lean:162–181` | Scans a list and compares priorities, with `[LE π] [DecidableLE π]`; its occurrence law is a permutation. It does not preserve a binary-tree left path. |
| Existing `Search.LeftistQueue.deleteQ`, `Applications/Search/LeftistQueue.lean:151–153` | Removes a heap root and combines both children on its own ranked heap carrier. Heap-minimum semantics is distinct from first inorder position. |

The pinned Std `minView!` at Operations:89–94 is expressly a fallback that may
panic when its preconditions fail. It is not a route around these differences.
No alternative should be relabelled as the ordinary source extractor solely
because it can return a minimum under an invariant.

## 4. Proposed minimal contracts and proof routes

The symbol `extract?` below denotes the **proposed actual ordinary operation**,
not an existing declaration, assumed oracle, or new abstract interface. These
are proposed theorem shapes only; no Lean definition has been authored.

### 4.1 Operation and domain

Use `Option (α × BinaryTree α)` for arbitrary `α : Type u`:

```lean
extract? .nil = none
extract? (.node a .nil r) = some (a, r)
extract? (.node a l r) =
  (extract? l).map (fun (m, l') => (m, .node a l' r))  -- only when l ≠ .nil
```

The implementation should pattern-match on the left constructor, not demand a
`DecidableEq α` merely to test emptiness. Structural recursion goes into the
actual nonempty left child. The residual on return is the actual recursive
residual under the same ancestor label and untouched right child. An Option
map can cover the logically unreachable recursive none branch without inventing
a default label or fallback tree.

Prove `extract? t = none ↔ t = .nil`, or equivalently explicit success for every
nonempty raw input. Successful-return hypotheses then imply the source's
nonempty domain; no redundant ordering premise is introduced. A proof-domain
worker is possible, but need not be exported as a second operation just to
avoid the ordinary Option boundary. `BinaryTree Empty` and
`BinaryTree (Nat × Empty)` still support the total failure result.

### 4.2 Exact raw observation is one-way

For the actual successful result:

```lean
extract? t = some (m, t') → m :: Trees.inorder t' = Trees.inorder t
```

**Do not turn this implication into an equivalence.** The same tail list can
have many tree shapes; an arbitrary t' satisfying that list equation is not
therefore the actual returned residual. Literal branch equations, not an
extensional set/list specification alone, determine the executable operation.

Proof route: induct on t, split its left shape, and in the recursive branch
use successful extraction of the child and its induction hypothesis. Expand
`Trees.inorder_node` and use the already-pinned `List.cons_append` and
`List.append_assoc`. The actual child Option success follows from the parent
success or the nonempty-domain law. No sorting or equality decision is used.

Immediate consequences need no new traversal:

- m belongs to the original inorder; each residual label belongs to it.
- `(Trees.inorder t).head? = some m` and
  `(Trees.inorder t).tail = Trees.inorder t'`.
- `t'.numNodes + 1 = t.numNodes`, by `congrArg List.length` and
  `Trees.inorder_length`; this counts occurrences, not set cardinality.
- An exact input-inorder equality can transport the **observed** optional pair
  `(m,inorder t')`. It does not imply equality of residual trees or work.

The source-needed `t'.height ≤ t.height` is a separate structural induction:
base residual r is below the parent height; recursive reconstruction uses the
induction inequality for the left residual and monotonicity of `max` with the
unchanged right height. This supports the extraction part of C05-013 without
claiming the whole deletion-height theorem. `BinaryTree.height_le_numNodes`
then remains available without a new tree-shape unit.

### 4.3 Arbitrary label transport and full semantic pairs

For `f : α → β`, with independent universes, the actual operation should satisfy:

```lean
extract? (t.map f) =
  (extract? t).map (fun (m, t') => (f m, t'.map f))
```

A tree/left-shape induction is enough; no injectivity, ordering, inhabitation,
key equality or decision instance is needed. If an actual measured executor is
selected, prove the stronger whole-pair transport with its Nat observation
unchanged, then derive this value law. This is not a cost claim for executing
a separate preprocessing `t.map f` traversal.

The Chapter 6 specialization is α = κ × β with semantic value β arbitrary in
an independent universe. The output must contain the entire `(key,value)`.
Ordinary `Prod.fst` key projection and an outer metadata projection are distinct
maps: stripping an annotation does not justify dropping a semantic map value.

For an observation-level map client, pinned `List.lookup` in
`Init/Data/List/Basic.lean:1826–1835` needs only `[BEq κ]`; its exact cons law is
`((k,v)::xs).lookup q = match q == k with | true => some v | false => xs.lookup q`.
The raw head/inorder theorem therefore gives that Boolean equation for the
original and residual lists without an equality law. At the extracted key,
`List.lookup_cons_self` (`Init/Data/List/Find.lean:1349`) needs only `[ReflBEq κ]`
to return its payload, with no ordering premise. Identifying Boolean tests with
mathematical equality needs a lawful or explicitly local equality observation;
concluding that lookup of the removed key in the residual is none additionally
needs the strict-key absence fact. No BEq assumption belongs on extraction
itself. A full map/delete implementation or new ADT interface is not needed for
this client.

### 4.4 Ordered residual versus leastness

A direct structural proof can preserve `Trees.Ordered R` for **any** relation R:

```lean
Trees.Ordered R t → extract? t = some (m,t') → Trees.Ordered R t'
```

At a left-empty root, the result is the already ordered right child. At an
ancestor, the actual left residual is ordered by induction; its labels are a
subset of the old left inorder by the raw equation, so the old root bounds
still apply. The unchanged right child and bounds are reused. No transitivity
is required for this preservation claim. This is a thin theorem about this
operation, not a generic preservation-family record.

Leastness is stronger. Under `hR : Transitive R` and `Ordered R t`, existing
`pairwise_inorder_of_ordered R hR t` plus the head equation gives
`∀ b ∈ inorder t', R m b` and Pairwise of the residual. Alternatively a supplied
Pairwise inorder premise gives those consequences directly without assuming
transitivity. Exact pinned helpers are `List.pairwise_cons` at
`Init/Data/List/Basic.lean:1378`, `List.rel_of_pairwise_cons` and
`List.Pairwise.of_cons` at `Init/Data/List/Pairwise.lean:57–61`.

For source keys, `[Preorder κ]` and
`Trees.Ordered (fun a b => key a < key b) t` suffice. Reuse
`ordered_key_iff_pairwise` or the generic transitive route. It follows that
`key m < key b` for every residual entry b. Consequently:

- `key m` is in the original key set and is below every original key;
- the residual key set is exactly the original key set minus `key m`;
- the residual retains strict key Ordered, and cannot contain another entry
  with the removed key.

These are proposition-level statements without global key decidability.
`IsLeast` itself is the existing `a ∈ s ∧ a ∈ lowerBounds s`
(`Mathlib/Order/Bounds/Defs.lean:48–49`, only LE at definition level); the
Preorder specialization above supplies reflexivity and strict-to-weak comparison.
No linearity, payload order, global key injectivity, comparator, or full-payload
equality decision is required for these consequences.

On a malformed tree, first inorder need not be the numeric minimum. On raw
duplicate labels/keys, one occurrence is removed but the same label/key can
remain. Under merely `Ordered R`, without transitivity, the extracted label
need not relate to all remaining labels: existing
`OrderedTreeExamples.next_ordered`/`next_not_pairwise` give that boundary.

## 5. Smallest source dependencies and placement options

| Selected content | Actual reusable dependency, not a new acceptance prerequisite |
| --- | --- |
| Raw operation, inorder/map/size/height laws | `Applications.Trees.Observations` from XT01 plus canonical BinaryTree/list APIs. |
| Structural Ordered and strict-key consequences | `Applications.Trees.Ordered` from XT07; it already imports Observations and the needed list sort interfaces. |
| Actual Nat invocation observation | Existing `Applications.Resources.CallCount`, hence `Measured`, `Resources.bind`, `Resources.pure` and `CallCount.tick`. |
| Optional `IsLeast` packaging | Existing `Mathlib.Order.Bounds.Defs`; no need to import a separate finite minimum algorithm. |
| Existing connected fixtures | `Examples.OrderedTrees` at XT07, through its actual `OrderedTreeExamples` namespace. |

Raw-only value work could start from the retained XT01 tip
`64c6b777d828ecfe83234fc2aed94600a1f24297`. The smallest already-retained tree
tip containing the proposed ordered contracts is XT07
`66eae34815a177c6b4bf5120e05202ebb8876c91`; its history also contains rotations.
That history is a fact, not a requirement to import rotation modules into the
extractor. The newer XS01 tip is unnecessary unless a separately justified
search-specific client is selected. No XT02–XT05, XA01, XH01, merge, or new
ADT dependency is needed for the ordinary extractor.

These are source-dependency observations, **not a chosen authoring base or an
integration authorization**. The retained tree tips inherit earlier unaccepted
Chapter 1 material. Root must choose any later isolated base and reconcile the
accepted C1 repair through the existing workflow; this report does neither.
The initial c80eec9 Chapter 2 prefix remains unchanged and this possible unit
cannot become its prerequisite.

A value-only unit could use an ordinary `Applications/Trees/Leftmost.lean`.
If the future scope includes actual counts, the smaller implementation pattern
is the saved XS01 idiom: a single `Resources.TreeLeftmost.run` returning
`Measured (Option (α × BinaryTree α)) Nat`, with transparent optional-result and
entry-count projections. That suggested path/namespace is not frozen. Separate
semantic theorems continue to use the existing tree observations. Do not author
a second pure recursive extractor and a third recursive cost function merely
to restate this one execution.

## 6. Resource observations: necessary boundary and a possible convention

The source preflight establishes no ordinary generated `T_split_min` theorem.
Its exact nonempty self-call recurrence is reconstructed from Chapter 1's
explicit invocation convention. No comparison occurs; constructors, shape
inspection and pair/Option projections are uncharged in that chosen model.

If selected, an actual measured run must perform these branches:

| Input | Actual value/control | Nonempty source invocation count |
| --- | --- | --- |
| `.node a .nil r` | Return `some (a,r)` without visiting r or calling nil. | 1 |
| `.node a l r`, l nonempty | Run only l; rebuild using the actual returned left residual; return the actual pair. | `entries l + 1` |
| `.nil` | Total Lean adaptation returns none. | **No source equation; choose and label an extension.** |

The existing exact composition is enough. `CallCount.tick r = (r.1,r.2+1)`;
`Resources.bind r f` invokes f on r.1 and adds the observations. A recursive
branch can tick the bind of the actual left run with the zero-cost Option map
that rebuilds `BinaryTree.node a l' r`. The base uses tick of `pure (some (a,r))`.
This is one execution, with no right traversal or independent cost oracle.
Qualify `Resources.bind`/`Resources.pure` in source proof scripts, as their short
names can also denote standard operations.

For a total resource API, **a possible and coherent proposal** is `(none,1)` at
nil, consistent with charging every entered Lean run once. It is not yet selected
and is not attributed to the unspecified HOL empty input. Choosing `(none,0)`
would be another declared extension and would change only empty-run statements.
No public tariff parameter is justified merely to postpone this choice. If
resource work is deferred, the value proofs require no empty-cost decision.

On nonempty inputs either extension yields `1 ≤ entries t ≤ t.height`, hence
`entries t ≤ t.numNodes`. The proof follows the actual left recursion: left
height is at most the parent's max; the base has one node. With the proposed
one-charge nil extension, universal bounds become `1 ≤ entries t` and
`entries t ≤ t.height+1`; the sharper bound requires successful/nonempty input.
No independent left-spine statistic or second visited-node observation is
needed to expose these direct equations and bounds.

Calling the left child unconditionally and interpreting a none result as
"take this root" yields the same value but one extra charged invocation on
every nonempty input under a positive nil charge. `TreeSearch.run (fun _ => .lt)`
also reaches nil and returns no residual. Neither gives this source count.
The retained query executor is an architectural example of measured paths,
not a cost-correct implementation of extraction.

Left chains attain the height bound; nonempty right chains cost 1 regardless
of height. Thus there is no lower bound proportional to each input's height,
and no unconditional logarithmic bound. Orderedness alone does not balance a
tree. A later balanced representation needs its own height and rebuilder work
correspondence. These counts do not measure allocation, comparisons inside an
unrelated callback, stack space, Lean runtime or a compiler realization.

## 7. Connected uses and failure boundaries

These expected clients are evidence for the proposed shared interface, not a
new frozen case list or checked Lean results from this task. The independent
case author is preparing the separate case report.

- **Raw symbolic splice:** for arbitrary labels and right subtree r, extraction
  from `.node a .nil r` returns the exact r. One parent above it returns that
  actual r as the parent's new left subtree. This distinguishes the source
  residual from an arbitrary reconstruction of the tail list.
- **Existing printed set tree:** `OrderedTreeExamples.printedTree` has inorder
  `[2,3,5,6,8,9]`. Extraction returns 2; its residual root remains 6, the left
  child remains 3 with nil left and singleton 5 right, and the right subtree 9
  with left singleton 8 is unchanged. The nonempty invocation count is 3.
  Existing `printed_ordered` discharges the strict minimum consequence.
- **Actual semantic-map successor body:** `taggedTree` is the existing tree
  of `(0,false),(1,true),(2,false)`. Its right child is the singleton `(2,false)`.
  Bind extraction of that actual right child to plain root reconstruction with
  the old left child: the result has root `(2,false)`, left `(0,false)`, and nil
  right, with extraction subcost 1 under the proposed convention. This is the
  source's replacement body, not a complete delete algorithm; the old true
  payload must not survive. Extracting taggedTree itself is a different run
  returning `(0,false)` with count 2.
- **Label transport and universes:** use `discardTag` and its actual key law,
  then an arbitrary cross-universe map. Whole-run transport should preserve
  both the mapped residual and count without global injectivity. A separate
  preprocessing map traversal remains outside this cost.
- **Duplicates:** existing `sameKeyRecords` returns `(1,10)` and the singleton
  `(1,20)`. Full entries are distinct but key 1 remains. Mapping keys gives an
  identical-label duplicate case. This refutes raw set-difference or local
  unique-key conclusions from mere payload distinctness.
- **Unordered/nontransitive boundaries:** `three 2 0 1` extracts 2 although 0
  is least. If arbitrary-R preservation is exposed, existing `next` on
  `three 0 1 2` preserves residual Ordered yet `next 0 2` is false; transitivity
  was genuinely needed for the all-tail relation consequence.
- **Shape/work distinction:** strict left and right chains of n positive nodes
  can have the same inorder and height but costs n and 1 and different residual
  shapes. This prevents transferring work or returned-tree equality from inorder.
- **Empty values:** empty input works at `Empty` and at `Nat × Empty`; only the
  explicitly chosen empty observation is asserted. No successful empty-payload
  witness or default is postulated.

Existing `Trees.Cached.erase` is `t.map Prod.fst`, so the raw map theorem can
relate erased observations. It does **not** preserve `Cached.Valid`: deleting
a left child while retaining an ancestor's old height/size annotation can leave
that annotation stale. `Cached.smartNode_valid_iff` and `erase_smartNode` are
real reuse for a later cache-repair algorithm, not proof that ordinary full-pair
rebuilding already repairs caches. The map pair's semantic value is also not
such a cache. Existing XT01 positive smart-node costs are a distinct tariff.

The source preflight's balanced-domain distinctions remain mandatory: interval
smart rebuilding; red-black old-color-dependent baldL; 2–3 completeness and
underflow tags; rightmost AVL split_max and its different pair order; and
join-based actual helper work. A join locale with only raw set conservation
does not imply this raw head/inorder equation or one-occurrence decrement.
The retained AFP StronglyJoinable generated timing source is for that different
join algorithm and cannot supply ordinary-node timing for free.

## 8. Remaining proof/API risks, provenance and stop boundary

No mathematical obstruction was found to this bounded ordinary operation.
The main proof routes use structural induction, exact Option cases, current
inorder/Pairwise laws and elementary Nat/max inequalities. Minimal assumptions
are satisfiable on empty, arbitrary-payload and ordinary strict-key examples.
The algorithm does not compare keys, so no comparator law or decision instance
is necessary for it or its raw transport/resource recurrences.

No proposed Lean code was elaborated. In particular, nested left-pattern
termination, Option-map equation normalization, independent-universe inference
and proof-script simplification would still require actual compiler validation
on a later immutable candidate. These are untested implementation obligations,
not observed errors or reasons to weaken the semantic statements. Future cases
must consume the actual exported operations and theorems rather than an imagined
API or independently computed pair relabelled as an execution result.

Exact source licenses remain attached to their origins: Mathlib and Lean source
files retain their Apache 2.0 notices; source-derived Isabelle work must retain
the complete BSD notice identified in the stopped source report
(`ISABELLE-COPYRIGHT`, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`).
No manuscript copying, download, dependency change or new upstream source
campaign occurred. The existing complete source preflight owns the detailed
later-family pins and licenses; this report does not reinterpret them.

The possible extractor would support C05-006/007, the helper part of C05-013,
and C06-047. Whole deletion, direct recursive exercise proofs, complete set/map
laws, interval algorithms, balanced constructors, logarithmic bounds and later
join/set work remain original queued obligations. Nothing here changes the
initial Chapter 2 prefix, any frozen scope, active gate or acceptance condition.
After complete report readback, all writes stop; root owns any later decision,
requirements, implementation, review, durable checkpoint and upload.
