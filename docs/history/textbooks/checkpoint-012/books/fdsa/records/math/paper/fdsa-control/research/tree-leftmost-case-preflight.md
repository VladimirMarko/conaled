# Ordinary leftmost extraction: independent case preflight

Status: **bounded source preparation, 2026-11-02; complete preflight with stopped author handoff**. The ordinary operation, observation model, source base, public names and file scope are not frozen. This report does not release implementation, activate a chapter, certify a proof or start an additional review loop. Only this report is owned by this task.

## 1. Independent conclusion

The smallest useful common operation returns the **actual first inorder entry and the actual residual binary tree**. The original Chapter 6 map implementation calls the very same polymorphic Chapter 5 operation on full `(key,value)` labels. This is a concrete shared use, independent of whether a later balanced representation also descends along a left spine.

The cases below distinguish that operation from four tempting replacements: finding only a key, scanning for a global minimum on a malformed raw tree, constructing an arbitrary tree with the right remaining set or list, and descending into the terminal empty child. Each replacement can satisfy some weaker observation while changing the source behavior or its declared call count.

The proposed compact evidence consists of the exact base and one-parent rebuilding cases; the retained printed tree; the retained semantic-pair tree and its successor-replacement body; the retained duplicate-key records; one malformed specialization of the existing three-node fixture; and strict left/right chain families. An arbitrary-relation example and a stale-cache example are conditional boundary evidence for stronger claims, not a request to implement extra abstractions.

The calculations were derived from the literal source equations before the completed source report was read. A small ephemeral Python recurrence subsequently evaluated the chosen finite trees, including every returned residual shape and the nonempty invocation counts. It rejected empty input as outside the source-defined domain. It created no saved program or proof artifact. These calculations are mathematical expectations, not Lean or Isabelle validation.

## 2. Exact inputs and reading limits

The source context is the retained July 27, 2026 manuscript, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`, and Isabelle companion revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`. The source report records the companion's BSD notice and the separate later AFP timing provenance. No remote retrieval or manuscript redistribution was performed here.

The retained ordinary tree source was inspected at exact Git commit `66eae34815a177c6b4bf5120e05202ebb8876c91`. This is an inspection reference, **not a selected XT08 implementation base**, and its inherited tree drafts are not thereby accepted. Project Git reads ran through pinned Nix in `conaled-ch01-cost-models`, with `GIT_OPTIONAL_LOCKS=0`; no Git mutation occurred.

### Control and primary-source inputs

| Input | Bytes / lines | Ordinary SHA-256 | Reading scope |
|---|---:|---|---|
| `fdsa-control/tickets/FDSA-XT08.md` | 1,523 / 26 | `0b4a2402004d5c9689297d0c473bf91c3b33894fcbd089dffd38da73d6122022` | Complete initial assignment/status record. |
| `fdsa-control/research/tree-leftmost-source-preflight.md` | 30,462 / 392 | `82fe82030581dc888d2165a0c7a236ec316a83b66906b9d7fcf32f6af18b3185` | Complete stopped source report, read after independent derivation. |
| `fdsa-control/research/tree-leftmost-api-preflight.md` | 30,485 / 485 | `2cc8c6f1f9802a85cbc64ffbbec5285edccf154e7d8bb75807534550e63db038` | Complete stopped API report, read before final correspondence and readback. |
| `fdsa-control/research/tree-order-case-preflight.md` | 12,227 / 210 | `e5c680ecdd0430f71e96f7149ebc64bdd4d834f7b0272129f0976bac4c537ffe` | Retained case context, including raw/key-order and payload distinctions. Historical validation handles are not current-status evidence. |
| `book-source/Tree_Set.thy` | 3,801 / 119 | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` | Complete source, especially equations 35–37, deletion caller 39–45 and `split_minD` 76–79. |
| `book-source/Tree_Map.thy` | 2,028 / 58 | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` | Complete source, including actual `Tree_Set` import and full-pair successor use. |
| `book-source/chapter05.txt` | 32,466 / 605 | `b00475b2893cf76a66a5c164a63ee99e065772fffa7ae56054359b278c5c4b1e` | Printed pp.61–62: replacing deletion, ordinary extraction and the height claim. |
| `book-source/chapter06.txt` | 11,842 / 233 | `b50500309106a77b094aebbc807b5b6979feb72d03bb443f2fd2785ee5dc3681` | Printed pp.82–83: full-pair deletion body, association-list refinement and the erroneous cross-reference. |
| `book-source/Set2_Join.thy` | 14,764 / 376 | `15edbd8a0b1b00633a15d9d1ccffb92d60ca9b313ba3b2f3bf4313af79f57d1b` | Locale assumptions, `split_min` and `join2` contracts; no claim to have reread the entire theory. |

The original Chapter 5 inventory's extraction/deletion/height rows and the matching extraction rows in Chapters 6–10 were read. The initial large Chapter 5 display was truncated in unrelated later material; this report does not count that as a new full inventory read. The completed source report supplies the detailed later-family correspondence. Exact inventory identities are:

| File under `fdsa-control/research/` | Bytes / lines | Ordinary SHA-256 |
|---|---:|---|
| `chapter05-obligations.md` | 45,177 / 372 | `f512f6b3723e8e036e9292aab985e93d15b2bf49b1c2c6dff79b3e6911ffcaad` |
| `chapter06-obligations.md` | 36,661 / 321 | `078bb9759e7bfd9245cfff69443f7722ae4b49295da61f311689da874bb20146` |
| `chapter07-obligations.md` | 33,696 / 336 | `8e9aa9dda75c04a4c6a09a40feead8a2ff8d7ebc64c7dd47c0344921a6f41bde` |
| `chapter08-obligations.md` | 40,867 / 422 | `16e26a46452d06401e1f50317fb8d7e3ad4a341a2070870b07c7014f1b2e07e1` |
| `chapter09-obligations.md` | 45,359 / 423 | `6ade1fd1a470c64d613212098e311d2e0189f62bd82045dbb2f8f4387f426285` |
| `chapter10-obligations.md` | 49,723 / 487 | `f3703190c2c5591a8b8685e88205652ca412e90fedb3b467ceb5d4bfd55eac0b` |

### Actual retained APIs and fixtures at the inspection reference

| Full project path | Bytes / lines | Ordinary SHA-256 | Reading scope |
|---|---:|---|---|
| `Applications/Trees/Observations.lean` | 4,119 / 107 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` | Complete. |
| `Applications/Trees/Ordered.lean` | 5,817 / 126 | `26549e623acdce3ac29e3fdd30858eb068c1bf7cd5f223468bbcbb30ecffbe66` | Complete. |
| `Examples/OrderedTrees.lean` | 17,154 / 386 | `e7715af3106bfa32983d424abc87ee75c70c8e362bb6d9e27de3ee7a253793d1` | Complete. |
| `Examples/TreeCache.lean` | 16,307 / 363 | `ae78e0f515ba11c9f5348533624df49da59d98887689a16c16a35c3f880fd754` | Lines 1–195: actual sample/annotation definitions, repeated-tree fixtures and Empty observations. |
| `Examples/TreeRotations.lean` | 13,905 / 283 | `9c99d5169e48e2ea0940361cb2b9fc5e5f764b947e6e4796fc279d3b8f33c4f2` | Lines 1–85: actual singleton, arbitrary-label fixtures and partial-operation boundaries. |

`Trees.inorder` is an ordered list of **all** node-label occurrences, not a set. Its relevant actual laws are `inorder_nil`, `inorder_node`, `inorder_length`, and `inorder_map`. Canonical size/height and label mapping remain on `BinaryTree`; `Trees.height_map` and `numNodes_map` are available. The constructor is `BinaryTree.node label left right`.

`Trees.Ordered R` is the recursive two-subtree/bounds predicate. The exact existing connections are `ordered_of_pairwise_inorder`, `pairwise_inorder_of_ordered` with `Transitive R`, `ordered_key_iff_pairwise` and `ordered_key_nodup` with a key `Preorder`, and `ordered_map_key_iff` for exact key preservation. None gives an extractor or a residual tree merely from a list observation.

## 3. Source operation and domain before any implementation choice

For compact mathematical notation only, write `E` for the empty tree, `N(l,a,r)` for a node, `L(a)=N(E,a,E)` for a singleton, and `I(t)` for `Trees.inorder t`. Thus `N(l,a,r)` is Lean's `.node a l r`. Write `X(t)=(m,t')` for the source-defined extraction on a **nonempty** tree; `X` is not a proposed public Lean name.

The two literal behaviors are:

1. `X(N(E,a,r)) = (a,r)` for arbitrary label `a` and arbitrary right subtree `r`.
2. If `l` is nonempty and `X(l)=(m,l')`, then `X(N(l,a,r))=(m,N(l',a,r))`.

The second equation uses the **returned** `l'`. The base promotes the original right child, even if that child is nonempty and large. No key comparison, payload equality, inorder construction, minimum scan, or visit to the right subtree is part of this recurrence. The empty-child test can be a constructor match, so no `DecidableEq α` is needed.

The HOL empty case has no supplied equation. A possible total Lean result is `Option (α × BinaryTree α)`, with none on `E`; another faithful interface uses an explicit nonempty input. Both require a bridge to the actual equations above. A total pair-valued operation on every `BinaryTree Empty` cannot return an `Empty` label. Adding a default or an `Inhabited α` assumption would hide this mismatch.

For an Option choice, the useful domain expectations are `none iff input = E` and success on every nonempty **raw** tree, without a BST premise. The existing `TreeCacheExamples.empty_tree` proves that every `BinaryTree Empty` is empty. Likewise every `BinaryTree (Nat × Empty)` is empty: the key type remains inhabited, but no semantic map entry exists. These boundaries are not tests of an impossible successful input.

## 4. General consequences and their exact hypothesis boundaries

### Raw observations

On every source-defined success `X(t)=(m,t')`:

- `m :: I(t') = I(t)`. This is the source's `split_minD`, preserving order and repeated occurrences.
- Consequently the returned entry belongs to the original inorder list, the residual list is its tail, and the input label set is `{m} ∪ labels(t')`.
- By the existing `Trees.inorder_length`, `t'.numNodes + 1 = t.numNodes`. This counts an occurrence; it is not a raw set-cardinality decrement.
- The actual structural recurrence gives `t'.height ≤ t.height`. Inorder equality alone would not prove this height claim.

None of these requires order, key equality, payload equality, inhabitance, or a comparator. The exact residual-tree equations are stronger operational statements than the list theorem. Many trees have the same inorder list; a future implementation must prove correspondence to the structural recurrence as well as the list observation.

### Ordered minimum and removal

Let `key : α → κ`, with only the key-side assumptions needed by the existing strict-order bridge. Under `[Preorder κ]` and `Trees.Ordered (fun a b => key a < key b) t`, the extracted full entry has a least input key; every residual key is **strictly greater** than `key m`; the residual remains strictly key ordered; and its key set is the original key set minus `key m`.

These follow by transporting the head equation to the existing pairwise key observation and using strictness. The extracted key is absent from the residual because strict order is irreflexive. This uses uniqueness of keys in this actual tree, not global injectivity of `key`. The payload remains arbitrary in an independent universe. The extractor has no query or comparator whose calibration would need the search unit's `Ordering.Compares` premise.

For an arbitrary structural relation `R`, residual `Ordered R` can also be preserved directly: every retained subtree label was already in the old subtree, and the splice preserves its ancestor bounds. That argument does not need transitivity. A claim that the extracted entry is related by `R` to **all** remaining entries is stronger and does need an additional premise, as the optional existing `next` case below shows. This is a boundary if such a theorem is selected, not a proposed order framework.

### Label transport

For arbitrary `f : α → β`, even between independent universes and even noninjective, the expected raw transport is

`X(t.map f) = (f m, t'.map f)` whenever `X(t)=(m,t')`.

For an Option presentation this becomes mapping the whole successful pair, including its residual tree, and preserving failure. The expected execution-count equality follows from the same shape-sensitive recurrence if the selected measured implementation proves it. It does not follow from `Trees.inorder_map` alone, and it does not charge the preprocessing computation `t.map f` for free.

Preservation of a chosen key-order conclusion needs the appropriate relation/key-preservation premise. A constant map still obeys raw structural transport but can collapse distinct keys. A semantic payload map deliberately changes the returned payload; it is not permission to erase that payload when claiming the original map's values are preserved.

## 5. Candidate timing observation, expressly unfrozen

Let `Csrc` mean **one charge per invocation of the source-defined ordinary extractor**, with constructors, shape tests and pair observations uncharged. This is an explanatory observation, not a chosen API, runtime claim, or generated Isabelle theorem.

On nonempty input it has the exact recurrences:

- `Csrc(N(E,a,r)) = 1`.
- For nonempty `l`, `Csrc(N(l,a,r)) = 1 + Csrc(l)`.

Thus it counts the nonempty nodes of the left spine. Every reached invocation is nonempty; there is no final call on `E`. An implementation that first recursively calls an empty left child and then interprets failure as the base case can return the same value, but charging every invocation would add one to each successful source call sequence. It would require a different tariff or an explicit correction, not an unchanged source timing claim.

For every nonempty `t`, `1 ≤ Csrc(t) ≤ t.height`, with no BST assumption. A left chain attains height; a right chain has cost one however tall it is. Rebuilding occurs at precisely the left ancestors above the removed node, so there are `Csrc(t)-1` source `Node` constructions. That separate count is not a physical allocation or memory theorem, and those constructions have charge zero under this candidate convention.

If a total Option executor chooses `(none,1)` on `E`, the new empty case fits a one-entry convention and the all-input bound becomes `cost ≤ height + 1`. The `1` is an explicit extension to unspecified source behavior. Choosing zero on empty instead defines a different total observation. No empty count is frozen by this report.

The completed source report found no generated ordinary `T_split_min` in `Tree_Set`/`Tree_Map` or the other scoped point-update sources. It also identifies the distinct AFP generated timing for the **join-based** helper, whose recurrence includes actual `W_join` work on returned residuals. Accordingly these ordinary calculations reconstruct the displayed recurrence under named charges; they neither claim that generated timing is absent everywhere nor transfer the ordinary count to a rebuilder that does more work.

## 6. Compact connected cases with independently specified outputs

### A. Domain, arbitrary base, and actual right-child promotion

For arbitrary `a : α` and arbitrary `r : BinaryTree α`, the base returns exactly `(a,r)`, with `Csrc=1`. This single general case includes a singleton and an arbitrarily tall right subtree. It requires no equality, order or inhabitant for unrelated labels. A singleton carrying `false` succeeds with that value; it is not an empty result.

The first recursive case with a possibly nonempty promoted child is:

`X(N(N(E,a,B),c,R)) = (a,N(B,c,R))`, with `Csrc=2`.

Both opaque fringes `B` and `R` are retained exactly. Neither is traversed by the extraction. The small strictly ordered numerical instance is:

| Observation | Independently expected value |
|---|---|
| Input | `N(N(E,0,L(1)),2,L(3))` |
| Returned entry | `0` |
| Actual residual | `N(L(1),2,L(3))` |
| Inorder before / after | `[0,1,2,3]` / `[1,2,3]` |
| Source invocations | `2` |
| Nodes before / after | `4` / `3` |
| Height before / after | `3` / `2` |

Dropping `B` would lose entry 1; reinstalling the old left child would retain entry 0. This is why the test must examine the full residual constructor expression and consume the actual recursive result.

For empty input, including `BinaryTree Empty` and `BinaryTree (Nat × Empty)`, the proposed Option value is none. Its count remains the separate extension choice above. No source nonempty claim should be applied to it.

### B. The retained printed ordered tree

Use `OrderedTreeExamples.printedTree` and its existing `printed_inorder`/`printed_ordered` statements. Its actual definition is

`N(N(L(2),3,L(5)),6,N(L(8),9,E))`.

The source visits labels 6, 3, and 2. The independently expected output is:

`(2, N(N(E,3,L(5)),6,N(L(8),9,E)))`, with `Csrc=3`.

The residual is specifically rooted at 6 with left root 3 and unchanged right root 9; equal inorder does not identify that shape. Its inorder is `[3,5,6,8,9]`, it has five nodes, and its height remains 3. This both exercises the three-level return path and refutes a blanket claim that extraction always decreases height by exactly one.

The positive ordered client should connect the actual extraction result through the general head theorem and the existing strict-key bridge. The result 2 is least; all residual labels are greater than 2; the residual is ordered; the exact node decrement is one. Recomputing only the concrete lists would not exercise those public-law connections.

### C. Semantic pairs, a false value, and the actual map successor body

Use the existing `OrderedTreeExamples.taggedTree`, whose name refers here to semantic `(Nat,Bool)` records:

`N(L((0,false)), (1,true), L((2,false)))`.

The original ordinary extraction on this whole tree must return

`((0,false), N(E,(1,true),L((2,false))))`, with `Csrc=2`.

The residual full-entry list is `[(1,true),(2,false)]`. Under the existing key ordering, key 0 has been removed, while keys 1 and 2 retain `true` and `false`, respectively. In an optional map observation, a stored `false` is `some false`, distinct from absence. There is no order or equality requirement on the semantic Bool payload in the generic claim.

The completed API assessment identifies the actual standard observation `List.lookup`, whose cons equation tests the query against the head key. On the concrete Nat-key lists here, the original lookup at 0 is `some false`, and the residual lookup at 0 is `none`; lookups at 1 and 2 retain `some true` and `some false`. A generic Boolean-key observation requires its stated `BEq` assumptions, and identifying that test with equality requires a lawful or local equality premise. These assumptions belong to the observation bridge, not the extractor. No map ADT or independent tree-search dependency is needed to state this list client.

**The Chapter 6 successor-replacement connection uses a different input to the extractor.** Consider only the nonrecursive EQ body for deleting this tree's root key 1. Its right child is the nonempty singleton `L((2,false))`. The actual extraction of that child is `((2,false),E)`, with one extractor invocation. Substituting this returned pair into the literal source constructor gives:

`N(L((0,false)), (2,false), E)`.

The old left subtree is unchanged. The whole successor entry, including its false value, becomes the root. The resulting inorder is `[(0,false),(2,false)]`; key 1 is absent, and key 2 still denotes false. Reusing the old root's true value would instead produce `(2,true)` and fail this observation despite preserving the remaining key set.

This body is a concrete consumer of the actual returned entry **and** actual returned residual. It is not an implementation of the recursive delete operation or credit for the whole map ADT. Its one extractor call is not a claim that full deletion costs one: a separately charged delete entry or any other selected cost would have to be included by that future implementation.

For structural transport, reuse `OrderedTreeExamples.discardTag (k,b)=(k,())`. Applied to the whole-tree extraction, the expected result is

`((0,()), N(E,(1,()),L((2,()))))`, with the same two source invocations.

The existing `discardTag_not_injective` and `discardTag_preserves_key` distinguish raw mapping, key-order preservation, and semantic value change. This intentional Bool-to-Unit client does not justify silently discarding a Bool when implementing the original map.

### D. Duplicate keys and one-occurrence removal

Reuse `OrderedTreeExamples.sameKeyRecords`:

`N(E,(1,10),L((1,20)))`.

Its output is exactly `((1,10),L((1,20)))`, with `Csrc=1`. The two full records are distinct and the existing explicit lexicographic relation orders them, but strict ordering by `Prod.fst` fails. After extraction, key 1 is still present with value 20. Thus full-record distinctness or lexicographic ordering cannot replace strict key uniqueness in a minimum-key removal contract.

This same case, mapped by `Prod.fst`, also supplies the raw identical-label counterexample without a second independent fixture: `N(E,1,L(1))` returns `(1,L(1))` in one source invocation. The input and residual label sets are both `{1}`, while `{1} \ {1}` is empty. The exact inorder equation and one-node decrement remain true. Set union with the extracted entry is the correct unconditional consequence; set difference is not.

The negative result must be stated at the observation it refutes. Removing the exact full record `(1,10)` does leave only `(1,20)` in this particular pair tree; the failed assertion is deletion of the **key** 1, or deletion of a duplicated full label after projection.

### E. A raw inorder head can fail to be the numeric minimum

Use the existing constructor family `OrderedTreeExamples.three 2 0 1`, namely

`N(L(2),0,L(1))`.

The input inorder is `[2,0,1]`. The literal source returns

`(2,N(E,0,L(1)))`, with `Csrc=2`.

The residual inorder is `[0,1]`, and the node count falls from three to two. Entry 2 is the first inorder occurrence but is not a least natural label because 0 is also present. The input is not a strict BST; no comparator choice or successful-extraction condition repairs that missing premise.

The residual happens to be ordered. This does not imply that the original tree was ordered, nor does it turn the extracted 2 into its minimum. The raw result must remain 2 if a future proof or implementation is repaired.

### F. Strict left/right chains: complete residuals and sharp counts

For a nonempty list of increasing distinct keys `[0,...,n-1]`, let `Ln` denote the left chain rooted at `n-1` and ending at 0, and `Rn` the right chain rooted at 0 and ending at `n-1`. These are mathematical fixture families, not new required carrier definitions.

Both are strict BSTs with that exact inorder, `n` nodes and height `n`. The complete expected outputs are:

| Input | Entry | Actual residual shape | Source invocations |
|---|---:|---|---:|
| `Ln`, `n>0` | `0` | The left chain on `[1,...,n-1]`, retaining root `n-1` when `n>1` | `n` |
| `Rn`, `n>0` | `0` | The original right child: the right chain on `[1,...,n-1]` | `1` |

For `n=1`, both residuals are empty. For `n=3`, the precise expressions are:

- Left input `N(N(L(0),1,E),2,E)` gives `(0,N(L(1),2,E))`, cost 3.
- Right input `N(E,0,N(E,1,L(2)))` gives `(0,N(E,1,L(2)))`, cost 1.

Both residuals have inorder `[1,2]` and height 2, but their roots and child positions differ. Full residual equality must not be inferred from the shared list. More generally the two residual shapes differ for `n≥3`; the counts differ for `n>1`.

The family proves the prospective raw height upper bound is sharp and shows that a height lower bound does not hold uniformly for all shapes. It also exposes why a strict BST invariant alone supplies no balanced logarithmic-height premise. The source-entry equations for arbitrary `n`, if formalized, would be substantive general witnesses; the finite Python checks for `n=1,...,6` are only sanity checks and establish no asymptotic theorem.

These are counts for the **ordinary leftmost** extractor on left and right chains. They do not instantiate AVL's rightmost balancer or infer its full work by symmetry.

## 7. Conditional stronger-claim boundaries, without extra scope

### Arbitrary relation: residual preservation versus leastness

If the API exposes the weak structural residual-order theorem, reuse the existing `OrderedTreeExamples.next a b := b=a+1` and `next_ordered` on `three 0 1 2`.

The actual output is `(0,N(E,1,L(2)))`, with `Csrc=2`. Both original and residual satisfy the appropriate structural `Ordered next` predicate. Nevertheless `next 0 2` is false. This is a compact counterexample to concluding that the extracted entry precedes every residual entry from arbitrary structural `Ordered R` alone. It uses the existing nontransitivity fixture and need not create a new relation package or become a mandatory case if only strict-key consequences are selected.

### Ordinary rebuilding does not maintain derived caches

If any erasure or cache-preservation claim is considered, the existing `TreeCacheExamples.sizeSample` gives a direct boundary. Its underlying sample is `N(L(0),1,N(L(2),3,E))`; the correct size annotations are root `(1,4)`, left `(0,1)`, right `(3,2)` and its left leaf `(2,1)`.

Ordinary extraction on those full labels returns `(0,1)` and the raw residual

`N(E,(1,4),N(L((2,1)),(3,2),E))`, with two extractor invocations.

The residual has three nodes, but its retained root annotation is 4; the correct local size equation is `0+2+1=3`. Erased inorder is `[1,2,3]`, yet the root cache is stale. This establishes the intended distinction between raw full-label transport/erasure and a later smart constructor that recomputes annotations. It does not add a cached extractor to the proposed ordinary scope.

Semantic map payloads are different: `(key,value)` in `Tree_Map` is a full logical entry, whereas `((key,value),annotation)` would contain an outer annotation. Erasing the latter must preserve the inner pair. The Bool value in case C cannot be treated as an irrelevant cache field.

## 8. What later variants cannot inherit automatically

The completed source report's later-family table was read in full. The following limits matter to these cases:

| Family / original rows | Required separation from the ordinary cases |
|---|---|
| Interval smart extraction, C05-076/078 | Actual ancestors must use the smart constructor. Erased inorder can be independent of cache/BST validity, while cache preservation has its separate valid-input premise. The stale-size example demonstrates the ordinary mechanism's limitation. |
| 2–3 extraction, C07-037/042/048/049 | Different carrier and underflow-tagged residual; completeness justifies partial helpers and is required even by the inspected source inorder theorem. Ordinary success on every nonempty raw binary tree does not supply this domain. |
| Red-black replacement, C08-047–051/071/072/086 | Reconstruction depends on the **old** child's color and uses `baldL` or red rebuilding. Raw erased inorder, color/black-height preservation, map adaptation and actual balancing work remain separate. The ordinary residual shape and count are not its output/work theorem. |
| Cached and balance-factor AVL, C09-030–033/039/040/084–086 | The source extracts the rightmost predecessor, returns residual before entry, and uses its actual balancer or height-change test. The two families' source invariant premises differ. Neither is implemented by an ordinary leftmost extractor. |
| Join-based extraction, C10-014–021 and later work rows | The recursive residual is supplied to `J`; exact output shape, validity and total work depend on that actual operation. The base locale's unconditional conservation assumption is set union, not raw inorder or multiplicity. |

### A concrete set-versus-inorder boundary for the join locale

The original `Set2_Join` assumptions require `set(J l a r)=set(l)∪{a}∪set(r)`, conditional BST preservation, and separate invariant laws. They do not require `I(J l a r)=I(l)++[a]++I(r)` on arbitrary raw input.

Consider raw input `N(L(0),2,L(1))`, whose inorder is `[0,2,1]`. Ordinary extraction returns `(0,N(E,2,L(1)))`, with residual inorder `[2,1]`. At the corresponding join-based rebuilding point, a result of `J E 2 L(1)` whose inorder is `[1,2]` has the same required set `{1,2}`. Because the raw node with root 2 and right key 1 is not a BST, the conditional BST-input premise does not itself rule out that reordered result.

Thus the set equation alone cannot derive the ordinary raw head-inorder equation. A join that normalizes a finite key set into a strictly sorted right chain is a conceptual way such order changes can occur; no such join is implemented here, and no claim is made that a specific RBT/AVL join chooses this output. Duplicate elimination likewise cannot be excluded by a raw set equation alone, so the ordinary one-node decrement cannot be imported without the appropriate stronger premise.

Even a later join with a separately proved inorder law may return a different shape and incur extra recursive work. The source report identifies the supplementary StronglyJoinable `join_size` and `W_join` hypotheses rather than silently obtaining them from `set_join`. No generic rebuilder framework, mirror extractor, balance proof, allocation model or join-cost bound is proposed by these cases.

## 9. Intended public connections and original obligations

No extractor API exists in the retained ordinary tree files read here. Future case names therefore remain unfrozen. If a unit is selected, the examples should consume its actual execution and public laws, with these existing connections:

| Case / conclusion | Meaningful public connection to retain |
|---|---|
| Empty and arbitrary base | Actual domain/base equations, plus existing `TreeCacheExamples.empty_tree`; no default or payload equality. |
| Promoted child and printed tree | Actual recursive result, exact residual constructor, general head-inorder law; `Trees.inorder_length` for size; actual structural height law for height. |
| Ordered minimum and residual | Existing `printed_ordered`/`taggedTree_ordered` and `Trees.ordered_key_iff_pairwise`; retain strictness and local distinctness, rather than an unrelated concrete minimum calculation. |
| Semantic map successor body | Bind or pattern matching on the actual returned full pair and residual; preserve the successor's false value and old left subtree. No whole-delete theorem is substituted. |
| Duplicate and malformed cases | Actual successful raw execution together with explicitly failed key-order/minimum/removal premises. Do not weaken or change the expected result to make a theorem easier. |
| Label transport | Actual full-result map theorem and, if measured work is selected, actual execution-count transport; use `inorder_map` and `ordered_map_key_iff` at their distinct observation levels. |
| Chain family | Actual nonempty cost recurrence and full output shape; raw height bound and source-valid-domain restriction. No list-equality-to-cost inference. |

These support C05-006/007 and the helper used by C05-008 and C05-013, and the exact shared operation of C06-047 with the successor body needed by C06-048/063. They do not discharge whole deletion, its set/map laws, C05-021's direct proof route, Chapter 6's complete ADT realization, or any later balanced implementation or logarithmic/work bound.

The Chapter 6 printed reference to §5.6.4 remains the recorded source erratum: the actual generic dependency is §5.2's ordinary `Tree_Set.split_min`. Its interval-cache namesake is not an interchangeable map operation.

## 10. Completed-preflight correspondence and final handoff

The complete stopped source report was read after the independent calculations. It agrees on the literal guarded descent, arbitrary-label head equation, full semantic-pair reuse, nonempty source-entry count, and the separate status of the proposed empty Option cost. Its later-family and generated-versus-reconstructed timing distinctions are retained above.

The complete stopped API report was then read at the identity recorded in section 2. Its actual carrier, inorder and strict-key interfaces agree with the source files inspected independently here. Its scoped search found no ordinary full-entry/residual extractor; the existing `Ordnode.splitMin` and Std internal `minView` use different cached/balanced carriers and rebuilders. Their minimum/list results cannot supply the source's literal residual shape without an algorithm correspondence. `BinaryTree.indexOf`/`get` likewise provide a path/value, not the rebuilt residual.

The API report explicitly keeps the head-inorder theorem one-way; the chain and printed residual cases preserve that distinction. Its proposed arbitrary-label transport, node decrement, residual-height nonincrease and ordered consequences agree with the independent expectations. Its arbitrary-relation residual lemma is feasible but remains a choice for the later scope, with the `next` boundary retained if selected. Its concrete map successor body is the same full-entry client described in case C, not a completed deletion implementation.

If resource work is selected, its recommendation of one actual measured recursion with a Nat observation and transparent projections is compatible with these cases. It would use the existing `Resources.bind` and `CallCount.tick` rather than a separate recursively defined cost oracle. The agreed nonempty recurrence has no reached nil call; the empty observation is still a choice, and mapping inputs separately still incurs whatever separately declared preprocessing cost applies. No second cost axis, generic rebuilder or new carrier is needed by the selected evidence.

No concrete mismatch was found among the independently calculated cases, completed source assessment and completed API assessment. Their agreement is source-level preparation; no proposed theorem has been elaborated by this task. The recommendation is to consider only the ordinary source-shared primitive and its stated connections through the existing freeze/release workflow. Public names, implementation base, tariff and exact scope remain unfrozen.

Only this report has been written. The completed file was read back in full, then writes stopped; its final byte/line count and ordinary SHA-256 are recorded in the separate author handoff. No Lean source, prior report, ticket, index, ref, worktree, cache, compiler/checker state, chapter scope or validation gate has been changed, and no upload or independent final review has been initiated.
