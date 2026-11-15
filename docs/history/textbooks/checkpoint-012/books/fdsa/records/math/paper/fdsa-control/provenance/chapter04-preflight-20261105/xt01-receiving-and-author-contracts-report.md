## XT01 receiving preparation is ready

**Exact XT01 can be received onto accepted Chapter 3 without replacing any accepted formal source.** All **22 pre-existing local files** in its recorded 26-file import closure are byte-identical between donor `64c6b777d828ecfe83234fc2aed94600a1f24297` and accepted `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`. The four new formal modules and their source document are absent at the accepted candidate.

I have now read the **complete four-module formal addition**, including all **363 lines of `Examples/TreeCache.lean`**, the complete source document, and the original entrypoint/reconstruction-map deltas. This remains implementation preparation; I made no changes and ran no compiler or verification command.

### 1. Exact original scope and receiving targets

Original unit:

- Base: `a14977b9e316cc484ffad8a470d26b15615956c0`
- Candidate: `64c6b777d828ecfe83234fc2aed94600a1f24297`
- Tree: `1e7b8d55d44b4302b70cec5b38411b5529247556`
- **Seven changed paths, 894 insertions, no deletions.**
- Frozen requirements: `81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce`

The exact original path identities are:

| Path | Bytes | SHA-256 |
|---|---:|---|
| `Applications/Trees/Observations.lean` | 4,119 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Cached.lean` | 5,668 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| `Applications/Resources/TreeCache.lean` | 3,877 | `54d6bf9255e4d2b619fcd079a5636bac391aeb44eafe45cc0f4c6abfc2afebf6` |
| `Examples/TreeCache.lean` | 16,307 | `ae78e0f515ba11c9f5348533624df49da59d98887689a16c16a35c3f880fd754` |
| `docs/research/fdsa-tree-cache.md` | 11,655 | `4d8bfd13aece8fe9c3eeb563ee3908bd443d523c75fcdaa0658fa7b0639d4bed` |
| Original `SquareApplications.lean` | 8,318 | `f6c0e7e43ffdd4f50d7b9a2402d3135d3cd104285c4e539c426ef6cd544b196b` |
| Original reconstruction map | 18,101 | `b7e4fd17a6b2b76974a39caa55de6d5231c813b13c8e873a024167f36126d9f1` |

The accepted files that will receive additive integration edits have these different identities:

| Current path at `298…` | Bytes / lines | SHA-256 |
|---|---:|---|
| `SquareApplications.lean` | 10,717 / 326 | `66f9a33157409cf12c5044b3f3b338d7da83e720f22e724989e2184e66bf4211` |
| `docs/research/fdsa-reconstruction-map.md` | 46,755 / 710 | `dca421107e141c97e48ae28225b26e308816e0b5bae201dca39a2a3d5cc8e741` |

### 2. Safe receiving recipe

After checkpoint 0137 is durable and you explicitly release source work:

1. **Use an isolated receiving branch based on exact accepted `298…`.** Record the original XT01 base/candidate and this incorporated accepted base. Preserve the original `work/fdsa-tree-cache` reference.

2. **Receive the four formal files as exact Git-blob additions.** Their paths are absent at `298…`. Initially retain their complete donor bytes, public names, examples, options and proof bodies. Any subsequent compiler repair becomes a separately identified candidate correction.

3. **Receive the source document with a narrowly recorded status reconciliation.** Its mathematical account and example connections remain useful. Its opening status and final review-boundary wording come from the original draft stage. A dated receiving notice should distinguish:
   - the now accepted Chapter 1–3 base;
   - the completed, still-Blocked independent XT01 source assessments;
   - the absence of actual XT01 compilation/type/full-audit/final-approval evidence.

   Preserve the original document through the donor commit and record the exact receiving document delta.

4. **Add only `import Examples.TreeCache` to the current public entrypoint.** The original delta was precisely that one import. Its transitive imports cover the other three new modules. Removing the one added line from the receiving entrypoint should recover the current accepted file byte-for-byte.

5. **Append the XT01 section to the current reconstruction map.** Retain all 46,755 accepted bytes as an unchanged prefix. The original addition is 25 lines, with the six-row mapping for folds, observations, caches, annotation, local work and connected uses. Reconcile its old final sentence, which says no earlier review covers the draft: complete independent source assessments now exist, although final qualification remains pending.

6. **Keep unrelated shared drafts outside this receiving candidate.** The current dependency comparison shows that no Potential generalization or other later shared prefix is needed: every pre-existing file in XT01’s local closure already matches the accepted base exactly.

7. **Capture and qualify the complete receiving candidate under the existing XT01 loop.** Retain all seven original paths, all 115 public names, original requirements, case expectations and prior review history. Full actual types, applicable complete check/audit, both final independent axes and immediate verification remain mandatory.

This recipe preserves all accepted source and documentation content while making the XT01 integration delta explicit and reviewable. It does not require rebasing or modifying the historical donor branch.

### 3. Exact 115-name inventory

I read the full preferred inspection input and independently reconstructed the authored declaration order from all four formal source files. The reconstructed sequence equals the existing inventory exactly.

| Module | Definitions | Theorems | Total |
|---|---:|---:|---:|
| `Applications.Trees.Observations` | 2 | 13 | 15 |
| `Applications.Trees.Cached` | 5 | 19 | 24 |
| `Applications.Resources.TreeCache` | 2 | 6 | 8 |
| `Examples.TreeCache` | 16 | 52 | 68 |
| **Total** | **25** | **90** | **115** |

There are no authored private declarations, anonymous examples or new instances in this original four-module addition. Generated declarations remain part of the eventual exhaustive audit.

Exact retained inputs:

```text
fdsa-control/provenance/binary-tree-cache-public-statements115-prepared-20261104/
```

- `inventory.json`: **29,136 bytes**, SHA-256  
  `630a879b3922b298f0f641e9d8fec222d07911ad40378afcfe050d724479f9d1`
- `StatementsExplicit.lean`: **4,522 bytes**, SHA-256  
  `6c5e005fc23b5c9c3441c47da709de201df77c5b773fb8950964143280ab6df2`
- Exact ordered-name digest, one name per line with a final LF:  
  `1b3459408687c6090f25ff71a11f3fdb886fddea29c6c4421f690261cf8bf4fe`

The preferred input contains four imports, the original three printing options, and the exact 115 `#check @…` commands. The older `Statements.lean` and the explicit-`@` correction record remain preserved. Neither historical input has run.

For receiving qualification, preserve this exact name sequence and record any expanded printing-option preparation separately. The four equation-style definitions remain:

- `Trees.fold`
- `Trees.Cached.read`
- `Trees.Cached.Valid`
- `TreeCacheExamples.chain`

Their original syntactic headers stop before the first leading equation `|`. Source header records are distinct from actual elaborated types.

### 4. Current interfaces and pinned API assessment

**I found no concrete missing, renamed or incompatible API in the inspected source paths.** This is a static assessment; no elaboration success is claimed.

The important current interfaces are byte-identical to the original XT01 dependency view:

| Interface | SHA-256 |
|---|---|
| `Applications/Resources/Measured.lean` | `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| `Applications/Resources/CallCount.lean` | `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |
| `Applications/Resources/ListReversal.lean` | `39aa38f0d3de87c0e37f222eea89880f81a1d93eeeff8e7618b07a260e2d7f0e` |
| `Applications/Sequences/OrderedSummary.lean` | `d484e6c34f4ebace4ba121f931eba53a86f34a3c4b69e06d9d0b24ae8c8c7261` |

The inspected definitions support the draft’s actual calls:

- `Measured` is a value/observation pair.
- `bind` retains evaluation order as `r.2 + s.2`.
- `CallCount.tick` adds one after the body.
- `ListReversal.appendRun_exact` supplies `(xs ++ ys, xs.length + 1)`.
- `OrderedSummary.summary` supplies its nil, append and singleton laws over a `Monoid`.
- Mathlib’s `BinaryTree.node` is label/left/right; canonical counts and height have the equations used by the proofs.
- `BinaryTree.left` and `right` return `nil` on `nil`, without requiring inhabited labels.
- The `FreeMonoid` source confirms the concrete list representation, concatenative product, `ofList`, singleton `of`, and lift used by the noncommutative word example.

Pinned Mathlib files inspected:

- `Mathlib/Data/Tree/Basic.lean`: **6,679 bytes**, SHA-256  
  `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d`
- `Mathlib/Algebra/FreeMonoid/Basic.lean`: **19,259 bytes**, SHA-256  
  `82573d5b6f5968524f3c9c84ed91fd6a3f5eb222434789e6a2de7145c870e2a9`

The FreeMonoid local bytes were compared directly with the exact Mathlib Git blob. The tree API identity matches the pinned source and retained independent assessments.

The following configuration files are also unchanged between donor and accepted base:

```text
lean-toolchain     Lean 4.35.0
lakefile.toml      SHA 76966dfb4ea744d75d4bbe20ed3a6c576a17145d23f36ba44c4422673c51b04f
lake-manifest.json SHA dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b
```

No fresh-check trigger is introduced by this read-only preparation. Actual acceptance mode remains governed by README and the eventual change.

### 5. Prerequisites and review continuation

The frozen wording is explicit:

- **XT01:** accepted Chapter 1 is required before integration or acceptance. Later incorporation of an accepted base must preserve the original history, requirements and findings.
- **XT02:** accepted Chapter 1 **and accepted XT01** are required before integration or acceptance. It retains its original six-path scope, 90-name preparation and **XT02-SP01** history.
- **XT03:** accepted Chapter 1 **and accepted XT01** are required before integration or acceptance. **XT02 is expressly not an implementation prerequisite.** Retain its original seven-path scope, 88-name preparation and **XT03-CP01/DOC01** history.

Thus XT02 and XT03 can become independent source streams after the XT01 prerequisite is satisfied. Their final gates remain independent and complete.

The retained XT01 canonical source reports currently have these identities:

| Report | Bytes | SHA-256 |
|---|---:|---|
| Standards preparation | 22,912 | `a24df99f02fd70300f25b982b53293d2f0d8485f053b8891829fe81c37043c97` |
| Spec preparation | 21,429 | `c54206bcb23cf96bc0968c2bc4f84ed2166ee6f257c4a1d952f5c578418d3432` |

Both report complete source assessment, zero concrete findings and overall **Blocked**. I inspected their current scope/API/status passages without replacing their assessments or claiming a new complete read of both reports in this preparation.

### 6. Proposed disjoint Chapter 4 contracts

These are proposed interfaces for you to freeze before author release. All listed paths are absent at accepted `298…`.

#### A. Basic observations: one owner

**File:** `Applications/Trees/BasicObservations.lean`  
**Namespace:** `Trees`  
**Dependency:** accepted XT01 observations.

Reserve:

```lean
setTree  : BinaryTree α → Set α
preorder : BinaryTree α → List α
Subtree  : BinaryTree α → BinaryTree α → Prop
subtrees : BinaryTree α → Set (BinaryTree α)
```

Use an independent structural set observation with the book recurrence, preserving arbitrary labels:

```text
setTree nil = ∅
setTree (node a l r) = setTree l ∪ {a} ∪ setTree r
preorder nil = []
preorder (node a l r) = a :: (preorder l ++ preorder r)
```

A small inductive structural `Subtree` relation with reflexive, left and right constructors is sufficient. Define `subtrees t = {s | Subtree s t}` and prove the exact book set recurrences. This avoids introducing graph/path infrastructure.

The initial contract should include:

- inorder/set and preorder/set membership equivalences;
- preorder length and map laws;
- subtree reflexivity, nil membership, node decomposition and transitivity;
- exact `subtrees` recurrence correspondence.

Neither equality decisions nor label ordering belongs in these generic contracts. Freeze this file first so enumeration, reconstruction, maximal-subtree and maximum-cache authors share one vocabulary.

#### B. Boolean/height summary: one owner

**File:** `Applications/Trees/CompleteSummary.lean`  
**Namespace:** `Trees`  
**Dependencies:** XT01 fold and the accepted/reconciled XT02 shape interface for the correctness bridge.

Reserve:

```text
completeHeightStep : (Bool × Nat) → α → (Bool × Nat) → (Bool × Nat)
completeHeight     : BinaryTree α → Bool × Nat
completeBool       : BinaryTree α → Bool
```

Suggested algorithm:

```text
completeHeightStep (cl, hl) _ (cr, hr)
  = (cl && cr && decide (hl = hr), max hl hr + 1)

completeHeight t = fold (true, 0) completeHeightStep t
completeBool t = (completeHeight t).1
```

Required shared laws:

```text
(completeHeight t).2 = t.height
completeBool t = true ↔ Trees.Complete t
```

The algorithm does not call the Prop predicate or compare tree labels. It can support:

- the source-facing executable completeness observation;
- Exercise 4.10’s generic cached Boolean/height specialization;
- the summary component of the one-traversal maximal complete subtree algorithm.

Avoid making `decide (Complete t)` an unexamined computational dependency of the algorithm. The Boolean result and its proved equivalence give the necessary executable boundary directly.

#### C. Disjoint later modules

| Owner stream | Files and public responsibility |
|---|---|
| Structural/cache author | `BasicObservations`, `CompleteSummary`, `Augmented`, `MaximumCache`; generic source-facing cache specializations and raw maximum-to-optional-summary bridge |
| Exercise author | `Levels`, `Enumeration`, `Reconstruction`, `Rose`; matching separate example modules |
| Balancing author | `Balance`, `Resources/TreeBalance`; prefix/suffix contract, derived wrappers, shape/log laws and actual measured execution |
| Assigned maximal-subtree owner | `MaximalCompleteSubtree`, importing the frozen `Subtree` and Boolean/height contracts; no edits to those shared files |

For balancing, an `Option (BinaryTree α × List α)` prefix core is consistent with the recorded failure policy and supports a precise success/domain theorem. The full-list wrapper can be total without an `Inhabited α` assumption because `nil` is always available and successful consumption is proved. Choose and freeze the exact public names and failure policy before downstream examples begin.

Keep new Chapter 4 clients in new library/example files. The original XT01 four modules can then remain byte-stable during their receiving qualification. Root should own all public-entrypoint, reconstruction-map, chapter-correspondence and acceptance-record edits.

### 7. Read receipts and bounded correction

New read receipts:

- Complete `Examples/TreeCache` lines 1–185 and original delta summary: **`480285`**
- Complete examples lines 186–363 and complete entrypoint/map deltas: **`06917f`**
- Complete 183-line source document and retained closure/inventory schema: **`fc6d1b`**
- Complete preferred 115-name input and current XT01 ticket/round record: **`6aa39a`**
- All 26 original closure hashes, all 22 accepted dependency comparisons, complete current `Measured`/`CallCount`: **`580ee5`**
- Inventory/count/order reconciliation and preserved explicit-input correction: **`5d76ad`**
- Current tree APIs and exact XT01/XT02/XT03 prerequisite wording: **`04fcb8`**
- Current configuration and integration-target identities: **`26da87`**
- Fresh four-source reconstruction of all 115 names and held-review status/API passages: **`d89a37`**
- Pinned FreeMonoid source ranges and exact Git-byte comparison: **`69b092`**
- Proposed new path absence checks: **`dacc3a`**

One read-only command, **`ce9c4b`**, exited 1 when it tried the nonexistent name `lakefile.lean`, after displaying the intended current interfaces and confirming `lean-toolchain`. The corrected read **`26da87`** used `rg` to identify the actual `lakefile.toml` and completed both configuration comparisons. No files or references were written, and this was not a source or compiler failure.

**All implementation remains paused pending checkpoint 0137 durability and your explicit release.**
