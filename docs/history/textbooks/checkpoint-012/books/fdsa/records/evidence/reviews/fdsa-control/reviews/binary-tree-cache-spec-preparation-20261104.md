# FDSA-XT01 — independent Spec source preparation

## Current disposition and fixed scope

**Overall: Blocked. Source assessment complete, with zero new concrete Spec findings.** This is the independent Spec axis's source preparation within the existing whole-book loop. It is neither final approval nor Chapter 4 activation. I authored none of the candidate changes. Actual printed-type inspection, compilation, full candidate validation, exhaustive audit and immediate verification have not been supplied for this XT01 candidate.

The fixed original base is `a14977b9e316cc484ffad8a470d26b15615956c0`; the candidate is `64c6b777d828ecfe83234fc2aed94600a1f24297`. Independent immutable-Git inspection confirms that the candidate's sole parent and the merge base are that base. The nonempty three-dot diff contains exactly seven paths, 894 insertions and no deletions. The full frozen requirements are `reviews/binary-tree-cache-requirements.md`, version 1, SHA-256 `81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce`. All seven requirement groups and all mandatory connected cases remain in scope.

Accepted Chapter 1 remains accepted at `07e480f6ec9958d4975bb90151005b84f2907614`. The candidate's historical notes about an unaccepted Chapter 1 repair describe its original November 2 development boundary; they do not undo the later recorded acceptance. No accepted integration of XT01 is inferred. Exact Foundation F remains pending its own terminal and 145-type evidence; its continuation has priority. The established Foundation/Chapter 2 route and earlier reviews remain unchanged.

## Complete immutable source receipt

Every file below was read completely at the fixed candidate. Both existing-file diffs were also read completely; the full reads of the five added files cover their entire additions. No mutable worktree content substitutes for an immutable blob.

| Path | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Trees/Observations.lean` | 107 | 4,119 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Cached.lean` | 135 | 5,668 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| `Applications/Resources/TreeCache.lean` | 80 | 3,877 | `54d6bf9255e4d2b619fcd079a5636bac391aeb44eafe45cc0f4c6abfc2afebf6` |
| `Examples/TreeCache.lean` | 363 | 16,307 | `ae78e0f515ba11c9f5348533624df49da59d98887689a16c16a35c3f880fd754` |
| `SquareApplications.lean` | 253 | 8,318 | `f6c0e7e43ffdd4f50d7b9a2402d3135d3cd104285c4e539c426ef6cd544b196b` |
| `docs/research/fdsa-tree-cache.md` | 183 | 11,655 | `4d8bfd13aece8fe9c3eeb563ee3908bd443d523c75fcdaa0658fa7b0639d4bed` |
| `docs/research/fdsa-reconstruction-map.md` | 287 | 18,101 | `b7e4fd17a6b2b76974a39caa55de6d5231c813b13c8e873a024167f36126d9f1` |

The new public-root import is exactly `Examples.TreeCache`. That module imports the new pure cache and resource modules, and the cache imports observations, so all four new Lean modules occur in the intended transitive public closure. This source connection does not establish a complete candidate build, a coverage-guard pass or audit success.

All 15 governing instruction/documentation blobs match the retained exact reads, including AGENTS, implement, code-review and its heuristics, example-driven development and worked example, the shared review loop, architecture/domain rules, glossary, ADRs and language-direction guidance. The only nested AGENTS in the immutable tree governs an unrelated experiment. The exact Lean toolchain, Lake manifest and Lake configuration match the retained pins. The user's Nix waiver does not waive compiler/dependency identity, proof restrictions, qualified native execution, immutable-candidate checks or either independent review axis. The README's applicable normal-versus-fresh rules remain the validation authority.

## Primary source, retained correspondence and dependencies

I read the complete 259-line frozen requirements, ticket, start records, candidate handoff, source-identity table, completed bounded source preflight, and all three `research/binary-tree-shared-*-preflight.md` files. The earlier contributors were implementation support. Their assessments and the author's statement note were used as evidence aids; the present Spec assessment independently read the actual operations, proof bodies, claims and connected clients.

The pinned book text was read at literal-newline ranges 2056–2183 and 2454–2575, covering the relevant printed pp. 47–49 and 56–58. The text identity is SHA-256 `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`; the retained July 27, 2026 PDF identity is `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. I directly assessed the source's empty-leaf/node-labelled carrier, node/leaf counts, maximum height, inorder, annotation erasure, size cache, explicit-zero/ternary generic fold, all-node invariant and reader-correctness conclusion. The source's raw maximum-cache exercise and surrounding later obligations remain separate.

Relevant bounded portions of the Chapter 4, 5, 9, 15 and Appendix B inventories were also read; the receipt records their exact hashes and ranges. These preserve the companion revision `f86f290225eebcc52c1ae7dba2e098f405f51c21` and the recorded Tree, Tree2, interval, AVL, leftist and time-function identities. The earlier full theory inspections remain attributed to their original source records. I do not claim a new full read or rebuild of those Isabelle theories, nor that their revision built the manuscript. No external proof is a Lean dependency. No new PDF rendering or manuscript redistribution was performed.

At Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`, I read all 188 lines of `Mathlib/Data/Tree/Basic.lean` and the relevant complete contexts in `Mathlib/Algebra/FreeMonoid/Basic.lean` (1–150 and 285–335). The actual carrier has label/left/right constructor order, unlabelled empty leaves, a payload-independent empty-tree inhabitant, ordinary map, canonical counts and height, and total left/right projections. Its introductory retrieval-complexity prose is not used as a theorem about arbitrary tree height. The FreeMonoid implementation retains list order and supplies the exact singleton/lift behavior used by the word client.

I independently read the complete exact local `Resources.Measured` (71 lines), `Resources.CallCount` (58), `Resources.ListReversal` (116), `Resources.TreeFlattening.Core` (116), and `Sequences.OrderedSummary` (190) files. In particular, the actual append recursively processes its first list, the existing call-count adapter adds its final entry, and the exact theorem gives value `xs ++ ys` with count `xs.length + 1`. The sequence summary uses a free-monoid extension and requires only a monoid for the generic composition. Its optional outer-cache invariant is not substituted for recursive tree validity.

An immutable source-import traversal found 26 local files, 12 distinct external imports and 48 edges. The four new files are XT01's additions; all 22 pre-existing local closure files are byte-identical to accepted Chapter 1 R. The receipt preserves each exact input identity and import edge. This is a bounded source comparison, not a runtime/object qualification or transferred type/build credit. Later incorporation must account for the actual receiving candidate and any dependency changes.

## Assessment of all frozen mathematical requirements

### XT01-01 and XT01-02: ordinary fold, ordered observation and shape

`Trees.fold` is structural recursion on the existing BinaryTree carrier. Its arguments are the explicit empty summary and the ternary operation in left-summary/label/right-summary order. Independent universes are declared for payload, source summary and target summary. No algebra record, monoid, order, equality decision or inhabited-payload/summary instance appears in the generic fold interface. Supplying an actual empty summary is the intended mathematical parameter.

The constructor equations follow the actual recursion. `fold_map` applies the arbitrary label function exactly at the node-label argument; it does not require injectivity. `fold_fusion` assumes the stated empty-value equality and the operation compatibility for all supplied child summaries and labels, then proves the tree equation by induction. These are local algebra compatibility premises, not an assumption of the theorem's whole-tree conclusion. A future reachable-summary generalization is unnecessary for the frozen clients.

The size and height instances are proved equal to the existing `BinaryTree.numNodes` and `BinaryTree.height`; no competing size notion replaces them. Inorder is left labels followed by the node and right labels, retaining every duplicate occurrence. Its length equals canonical node count. Label maps preserve inorder by List.map and preserve node count, empty-leaf count and height. The leaf-count result reuses the existing node/leaf identity. These value laws include noninjective maps and make no append-timing identification.

### XT01-03 and XT01-04: recursive cache correctness and computed annotation

The cache uses `BinaryTree (α × β)` directly. `erase` is the existing map with first projection. `read` examines only nil versus node and returns either the supplied base or the actual root annotation. `smartNode` retains both child trees and computes only the new root field from their returned summaries and the payload.

`Valid` requires both child invariants and the local annotation equation recursively; nil is true. `smartNode_valid_iff` therefore retains both directions: valid children suffice, and invalid descendants are not repaired. The independent right side of `read_eq_fold` structurally folds the erased tree. The induction consumes child validity and the actual local equation. It never defines correctness solely by a correct root read.

Inorder and shape erasure are unconditional, including malformed annotations. `erase_smartNode` similarly has no validity premise. There is no BST order, balance, associative combine, commutative combine or decidable equality requirement. `annotate` computes the actual cached tree as an ordinary instance of the same fold with smart construction. Its validity, erasure and root-agreement theorems are separate, and establish a nonvacuous valid realization for every ordinary input tree. No whole-annotation running-time result is claimed.

### XT01-05: actual local reads and reached callback work

`readRun` returns the actual root read with the separately declared natural-number charge one. `nodeRun` sequences the left read, right read and supplied measured combine callback at those returned values. It stores that callback's actual result and retains both original child trees. No erased-tree pass, subtree fold or annotation pass occurs in this execution.

The actual sequencing gives `1 + (1 + (c + 0)) + 1 = c + 3`, with c the observation of the reached callback. `nodeRun_cost` has no cache-validity or callback-value premise. `nodeRun_le` needs only the bound on that same reached callback. `nodeRun_value` likewise needs only the value equation at the reached arguments; it does not strengthen this to a global callback contract. `nodeRun_valid` adds both child invariants separately. The existing Measured/bind interface permits the distinct payload, summary and result universes.

This tariff is explicit local-access mathematics. It is not the source leftist helper tariff, a cost of arbitrary precision arithmetic, allocation or physical sharing, or a whole-program runtime claim. Natural addition is the actual observation algebra; the proof's use of its commutativity does not add commutativity to the pure fold or ordered-summary interfaces.

### XT01-06: complete connected cases

| Required use | Independently assessed connection and boundary |
| --- | --- |
| Arbitrary-payload size and height caches | `size_reader` and `height_reader` consume the generic valid-reader theorem, canonical fold specializations and erasure shape laws. Height correctness has no AVL balance premise. |
| Single pair cache | Both `pair_fold_*` results invoke fold fusion with the two projections. `pair_reader` uses one recursive pair-validity premise to recover canonical size and height. |
| Asymmetric fixture | The actual tree has four nodes, height three and inorder `[0,1,2,3]`. Its size, height and pair annotations are computed by `annotate`; reader results use public correctness and erasure laws. |
| Independent ordered composition | `ordered_summary_fold` relates the existing sequence summary of full inorder to the tree fold with `l * measure a * r`, for arbitrary `[Monoid M]`. The proof uses nil/append/singleton summary laws and associativity in the required direction. |
| Noncommutative word | `sample_word` first invokes that generic composition, then the independently stated inorder, and obtains the specified FreeMonoid word. Child order is not hidden by a commutative consumer. |
| Inorder loses shape | Balanced and left-chain three-node trees have the same inorder and heights two and three. The statement does not infer height from an ordered-label observation. |
| Repeated and empty labels | A constant label map retains four occurrences and canonical shape. Every BinaryTree Empty is nil; generic fold, annotation/erasure and measured empty read retain the supplied summary base without inventing a payload. |
| Malformed descendants | The actual four-node cache stores 4,2,1,1 at labels 1,0,3,2. Root read equals true size four and satisfies the local root equation, while two descendant caches are wrong. The public validity equivalence exposes the failure, and smart construction reconstructs the same invalid tree. Erasure still gives the intended tree/inorder. |
| Arbitrary annotation transport | `erased_fold` directly uses the generic map/fold theorem and includes invalid annotations, with independent payload, summary and annotation universes. |
| Zero-observation size/height callbacks | The callbacks use existing pure computation. Public measured contracts give local cost three, actual smart-node values, valid output from valid children, and canonical size/height reader conclusions. |
| Actual recursive append callback | `appendStepRun` invokes the existing append execution at the reached left summary and `a :: rightSummary`. Public append/value/count and measured-node results give the intended inorder value and local count `leftSummary.length + 4`. Validity remains a separate conclusion. |
| Valid unbounded family | `chainCache n` is computed by annotation of a repeated-label left chain. Public annotation/read, inorder-length and canonical count theorems prove its read length n. The local call costs exactly `n + 4`, returns the next annotated chain and has valid children/output. `chain_node_exceeds` exceeds any proposed constant on this same valid family, including the correct n=0 boundary cost four. Preparation of cached inputs is explicitly outside the local count. |

The full abstract composition is present; the cases do not rely only on isolated arithmetic fixtures. No per-declaration example quota or new testing framework was introduced.

### XT01-07: integration and documentary scope

The public import connection is present, the source note covers the intended statements and limitations, and the map adds a bounded shared-unit section. The map's common-mathematics references to C04-062–072 do not close every Chapter 4 obligation; the unit does not claim the entire chapter or its set, reconstruction, balancing and exercise developments. The older map's Chapter 1 repair-status paragraphs are historical at this fixed ancestor. The later accepted Chapter 1 status must be preserved when preparing an eventual receiving candidate.

The exact draft precedes XP01's budget generalization. Its historical sentence about erasureSquare is therefore not a new XT01 instance of the later XP01 documentation finding. Any later incorporation must retain already-required documentary corrections for the actual combined candidate. No old finding or accepted state is reset by this independent source preparation.

## Source distinctions and retained later obligations

The book's augmentation invariant is reproduced as a recursive proposition and related to the independently computed fold. The source's erased inorder alternatives are connected by the arbitrary label-map law. The generic operation receives both child summaries; an applicative label traversal is not substituted for it, and a branch-sensitive height fold is not reduced to a monoidal summary of inorder.

The source's size smart constructor has bounded local overhead under its chosen primitive arithmetic convention. XT01 correctly exposes callback work for arbitrary augmentation instead of asserting a universal constant for arbitrary combine functions. The actual list callback is a chosen single append; associativity and singleton-append value identities do not prove a timing identity with a literal two-append source traversal. That operational bridge remains queued.

The interval specialization still needs its actual maximum semantics, attainment and search-pruning proofs. AVL balance and rotation/update correctness remain stronger than height-cache validity. The raw maximum-cache exercise's Option-valued reader needs its stated representation bridge, without imposing an artificial bottom or default payload on all trees. The existing leftist queue and its zero-helper tariff remain separate; its smart fork may swap children, so its unconditional content bridge is a permutation law, not fixed inorder equality. Braun interleaving, rose/binomial carriers and their observations are not replaced by this binary inorder.

Whole-fold/whole-annotation measured execution, accumulator/direct-inorder timing, logarithmic shape theory, tree enumeration/reconstruction, balancing and complete/almost-complete results remain outside this shared unit and mandatory in their original later chapter scopes. These are boundaries of XT01, not exclusions from the user's whole-book request.

## Complete authored declaration inventory and read boundary

| Source file | Public definitions | Public theorems | Explicit public total |
| --- | ---: | ---: | ---: |
| `Applications/Trees/Observations.lean` | 2 | 13 | 15 |
| `Applications/Trees/Cached.lean` | 5 | 19 | 24 |
| `Applications/Resources/TreeCache.lean` | 2 | 6 | 8 |
| `Examples/TreeCache.lean` | 16 | 52 | 68 |
| **Total** | **25** | **90** | **115** |

All 115 names are authored additions in the original scope. There are zero private named declarations, anonymous examples, named or anonymous new instances, inductives or structures. Generated equation/compiler helper declarations are not guessed or included in this authored-name count; the eventual exhaustive audit has its own declaration population.

Every complete source header was independently read in bounded inventory blocks 1–47, 48–81 and 82–115, after the complete source reads. The four equation-style definitions—`Trees.fold`, `Trees.Cached.read`, `Trees.Cached.Valid` and `TreeCacheExamples.chain`—end their recorded headers before the first leading `|`, rather than consuming a later `:=`. Inline attributes remain in their exact source prefixes. Section Ordered contributes context, not an extra namespace segment. The receipt records all 115 names, source positions, complete header text and hashes, and the relevant universe/instance contexts. None of this is an actual elaborated-type read.

The retained source preflight records an earlier removal of a redundant trailing proof step before the stable candidate. I read the exact current proof body and preserve that attribution; no new statement change, observed compiler failure or acceptance result is inferred. There are zero new concrete Spec findings. Any later actual elaboration issue must retain its own identity and be assessed under this same full scope.

## Remaining gates and preservation

A qualified actual focused result and complete actual public-type inspection are still required, with immutable source/dependency/program identities, exclusive input ownership, genuine terminal evidence and matching pre/post observations as applicable. A source signature, prepared inspection input or inherited accepted dependency alone does not satisfy those requirements. The full candidate build, guards and exhaustive axiom audit remain separate mandatory acceptance evidence under the README's applicable normal/fresh rules.

Both independent axes must complete the whole original scope on the actual integration candidate, including necessary corrections and incorporated-base changes. Immediate qualified `./check.sh --verify-candidate HEAD` must precede authorized local integration; a self-contained durability checkpoint follows. No push or GitHub mutation is authorized. Source preparation gives no final approval or chapter acceptance.

This reviewer performed only immutable source/control reads and the authorized new review/provenance writes. No compiler, process polling, runtime/object capture, source/ref/cache modification or chapter activation was performed. All earlier own F/C2/XP01/XR01/XW01/XU04/XU05/XU06 reports and receipts remain byte-identical. Foundation terminal evidence remains the first priority when supplied.

