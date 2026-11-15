## Chapter 4 preflight complete

**Chapter 4 has a complete, intact 76-obligation inventory and substantial reusable tree drafts.** The primary book PDF and extracted text are present at their exact recorded identities. The shared drafts remain uncompiled and unaccepted; their existing source assessments and findings must be carried forward. I made **no file, reference, worktree, Library or compiler changes**.

Once Chapter 3’s exact acceptance and checkpoint 0137 are durable, the next chapter scope can be frozen against accepted candidate `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`.

### 1. Exact chapter scope

The current inventory is:

`/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/research/chapter04-obligations.md`

- **39,471 bytes; 332 lines**
- **SHA-256:** `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4`
- All **76 unique rows, C04-001 through C04-076, occur in exact order**.
- It covers every Chapter 4 subsection, all **11 exercises**, and every named result from **Lemma 4.1 through Corollary 4.12**.
- The optional enumeration `Nodup` strengthening and the maximal-complete-subtree bonus are explicitly retained in the required scope.

The local ticket remains queued at this inspection:

`fdsa-control/tickets/FDSA-004.md`

- **2,683 bytes**
- SHA-256 `048fe208f6379295814722080ec1187385ed7b374bebc93eaaa21a6ce874b7c6`

The governing mathematical conventions are consequential:

- Use Mathlib’s **`BinaryTree α`**, whose labelled nodes and empty leaves match the book.
- `Complete` means all external empty leaves have the same depth.
- `AlmostComplete` means external leaf depths occupy at most two adjacent levels; it does **not** require left packing.
- Preserve arbitrary label types, including `Empty`, wherever the operation does not inherently require equality or ordering.
- Keep semantic observations, recursive cache invariants and resource observations separate.

### 2. Primary inputs and recovery routing

I verified these local primary inputs:

| Input | Size | SHA-256 |
|---|---:|---|
| `/workspace/scratch/b4a17a285e23/research-source/functional_data_structures_algorithms.pdf` | 1,742,029 | `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645` |
| `/workspace/scratch/b4a17a285e23/research-source/book.txt` | 719,122 | `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333` |

I read the complete Chapter 4 extracted-text span: **PDF pages 53–64, printed pages 47–58**. This includes the eleven exercise statements, the complete `bal` recurrence and derived wrappers, generic augmentation, and the maximum-cache exercise. The textual figure 4.3 labels agree with the recorded ten-element balancing example; I did not perform a separate visual PDF review.

The former `book-source` directory is absent. An exact-name, no-ignore search throughout the available workspace found **no** local copies of `Tree.thy`, `Tree_Real.thy`, `Balance.thy`, `Tree2.thy`, or `ISABELLE-COPYRIGHT`. If these proof-reference files are used, recover them at the pinned revision and check their original byte hashes:

**Immutable prefix**

`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`

| Relative path | Required SHA-256 |
|---|---|
| `src/HOL/Library/Tree.thy` | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `src/HOL/Library/Tree_Real.thy` | `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6` |
| `src/HOL/Data_Structures/Balance.thy` | `6d14341de140a4cf5d811798aa1796c143a9127aedfeae0b600f8d174e6bb3fc` |
| `src/HOL/Data_Structures/Tree2.thy` | `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e` |
| `COPYRIGHT` | `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d` |

The pinned book itself is available, so this missing companion-file cache is **not an established blocker to Chapter 4**. I did not attempt network recovery or claim to have re-read those missing theory files.

The existing manuscript-exclusion boundary is preserved: the inventory and ADR0001 exclude research copies of manuscripts from project deliverables. You acknowledged that boundary and will not add the PDF to checkpoint 0137.

### 3. Exact reusable shared drafts

The five directly useful shared units contribute **17 formal source modules**. All are immutable, available through local Git, and still require actual qualification.

| Unit | Exact candidate | Immediate parent | Relevant source |
|---|---|---|---|
| XT01 cached folds | `64c6b777d828ecfe83234fc2aed94600a1f24297` | `a14977b9e316cc484ffad8a470d26b15615956c0` | `Trees/Observations`, `Trees/Cached`, `Resources/TreeCache`, `Examples/TreeCache` |
| XT02 shape bounds | `974a97321a8ec174b56104c7e6efaaca881b6639` | XT01 candidate | `Trees/Shape`, `Trees/ShapeLog`, `Examples/TreeShape` |
| XT03 measured folds | `b0fce71fa00b2ff6250b09002176bdc75baf1f46` | XT01 candidate | `Resources/TreeFold`, three `Examples/TreeFold*` modules |
| XT04 suffix invocation | `b035f1151ab4f0c7d7380818576cfe97dae434c4` | XT03 candidate | `Resources/TreeAccumulator`, two `Examples/TreeAccumulator*` modules |
| XT05 traversal work | `317aae79ff98b90b5525c6dd53bcd815bc6c6e1a` | XT04 candidate | `Trees/TraversalWork`, `Resources/TreeTraversalWork`, `Examples/TreeTraversalWork` |

I read all nine pure/resource core modules in this table completely. I inspected the exact Git deltas and source identities for the examples, but did **not** perform a new complete semantic review of all example modules or assert actual-type credit.

#### XT01’s particularly useful exact source identities

| File | Bytes | SHA-256 |
|---|---:|---|
| `Applications/Trees/Observations.lean` | 4,119 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Cached.lean` | 5,668 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| `Applications/Resources/TreeCache.lean` | 3,877 | `54d6bf9255e4d2b619fcd079a5636bac391aeb44eafe45cc0f4c6abfc2afebf6` |
| `Examples/TreeCache.lean` | 16,307 | `ae78e0f515ba11c9f5348533624df49da59d98887689a16c16a35c3f880fd754` |

XT01 supplies the ordinary ternary fold, map/fusion laws, canonical size/height instances, inorder and map/length laws, annotation erasure, recursive validity, bottom-up annotation, and local measured construction. Its actual local tariff is **callback cost + 3**, from two root reads and one constructor entry. This does not supply a whole-tree traversal theorem or a constant bound for arbitrary callbacks.

The original source assessments remain useful preparation:

- XT01: both complete source axes, zero concrete findings; **115 prepared public names**, unexecuted.
- XT02: both complete source axes, zero new findings; **90 prepared public names**, unexecuted. Retain **XT02-SP01** and its docstring-only correction history.
- XT03: both complete source axes, zero new findings; **88 prepared public names**, unexecuted. Retain **XT03-CP01/DOC01**, with receiving/compiler confirmation still pending.
- XT04: retained bounded source assessments; actual compiler/full/final review gates pending.
- XT05: retained bounded source assessments; preserve **XT05-DOC01** and its source recheck, with final confirmation pending.

The five frozen requirement hashes are:

```text
XT01 81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce
XT02 50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91
XT03 0a83c0b87873c33f2d5bf5aeef655ae4ab2957bb4100202164b217363ed8fcf8
XT04 1c97ae18eb32c4ea582e8ee38162fe7963f3ba54394c919e91b7bd92c1b90477
XT05 454ccd268e41986bcff6abd6d48fd97fee68baad637ec1840b3cd4b39925e9f0
```

Their recorded dependencies require XT01 acceptance before XT02/XT03 integration or acceptance, XT03 before XT04, and XT04 before XT05. Preserve those recorded gates and original review scopes when choosing the receiving sequence.

**Do not import their old `SquareApplications.lean` or reconstruction map wholesale.** Each belongs to an old branch context. Carry the exact selected source additions and reconcile the current public entrypoint and documentation deliberately, retaining accepted Chapter 3 content.

### 4. Chapter 4 coverage map and remaining implementation

| Obligations | Available starting point | Required remaining work |
|---|---|---|
| C04-001–016 | Mathlib carrier; XT01 inorder/map/fold; XT02 minimum height and bounds | Independent element-set observation, preorder, structural subtrees, preorder/set bridges, checked source correspondence |
| C04-017–018 | XT03–XT05 actual fold, append, suffix invocation and shape-sensitive cost families | Exact Chapter 4 recurrence/tariff adapter and connected acceptance evidence |
| C04-019–020 | Mathlib finite unlabelled shape enumeration | Executable labelled enumeration with exact prescribed inorder, soundness, completeness, termination and `Nodup` even with repeated labels |
| C04-021–022 | Ordinary fold and induction infrastructure | Natural-weight path-length definitions and arbitrary-depth offset theorem |
| C04-023–026 | Basic list APIs | One-tree-traversal `levels`, no natural-number parameter/arithmetic in its algorithm, length and indexed correspondence |
| C04-027–028 | Inorder/preorder observations | Total reconstruction, distinct-preorder correctness, explicit duplicate counterexample |
| C04-029–030 | List reverse/map | Matching ordered rose-tree carrier, recursive mirror, nested involution proof |
| C04-031–037 | XT02 complete/leaf/log laws | Source-facing executable checker correspondence; draft has Prop invariants and deliberately excludes Boolean checker |
| C04-038–041 | XT02 completeness/height facts | One-traversal maximal complete structural subtree, maximality, equality-free bonus |
| C04-042–046 | XT02 almost-complete bounds and cross-type height optimum | Structural-subtree closure and final correspondence; child closure is already drafted |
| C04-047–058 | Accepted logarithm-halving result; XT02 shape laws | Full sequential prefix balancer, safe domain/failure interface, exact suffix consumption, wrappers, height/min-height laws, figure and corrected ordering connection |
| C04-059–060 | XT02 predicates | Exact almost-complete node characterization with the shorter-child completeness condition |
| C04-061 | Existing `Measured`/`CallCount` | Actual balancer execution and linear count under the explicit source tariff |
| C04-062–073 | XT01 generic caches and local cost interpretation | Full source-facing specializations/observation aliases, erased element-set bridge, valid-child and local-cost connections |
| C04-074 | XT01 generic fold/cache; XT02 completeness | Boolean/height summary, correctness and smart-constructor preservation through generic interface |
| C04-075–076 | Generic cache infrastructure | Raw label-valued maximum cache, empty `Option` result, maximum specification and explicit generic-interface bridge |

#### Existing accepted logarithm reuse

At the exact current candidate, `Applications/Resources/BottomUpSorting.lean` contains:

- `Resources.BottomUpSorting.clog_two_ceil_half`
- `Resources.BottomUpSorting.clog_two_source_half`
- `Resources.BottomUpSorting.int_ceil_logb_two_nat`
- `Resources.BottomUpSorting.int_ceil_logb_two_source_half`

The shifted recurrence needed by balancing can use the source-half theorem at `n + 1`, retaining the necessary positive-size premise. File identity inspected: **23,175 bytes**, SHA-256 `74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826`.

There is no reason to pull the unrelated unaccepted XL01 real-logarithm inequality unit merely to obtain these already available halving facts.

#### Ordering reuse without importing rotations unnecessarily

For the corrected sorted-input interpretation in C04-058, an existing pure module is available at:

`66eae34815a177c6b4bf5120e05202ebb8876c91:Applications/Trees/Ordered.lean`

- **5,817 bytes**
- SHA-256 `26549e623acdce3ac29e3fdd30858eb068c1bf7cd5f223468bbcbb30ecffbe66`
- Imports only `Trees.Observations` and Mathlib list sorting.
- Provides recursive `Trees.Ordered`, equivalence with pairwise inorder under transitivity, strict-key sortedness, and `Nodup ∧ SortedLE` correspondence.

The separate `OrderedRotations` module depends on rotation/cache units. The pure `Ordered` module itself does not. Any bounded reuse of that pure source must retain provenance and receive validation; it must not mark the full XT07 ticket accepted or silently incorporate the rotation branches.

### 5. Implementation choices worth fixing before parallel work

These are preparation recommendations, not implemented or approved results.

1. **Enumeration:** a direct recursion over root positions is a straightforward executable route. Enumerate each prefix/suffix pair and construct nodes; distinguish root positions by left-subtree size to prove no duplicates without requiring distinct labels. I inspected the pinned Mathlib Catalan tree file: its shape enumeration and membership theorem are available. However, pinned `Finset.toList` and `Multiset.toList` are explicitly **noncomputable**, so simply applying `Finset.toList` does not meet the executable list-enumeration requirement.

2. **Balancing:** use the established explicit domain or `Option` policy. The recursive right call must consume the suffix returned by the left call, then its head/tail. Replacing this with repeated `take/drop` would require a different cost theorem. Keep `n = 0` and too-short input behavior explicit, and avoid a global `Inhabited α`.

3. **Maximal complete subtree:** a single traversal can return a completeness flag, height, best subtree and best height. This meets the no-`complete`/no-`subtrees` implementation restriction and the no-tree-equality bonus. The proof must establish structural membership as well as completeness and maximal height.

4. **Maximum caches:** raw annotations should remain label-valued, with `none` only at an empty tree. A map from raw cache `b` to optional cache `some b` can connect this representation to generic zero=`none` augmentation. The representation bridge must be proved; adding `OrderBot α` or silently changing the raw representation would alter the source requirement.

5. **Resource distinctions:** preserve the three append interpretations and the retained XT03 raw/wrapped-term bridge. The balancer’s `2*n + 1` recursive-entry count does not grant the displayed direct-inorder `balanceTree` wrapper a linear bound. The direct traversal has quadratic left-chain and linear right-chain families under the same tariff.

6. **Completeness/height summary:** share one independently specified Boolean/height combine operation among the executable completeness checker, Exercise 4.10’s cache specialization and, where appropriate, the maximal-subtree traversal. This avoids parallel authors inventing incompatible versions of the same summary.

### 6. Safe parallel work partition

After checkpoint 0137 is complete and you explicitly release the next source work, a three-author split can keep writes disjoint:

| Author stream | Ownership |
|---|---|
| Structural observations and augmentation | Missing set/preorder/subtree bridges; checker correspondence; complete/almost-complete extensions; maximal complete subtree; size/completeness/maximum cache specializations |
| Traversal exercises | Enumeration/Nodup, weighted path lengths, levels, reconstruction and rose-tree mirror; retained accumulator/source correspondence as assigned |
| Prefix balancing | Safe sequential `bal`, wrappers and suffix contracts, exact shape/log laws, actual measured execution, ten-element example and strict-order connection |

First freeze the shared carrier, inorder, subtree and complete/height summary names on the receiving base. Give each author separate source/example paths and a clean isolated branch. Root should own the public entrypoint, correspondence ledger, reconstruction map and integration commits. Root remains the only serial compiler.

The existing shared-unit source and review histories should be continued through their recorded prerequisite gates. The eventual Chapter 4 whole-task review must still account for all 76 obligations against its fixed original chapter base, including all received shared work and new corrections.

### Read receipts and limits

Key read-only tool receipts:

- Governing instructions and current chapter ticket/index: `642151`, `260638`, `52e21e`, `7d4703`, `3b5deb`.
- Complete inventory reads: initial `7dc880` showed the first section but was globally truncated; the remaining sections were subsequently read untruncated in `597ce0`, `042586`, `f589a0`. Exact ordered 76-row reconciliation: `76876d`.
- Exact XT01 records and requirements: `651d01`, `73f222`.
- Complete shared core sources: `ab553e`, `4ac297`, `30e539`.
- Branch/parent/delta/source identities: `858579`, `e3fb85`.
- Book hashes and complete Chapter 4 text: `9808a3`, `f37773`.
- Missing companion-source search: `5ba801` — exit 1 with no matching filenames, an ordinary no-match result.
- Additional ordering/rotation boundaries: `42fcc8`.
- Mathlib pin and `toList` computability check: `a8640a`.

**No Lean, Lake, build, audit, candidate verification, test, Git mutation, checkpoint write or upload occurred in this preflight.**
