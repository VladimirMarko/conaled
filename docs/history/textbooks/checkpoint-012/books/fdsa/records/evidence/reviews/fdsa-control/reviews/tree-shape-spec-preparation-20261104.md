# XT02 tree-shape bounds — independent Spec source preparation

## Current disposition

**Overall: Blocked. Source assessment complete, with zero new concrete Spec findings.** This continues the existing FDSA-XT02 loop at original immutable candidate `974a97321a8ec174b56104c7e6efaaca881b6639`, over fixed original base `64c6b777d828ecfe83234fc2aed94600a1f24297`. The scope remains all six original paths and all 838 added lines. Frozen requirements are version 1, SHA-256 `50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91`.

No XT02 compiler, actual public-type inspection, candidate check, audit or final acceptance is credited. XT01 remains a prerequisite to this unit's eventual integration and acceptance. Accepted Chapter 1 and Foundation retain their accepted states; historical November 2 records about the formerly active Chapter 1 gate are not treated as current status. No chapter is activated, and the current combined-four candidate's full validation retains priority.

**XT02-SP01 is preserved and its source correction independently confirmed.** The original necessity wording was wrong; the candidate now states the sufficient implication that its unchanged theorem actually proves. Final acceptance confirmation remains pending with all other exact-candidate gates. The prior bounded contributors are retained as implementation support, not substituted for this independent axis.

## Scope, inputs and complete reading boundary

The actual parent and merge-base are both the fixed XT01 draft B. The nonempty three-dot/full-index diff is 43,643 bytes, SHA-256 `0e85b5703fb3bca8d1ee1d779ba64410d81e6a57f79359995ccecb0b80b09224`. All six file sizes, line counts and SHA-256 identities match the original source-identity handoff.

| Candidate file | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `Applications/Trees/Shape.lean` | 267 | 11,019 | `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3` |
| `Applications/Trees/ShapeLog.lean` | 69 | 2,796 | `35c0555383fc3d03bcac4f368d41b2c8f744a49e18ef72b192c3753b7ef4497b` |
| `Examples/TreeShape.lean` | 297 | 12,648 | `2bcf2b65fa7a0eccc043c3bc7ba66d1bfdcd469489eab52d9085fdfb3db0b516` |
| `SquareApplications.lean` | 254 | 8,344 | `3ce2c9953286d48d62aa8c354af5d1a1e07c483dbe57974f0beb97124db5effb` |
| `docs/research/fdsa-reconstruction-map.md` | 311 | 20,055 | `a9425275ce38e4a0c49b5bca9219bb38c6afcc36b65e6e7874e5c4e88a1fdc3b` |
| `docs/research/fdsa-tree-shape.md` | 180 | 12,279 | `9645f569674f6245d6eea53b40e409ae8fa69bd4b74955cccbf3a92a837a4228` |

I read the three complete new Lean modules, the complete new reconstruction note, and every root/map change using immutable Git blobs. The unchanged root/map bodies retain their complete prior XT01 assessment at exact B; no fresh whole-file reread of those unchanged bodies is claimed. The complete 233-line requirements, ticket, start and candidate handoffs, all source-identity fields, all 145 lines of retained source-review history and the three complete preflights were read. Their exact identities and boundaries are in the accompanying receipt. I applied the existing AGENTS, architecture/domain, code-review, example-driven and shared review-loop instructions without creating a replacement loop.

The complete unchanged `Trees.Observations` (107 lines), `Trees.Cached` (135 lines) and `Examples.TreeCache` (363 lines) were independently read again to check the actual fold, map, cache and fixture connections. Pure import traversal records 29 local files, 14 external module imports and 54 edges. Three local files are the new XT02 modules; all other 26 local files equal B exactly. This is source accounting, not evidence about compiled objects or receiving-candidate reuse.

The actual manifest still selects Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and Lean `leanprover/lean4:v4.35.0`; `lakefile.toml` and both pin files are unchanged. The existing leftist and random-access carriers are untouched. The draft reuses the existing carriers and interfaces, without an extra payload constraint, executor, balance framework or logarithm implementation.

## Primary-source and pinned-API correspondence

I checked the supplied manuscript identity directly: PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`, 1,742,029 bytes. The supplied extracted text has SHA-256 `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`. The complete text of printed pages 47–49, 51–54, 128–130 and 183–186 was read. Page 49 supplies the height/minimum-height recurrences and universal powers, pages 51–53 supply recursive completeness, strictness, almost completeness, optimum and rounding, and the later pages establish the separate Braun and leftist applications and their additional premises. This was a text/source assessment, not a fresh image-rendering or enumeration claim.

The retained preflights attribute `Tree.thy` and `Tree_Real.thy` to Isabelle revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, with hashes `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` and `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6`. I retain that precise attributed inspection and BSD-3-Clause provenance. I do not claim a fresh full read or rebuild of either theory or identify that later mirror pin as the manuscript build revision. Neither theory is a Lean proof dependency.

Actual immutable Mathlib source was inspected for the BinaryTree carrier/count/height conventions, the precise Nat log and ceiling-log implications and argument orders, all four Real logb/rpow order equivalences with their enclosing base-greater-than-one binder, both natural floor/ceiling bridges and `Real.rpow_natCast`. The latter has no extra sign premise; the analytic equivalences do require positive leaf count, which the candidate obtains from the canonical theorem. Exact file identities and read ranges are preserved. Source/API agreement supplies no elaboration credit: tactic inference, casts and all actual public types remain to be checked.

## Full mathematical assessment

### XT02-01: source observations and recursive meanings

`minHeight` is the existing ordinary fold with base zero and combine `min left right + 1`, giving external empty-leaf distance. Nil has minimum and maximum height zero; a singleton has both one. The map law allows arbitrary, noninjective label maps between independent universes. The proof of `minHeight_le_height` uses the actual child inequalities and min/max ordering, without an inhabited or nonempty premise.

`Complete` is genuinely recursive: nil is True; a node requires equal child heights and both children complete. The equivalence with equality of minimum and maximum heights is proved from the independent definition and induction, not used as its definition. `AlmostComplete` has the intended additive height-gap bound and its exact natural-subtraction equivalence. Complete implies almost complete; the latter passes to both children; both predicates are map-invariant. No payload order, decidable equality, finiteness or default value is assumed. These facts express the source's perfect-tree/external-depth convention, not left packing or an executable Boolean checker.

### XT02-02: sharp capacities and their converses

The two universal leaf bounds use structural induction and the appropriate exponent monotonicity, with nil included. Complete trees attain both bounds. Incomplete trees make both inequalities strict. The upper proof splits child maximum heights; the lower proof splits child minimum heights. In its equal-minimum case the completeness/height equivalence is used to show that two complete children would make the parent complete. The proof does not silently assume almost completeness or nonemptiness.

Both equality converses follow from those strict bounds with the correct equality orientation; in the lower-bound converse the supplied equality is reversed before contradiction. They characterize equality at the tree's own height or minimum height. An arbitrary power-of-two leaf count is explicitly insufficient, as the three-node chain shows.

### XT02-03: natural rounding and cross-type optimum

The universal rounded inequalities consume the actual power bounds. The exact almost-complete formulas split complete from incomplete trees. In the incomplete branch, the independent completeness equivalence and almost completeness give `height = minHeight + 1`; the strict power bounds then identify the floor and ceiling. The ceiling proof avoids a predecessor expression that would fail at height zero. Complete/nil cases use the exact standard logarithms of powers.

`height_optimal` quantifies over two unrelated payload types and universes. Only the first tree is almost complete, and the size premise is the full node-count inequality. The proof converts nodes to external leaves using `numLeaves = numNodes + 1`, then combines the first tree's exact ceiling with the arbitrary competitor's capacity bound. There is no strict-height strengthening, converse, equal-size restriction, common-label coercion or positive-size existence claim over an empty type.

### XT02-04: actual real statements

The separate ShapeLog module proves the actual real sandwich and both strict incomplete bounds. Each proof supplies base two greater than one and the positive canonical leaf count, converts real exponentiation at a natural exponent, and consumes the corresponding discrete theorem. The complete real height equality follows from the sandwich plus the completeness/height identity. The natural floor and ceiling corollaries consume the pinned `Real.natFloor_logb_natCast` and `Real.natCeil_logb_natCast` directly. Their types use natural rounding; the positive leaf count makes the source's logarithm nonnegative. Nil has one leaf and remains in every universal statement. No floating-point approximation or substituted arithmetic definition appears.

### XT02-05: complete connected cases and consequential boundaries

| Case group | Actual connection and assessed consequence |
|---|---|
| Empty payloads and singleton | `empty_tree`, nil predicate laws and the completeness/height equivalence are used. Arbitrary `BinaryTree Empty` values are necessarily nil, without claiming a positive-size inhabitant. Natural logs are connected through the almost-complete theorems and the empty real equality through the complete real theorem. |
| Complete three-node tree | The upper-capacity equality converse establishes completeness; minimum-capacity equality, minimum height two and real height equality consume the public results. Its four leaves are the relevant external count. |
| Right-heavy two-node chain | It is incomplete and almost complete, with three leaves, minimum one and height two. Both public strict power bounds and actual strict real bounds are used. Its exact Nat floor/ceiling equalities establish failure of strict rounded bounds. Child closure and the subtraction equivalence are exercised. Its orientation excludes hidden left-packing assumptions. |
| Saved asymmetric sample | The actual Nat-labelled XT01 sample has four nodes, five leaves, minimum two and height three. Its almost completeness supplies natural and real rounding; the separate node-offset counterexample rejects replacing `numNodes + 1` by `numNodes`. |
| Noninjective map and annotation erasure | The constant Nat-to-Unit map preserves the actual sample's shape, and a label map preserves complete shape. General erasure uses `Prod.fst` and the map theorems. The actual saved pair annotation consumes its erasure law. No cache-validity assumption is added for shape preservation. |
| Malformed annotation and real minimum cache | The saved corrupt size annotation has the same erased sample shape while recursive size validity fails. This is not a claim that corrupt size fields compute minimum height. Separately, `minSample` is constructed by actual `Cached.annotate`; its validity and erasure connect `min_reader` to a root result of two. No measured tariff or executor is added. |
| Power count and optimum nonconverses | The three-node chain has four leaves but fails completeness. The Bool-labelled four-node witness has five leaves, minimum one and height three; comparison with the Nat-labelled sample uses the generic optimum. The generalized theorem proves its optimality against arbitrary competitors with at least four nodes, paired with explicit failure of almost completeness. Equal ceiling height alone does not characterize almost completeness. |
| Recursive sibling-height balance | The private example predicate requires both local inequalities and recursive conditions at every node. The seven-node fixture has eight leaves, minimum two and height four, satisfies that predicate and fails almost completeness. The counterexample is not merely a root-balance test or a new AVL library. |
| Arbitrary saved chains | The universal rounded bounds apply to every `chain n` through the public core results, without an almost-complete premise or an unjustified equality claim. |

The public example theorem `localBalanceCounter_balanced` refers to the private recursive predicate in its type. Its meaning has been inspected in full; the private predicate remains included in source and future exhaustive audit scope. The future actual public-type inspection must retain that actual premise rather than treating a hidden generated name as an unexplained assumption.

## XT02-SP01 retained finding and correction

The original snapshot has 12,640 bytes and SHA-256 `9b0aacf07d1e9fe62f540abba5d24a387f3e962c9711d253fdb8d105001436f7`. Comparing it with the exact candidate gives precisely one docstring replacement at line 200: the old claim that a cached minimum is correct “only under” all-node validity becomes the sufficient claim that recursive validity makes it agree with the structural observation. Every formal source byte outside that comment is unchanged.

The original independent counterexample is mathematically valid: a root cached at one, with a left singleton cached incorrectly at 99 and a nil right child, reads one and has structural minimum one; even the root's local min equation holds, while recursive child validity fails. Thus necessity was false. The actual `min_reader` theorem requires `Cached.Valid 0 minStep t` and concludes equality, exactly the sufficient direction. It consumes `Cached.read_eq_fold` and unconditional erasure/map invariance. The corrected note also states that invalid descendants can coexist with an accidentally correct root. This confirms the recorded source correction without rewriting its history or inferring compiler/final acceptance.

## Explicit authored inventory and remaining source boundaries

| File | Public definitions | Public theorems | Private definitions | Instances / anonymous examples |
|---|---:|---:|---:|---:|
| Shape | 3 | 26 | 0 | 0 |
| ShapeLog | 0 | 7 | 0 | 0 |
| TreeShape examples | 8 | 46 | 1 | 0 |
| **Total** | **11** | **79** | **1** | **0** |

There are 90 explicit public names and one private name. The receipt preserves every name, source location, complete authored header, visibility and hash. For `Complete` and private `SiblingHeightBalanced`, equation-style headers stop before the first leading `|`, excluding their bodies. These counts are source inventory, not kernel declaration or new accepted-theorem counts. Generated declarations are not guessed or exempted from future full audit. No actual XT02 public type has been printed or assessed.

The public root's sole addition reaches all three new modules. The new map section and complete note retain all original limits: no tree enumeration, executable completeness checker, maximal/complete/almost-complete constructor exercise, arbitrary subtree framework, weight/Braun invariant, array operation, search invariant, leftist adapter/refactor, runtime or storage/sharing result. Chapters 4, 11 and 15 keep those full obligations; a shared source connection does not close any chapter row. Existing leftist `rank_paths`, `rank_size` and `rank_log`, and the distinct leaf-labelled random-access tree, are unchanged.

## Gates and preservation

The original scope, B/C history, all five frozen requirement groups and XT02-SP01 must survive incorporation of accepted prerequisites. All applicable focused compatibility/build obligations, the immutable complete candidate check, exhaustive audit, complete actual public-type inspection and both independent final axes remain mandatory. Immediate qualified verification must precede any acceptance fast-forward. The Nix waiver changes only the allowed environment route; it does not relax pins, proof restrictions or any mathematical requirement.

No compiler, project checker, build/cache/output command, process poll, source edit, Git mutation, remote mutation, image render or enumeration was performed for this preparation. One read-only metadata lookup used the wrong `lakefile.lean` filename; the actual tracked `lakefile.toml` was then found and compared. That lookup error is retained as reviewer bookkeeping, not a source or compiler failure. Earlier held F/C2/XP and all other source reports, including the combined-four I package, remain unchanged.

This report and `provenance/tree-shape-spec-preparation-20261104/source-assessment.json` are a source-preparation continuation only. Overall disposition remains **Blocked** until actual validation and prerequisite integration are established for the eventual immutable acceptance candidate.
