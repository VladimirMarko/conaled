# XT03 measured tree folds — Standards source preparation

**Source assessment complete; no new concrete Standards source finding. Overall outcome: Blocked pending actual validation and all final gates.** This is the independent Standards preparation by `/root/chapter02_standards` for the existing cross-cutting XT03 unit, at original immutable candidate `b0fce71fa00b2ff6250b09002176bdc75baf1f46` over `64c6b777d828ecfe83234fc2aed94600a1f24297`. The reviewer authored none of the included formalization. This does not activate Chapter 4 or approve a receiving integration.

The complete original seven-path scope, frozen requirements and cases are retained. XT01 acceptance remains the integration prerequisite; XT02 is not a prerequisite. All earlier C1/Foundation/shared-four acceptance records and C2/XP01/other source preparations remain unchanged.

## Immutable scope and complete reading

The original base is both the candidate's sole parent and merge base. Candidate tree: `b66d05bc7733290057c6104bcc5a74c43b4037a4`. The full original diff contains seven paths and 975 additions, with no deletions; its full-index binary patch is 51,952 bytes / 1,024 lines, SHA-256 `92fc6f768b50d9bf6c982e047e9118205db8c84078b90a60456d0eaa3c865991`.

All seven resulting files were independently read completely: **75,017 bytes / 1,515 lines**, including all 698 lines of the four declaring Lean modules. These are the resource core, three connected example modules, the public root, the full new note and the complete reconstruction map. The frozen 288-line requirement file is unchanged at SHA-256 `0a83c0b87873c33f2d5bf5aeef655ae4ab2957bb4100202164b217363ed8fcf8`. The entire ticket, start/candidate records, source identities, original source assessment and source/API/case preflights were read; original correction snapshots and complete affected diffs were checked separately. Historical source preflights are evidence aids, not a replacement for this independent assessment.

The [read ledger](../provenance/tree-fold-resource-standards-preparation-20261104/read-ledger.json) records exact file identities, contiguous bounded reading ranges, retained prior readings and pinned API contexts. Seventeen applicable repository instruction identities match previously completely read instructions, including AGENTS, the implementation/shared review loop, code-review heuristics, example-driven guidance, domain modeling and architecture rules. No truncated output is counted as complete reading.

## Exact declaration inventory

| Declaring module | Public names | Theorems | Definitions | Abbreviations |
| --- | ---: | ---: | ---: | ---: |
| `Applications.Resources.TreeFold` | 14 | 13 | 1 | 0 |
| `Examples.TreeFold` | 26 | 24 | 2 | 0 |
| `Examples.TreeFoldCache` | 22 | 21 | 1 | 0 |
| `Examples.TreeFoldObservations` | 26 | 19 | 6 | 1 |
| Total | **88** | **77** | **10** | **1** |

There are no authored private declarations, anonymous examples or new instances in these four files. Every explicit public name, kind, source line, raw header, UTF-8 offset and header hash was independently derived from immutable source and reconciled against the separately prepared 88-name inventory. Headers include same-line attributes and end immediately before `:=`, retaining preceding whitespace; all 88 use this delimiter. The `@[simp]` prefix on `run_nil` is included. Compiler-generated auxiliaries remain a future elaboration/audit boundary, not fabricated entries in this authored inventory.

The complete [source assessment and inventory](../provenance/tree-fold-resource-standards-preparation-20261104/source-assessment.json) preserves all 88 rows and their original statement forms. The prepared statement input is not an executed inspection; **actual XT03 type credit remains zero**.

## Mathematical statements and minimal assumptions

The generic `run` is one specialization of the existing ordinary `Trees.fold`. It computes the left result, the right result and then the actual combining callback, retaining all three observations and adding the structural entry last. Its raw interface requires only `Add C`; the exact grouping is left observation plus the sum of right/callback observations, then entry. It does not impose commutativity, a zero element, an order on costs or an inhabited payload. The nil case contains the declared entry observation. There is no separate recursively defined cost-only evaluator that could become disconnected from the returned value.

The unconditional value theorem retains the actual callback first projection. Entry independence concerns the value, not the observation. The specialized pure-fold theorem states its sufficient callback value law explicitly, while fold/map and value fusion use existing structural interfaces. These equalities neither execute nor pay for a second erasure/recomputation pass. Function-valued results remain permitted by the generic carrier, without claiming later invocation work has been measured during construction.

Reweighting maps the same measured execution through an additive monoid homomorphism. Its stronger algebraic context is local to that law; it does not weaken or overconstrain the raw Add-only definition. The actual pinned homomorphism and product-projection interfaces support the intended composition without an extra project framework.

For natural costs, the entry-change law gives the entry-zero work plus `entry * (2 * numNodes + 1)`, including nil calls. The structural lower bound and exact constant-callback formula retain all callback work. The upper-bound theorem quantifies one fixed `K` over the callback applied to the actual summaries of arbitrary left/right subtree runs. This is a uniform bound over the reached family, not a choice of a new `K` for each tree size and not a requirement that unreachable summary pairs satisfy the same bound. The constant-cost theorem has the analogous explicit premise with one fixed `k`.

## Connected operations and examples

The size and height clients use the existing actual measured callbacks and recover both their ordinary observations and exact structural costs. Empty-carrier and nil cases do not obtain an artificial default element. The inorder clients distinguish three actual append associations. Their node callback work is respectively `left.length + 1`, `left.length + 3` and `2 * left.length + 3`; their concrete sample totals are 15, 23 and 25 despite the same inorder value. These values and costs belong to connected executions, rather than independent cost expressions chosen to fit an expected result. The source algorithm and explicit alternative associations remain distinguishable.

The full annotation examples compose the same fold with the existing measured local `TreeCache.nodeRun`. Their value, recursive validity, erase and cached-read laws concern the actual returned tree. Size/height annotations give exact work `entry * (2*n+1) + 3*n`, hence `5*n+1` at unit entry and sample work 21. The list-cache recurrence keeps the callback's actual child reads and the additional `left.numNodes + 4` work; its sample work is 27. No unmeasured child recomputation is substituted for a cached read, and no second pass is silently supplied by a value equality.

Product observations separately retain structural and callback work from the actual execution. The first/second projections and their additive sum are homomorphic observations of that same run. The generic core is also exercised with `Additive (FreeMonoid Nat)`, making order observable: the sample callback word is `[0,2,3,1]`, and a singleton with entry tokens records `[0,0,1,0]`. Collecting its entries at the end gives `[1,0,0,0]`, so the explicit counterexample rules out extending the natural commutative collection law to arbitrary noncommutative observations.

The `resetStep` boundary returns summary zero and costs zero on reached child summaries `(0,0)`, while the unreachable pair `(1,0)` costs seven. Its exact structural-work theorem still pays for both recursive child runs although their summaries are discarded. This is a consequential use of the reached-summary bound, and its non-global-cost theorem prevents a hidden strengthening to all arbitrary summaries.

## Architecture, APIs and dependency boundary

The implementation stays in the existing Trees/Resources domains and uses ordinary fold, cached-tree validity/read laws and measured bind/tick/reweight operations. It adds no callback typeclass, reachability record, tree-count carrier, history framework, translator or parallel resource semantics. The public root adds the example observation module, which reaches the other three new modules through its imports. No checker/audit implementation, policy exclusion or pin is changed.

The independently reconstructed original closure contains **30 local files, thirteen direct external import names and 56 edges**. Its four new declaring roots and all 26 inherited sources match the separate prepared inventory. All 26 inherited sources are exact original-base bytes; the 22 older inputs are also exact accepted Chapter 1 bytes. The [dependency receipt](../provenance/tree-fold-resource-standards-preparation-20261104/dependency-closure.json) retains the full graph and identities.

Complete prior readings of the unchanged XT01 Observations, Cached, resource TreeCache and all TreeCache examples remain valid by exact source hashes. The complete relevant Measured, CallCount, ListReversal, TreeFlattening and OrderedSummary readings are likewise retained. The recorded SymmetricCosts context is only lines 1–80, and the other transitive graph entries are not misrepresented as newly read whole files. Later XP01 candidate T changes only `Potential` among those 22 older inputs, through the ListReversal/SymmetricCosts chain. A future receiving candidate must account for that concrete compatibility boundary; it is not a new XT03 prerequisite or automatic reason to transfer earlier type evidence.

Pinned Mathlib source contexts were independently inspected for product homomorphism projections/inclusion, additive homomorphism addition, additive type-tag operations and monoid structure, free-monoid list/word constructors and laws, and the rewrite-transparency distinction relevant to the retained correction. They match pin `56a005855ea17e0b0958f73ec801ae140b0a1679`. All ten original configuration/policy source identities match the base. These are source/API checks, not runtime or compiled-object qualification.

Book/Isabelle identities and correspondence remain grounded in the completely read frozen requirements and source/API/case preflights. No new PDF/theory fetch, rendering or fresh whole book-text reading is claimed. This Standards assessment independently evaluates the formal source and the stated model boundaries; source summaries do not supply compiler, type, audit or acceptance evidence.

## Preserved findings and scope corrections

**XT03-CP01 remains in the existing record.** The original wrapper-sensitive rewrite sequence in `list_node_cost` was replaced by an explicitly typed raw child-read equality, a recurrence hypothesis for the same actual callback/run and a final restricted `simpa only [annotateRun]`. The complete before/after diff and current source were independently assessed; all 22 raw declaration headers in the cache-example module are byte-identical across that correction. This is an adequate source correction to the identified elaboration risk, with no changed mathematical statement. Actual compiler and final-candidate confirmation remain pending. No original compiler failure or successful elaboration is invented.

**XT03-DOC01 remains in the existing record.** The exact note/map correction preserves every original book obligation in its owning chapter while making clear that excluded optional mechanisms do not impose a new generic translator/history framework or a particular auxiliary statistic. It changes neither the frozen requirements nor the formal source scope. Its source correction is independently confirmed; final receiving-candidate confirmation is still required.

No new mathematical, minimal-assumption, architecture, example or documentary finding was identified. Two read-only inventory bookkeeping failures are preserved honestly: the first matcher omitted a same-line attribute; the corrected 88-row comparison then succeeded before a separate attempt to sort dictionary-form edge records without a key failed. Complete keyed edge comparison subsequently passed. These were metadata-analysis errors, with no source change, compiler invocation or validation credit.

## Remaining gates and disposition

The four new modules retain `autoImplicit false` and `warningAsError true`. Source inspection finds no admission, new axiom, unsafe/partial/native-decide declaration or linter suppression. Kernel and axiom compliance still require the actual future full audit; source inspection does not establish them by itself.

The existing sequence still requires accepted XT01, an exact history-preserving receiving incorporation, the applicable qualified compiler checks, complete actual public-statement inspection with concrete affected compatibility evidence, a successful whole-candidate check and exhaustive audit, a matching verification record, both independent final axes and immediate qualified verification before acceptance. Normal versus fresh and focused-check reuse follow the repository's existing rules; this preparation introduces no new gate or scope requirement.

**Final source-stage disposition: complete original XT03 Standards assessment, zero new concrete source findings, inherited corrections retained with their pending formal confirmation. Overall Blocked. Actual compiler/type/full-check/audit/acceptance credit: zero.** Only this reviewer's new preparation records were written. No mutable worktree source, ref, compiler, process, runtime, output, cache, pin, ticket or global control was changed. Hold the new package after complete readback.
