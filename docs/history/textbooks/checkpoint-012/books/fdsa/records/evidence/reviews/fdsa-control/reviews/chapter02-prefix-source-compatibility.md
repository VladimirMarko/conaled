# Initial Chapter 2 prefix: compatibility with the Chapter 1 repair candidate

Date: 2026-11-02 UTC. Status: bounded source-only integration preparation; stopped after the readback recorded by the author handoff.

## 1. Finding and scope

No concrete public-statement or import compatibility obstruction introduced by the exact Chapter 1 repair candidate was found for the six saved initial Chapter 2 modules. The decisive evidence is that the repair adds four Lean files and changes the aggregate root imports, but changes none of the existing Lean files consumed by this prefix. The six prefix files are separate additions. Their measured-value, call-count, list, sorting, rank, and notation dependencies retain the same source bytes at the common base, the repair candidate, and the saved prefix.

This finding is deliberately narrower than a successful integration or a mathematical acceptance. It does not establish that the saved prefix elaborates, that a future combined tree builds, or that either chapter has passed its required reviews. Chapter 1 acceptance remains a prerequisite to integration. No source changes, conflict resolution, replacement prefix, new worktree, compiler invocation, project verification helper, or review loop was performed for this assessment.

The complementary root-import and reconstruction-map content reconciliation belongs to the architecture agent. This report identifies the precise imports that must survive and evaluates the source consumers; it does not create or approve a merged file.

### Exact version inputs

| Role | Exact Git commit |
|---|---|
| Common base, abbreviated `B` below | `1aabd512284fe86254278ac631eda061d311050b` |
| Chapter 1 repair candidate, abbreviated `R` | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Original initial Chapter 2 prefix, abbreviated `P` | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |

The read-only `git merge-base R P` returned exactly `B`. These immutable revisions, rather than the current contents of any Chapter 2 worktree or a later shared-unit branch, define this assessment.

The full input note was read: `fdsa-control/reviews/shared-integration-preflight.md`, 24,778 bytes, 205 lines, ordinary SHA-256 `e1d9c119e2bca35bbbd283eb47d05330f35d7e548f92e063eeebe7d4d53552eb`. Its historical repair and validation handles are not adopted as current status. This report uses the newly assigned exact `R` and does not report the status of the root-owned compiler process.

`P` ends with the Empty-index notation boundary. The later XP01 and affine-reversal commits are outside this prefix. Shared-unit implementations, including the later measured merge and ordered-tree search work, are also outside it. No later change to `Potential`, `FIFOContracts`, or a shared tree/merge API is assumed to be available here.

## 2. What was inspected

Git reads ran through the repository's pinned Nix development environment in `/workspace/scratch/845aa1048b05/conaled-ch01-cost-models`, with `GIT_OPTIONAL_LOCKS=0`. The operations were commit inspection, merge-base calculation, tree/path enumeration, `git show`, literal import search, and `git diff --no-ext-diff`. Ordinary Python byte comparisons and SHA-256 identities were used for evidence; no project hashing or verification program ran.

The author read all six prefix files below in full at `P`, all four new Chapter 1 Lean files in full at `R`, and all seven existing interface files in section 4 in full at `R`. The latter files were also compared as complete byte strings at all three commits. The two aggregate-root diffs were read in full. Build-input files were compared byte for byte; this is an identity check, not a build-system or dependency audit.

The first combined read of the six prefix files truncated a small part of the initial `ListCalls` output; a separate read recovered its first 45 lines. No omitted fragment is being counted as a full read. A read-only attempt to inspect a guessed `lakefile.lean` path failed because this repository uses `lakefile.toml`; root-tree enumeration supplied the actual path before the successful comparison. Neither read caused a repository mutation.

### Complete focused prefix sources at `P`

| Full path | Bytes | Lines | Ordinary SHA-256 |
|---|---:|---:|---|
| `Applications/Resources/InsertionSort.lean` | 7,257 | 178 | `385ea0ba077ac05a10547bc95cd37eb4fa80ef8fe826c6e2c250cca33f2b4aad` |
| `Examples/InsertionCosts.lean` | 3,862 | 101 | `f808254936f1757e639b4f49d94904056b92c84802d9a887a16d31c861c7ff37` |
| `Examples/ListLibrary.lean` | 6,761 | 170 | `036cf4c12ddf5d25ce433d9f7dbedfcbb96dfc3c7f602d10605388d2791e47ad` |
| `Applications/Resources/ListCalls.lean` | 7,970 | 190 | `fba668d88d4c929543a4d5337314761f74f9958cbbd8fc16cf41ca71da5a7e64` |
| `Examples/ListCalls.lean` | 4,333 | 124 | `d364a891af384d69683c5df1c4944856e84f2ce6e4104c6e283be552cf27a944` |
| `Examples/FunctionalNotation.lean` | 8,002 | 193 | `90a6af225009db0ab8b422318a7e7d2746f336f71b1f326c2d150dce0ec76f50` |

These are the six intended focused modules; the two `ListCalls` files are distinct core and example files.

## 3. Actual repair delta and namespace/import interaction

The complete `B` to `R` path inventory is:

| Change | Path |
|---|---|
| Add | `Applications/Resources/CallComparison.lean` |
| Add | `Applications/Resources/SharedDemand.lean` |
| Add | `Examples/CallModels.lean` |
| Add | `Examples/SharedDemand.lean` |
| Modify | `SquareApplications.lean` |
| Add | `docs/research/fdsa-call-models.md` |
| Modify | `docs/research/fdsa-reconstruction-map.md` |

In particular, this delta does **not** edit `Applications/Resources/Measured.lean`, `Applications/Resources/CallCount.lean`, or another existing Lean implementation. The earlier universe generalization of `Measured` is already in `B` and in `P`; it is not a new interface alteration made by `R`.

The complete `B` to `P` inventory consists of the six focused additions in section 2, changes to `SquareApplications.lean` and `docs/research/fdsa-reconstruction-map.md`, and addition of `docs/research/fdsa-notation-map.md`. Thus the only shared changed paths between these two deltas are the aggregate root and the reconstruction map. The map and the two standalone research notes are documented here as path-inventory inputs; this report does not claim a separate full content reconciliation of those documents.

### Complete new Chapter 1 Lean sources at `R`

| Path | Bytes | Lines | Ordinary SHA-256 |
|---|---:|---:|---|
| `Applications/Resources/CallComparison.lean` | 5,498 | 123 | `8d6d9324aa9dc71ceeaeaa04073f0f2a4f721a309995f0b623650bb19f01b520` |
| `Applications/Resources/SharedDemand.lean` | 12,012 | 251 | `c9740655b7afb51b28b044f1a72006d7a393b74a3e60e2f26464dc7eca7ee996` |
| `Examples/CallModels.lean` | 4,188 | 105 | `c1d13360a1229f21bf749d7e7db463eaf9d094089d6c2aa7c92171540e5616ac` |
| `Examples/SharedDemand.lean` | 7,844 | 188 | `5b0e374c3d57a9a681d49b9ae0b1bff41a6f60490efadc79cd2d3432b7737fc9` |

`CallComparison` adds declarations in the existing `Resources.CallCount` namespace. Its new observation is `refinedCost`; its `[simp]` equations are headed by that new definition. Its event-cost bounds, finite catalogue bound, and positive/zero entry-tariff qualifications do not replace `tick`, `tick_cost`, `primitive_rule`, `let_rule`, or `bind`. No conflicting declaration in the six prefix modules was found.

`SharedDemand` adds the separate `Resources.SharedDemand` namespace and operations for an identity-indexed cache. Equality decisions concern identities when requested, and finite-catalogue assumptions are confined to the relevant section. It does not change ordinary `Resources.bind` or add shared evaluation to an existing list operation. The two new example namespaces are `Examples.CallModels` and `Examples.SharedDemand`, distinct from the four prefix example namespaces.

The full four-file read found no new global typeclass instance or parser/syntax declaration that would change the prefix's payload domains or notation. The source-level declaration names do not collide with the six prefix modules or their generated `Examples.FunctionalNotation` additive declarations. This is a source inspection result, not an elaborated-environment collision check.

None of the six prefix import headers imports either new Chapter 1 core or either new Chapter 1 example. A literal import search over `P` also found no import of those four new modules. Conversely, the four Chapter 1 additions import pre-existing modules or each other; they do not import a Chapter 2 addition. No new dependency cycle between these two groups is indicated by the actual imports.

Importing both groups into the aggregate root does not retroactively add the other group's declarations to a separately compiled module's declared import environment. Consequently, the repair's extra refinement/sharing lemmas are not new premises or simplification rules inside these saved prefix files merely because the final root imports both groups.

## 4. Existing public interfaces remain byte-identical

For each row below, complete bytes at `B`, `R`, and `P` were equal. All seven files were also read in full at `R` for the claimed interface connections.

| Full path | Bytes | Lines | Common ordinary SHA-256 |
|---|---:|---:|---|
| `Applications/Resources/Measured.lean` | 2,906 | 71 | `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| `Applications/Resources/CallCount.lean` | 2,447 | 58 | `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |
| `Applications/Resources/ListReversal.lean` | 4,827 | 116 | `39aa38f0d3de87c0e37f222eea89880f81a1d93eeeff8e7618b07a260e2d7f0e` |
| `Applications/Resources/SymmetricCosts.lean` | 10,508 | 281 | `2e78ce2ac33ec06e9144988a6541a01bee276ba4035b16d4633b0e870daab6d5` |
| `Applications/Sorting/Sort.lean` | 5,922 | 128 | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| `Applications/Selection/Rank.lean` | 3,713 | 91 | `4a82df75593d909e2968bf1e27cbfea52c9795abfe81250bb2385e7dfc16f965` |
| `Examples/FunctionalBasics.lean` | 3,381 | 91 | `f9d141719675eaaf1a09bcfabf1a0e79cc2f68f89406a2229233b71a8d1bae3d` |

The concrete public facts relevant to this prefix remain:

- `Resources.Measured α C` is the ordinary product `α × C`, with independent value and observation universes. `bind r f` evaluates its continuation at the actual `r.1` and returns observation `r.2 + (f r.1).2`. Its general law statements do not impose commutativity on observations. The existing `erasureSquare` universe accommodation is retained.
- `Resources.CallCount.tick r = (r.1, r.2 + 1)`. `primitive_rule`, `let_rule`, argument sequencing, and branch rules retain their existing types. The Chapter 1 repair adds alternative tariff comparisons; it does not redefine the unit recursive-entry tariff used by the prefix.
- `ListReversal.appendRun_exact xs ys` still returns `(xs ++ ys, xs.length + 1)`. It includes the final empty-left-list invocation.
- `SymmetricCosts.lengthRun_exact xs` still returns `(xs.length, xs.length + 1)`. `splitRun_value k xs` returns the pair of `take` and `drop`, and `splitRun_work k xs` is `min k xs.length + 1`.
- `Applications.Sorting.insertionOn_spec` retains key-side `[LE κ]`, `[DecidableLE κ]`, `[Std.IsLinearPreorder κ]`, and `[DecidableEq κ]`, with arbitrary payload type. It yields the existing independent `StableSort` contract.
- `Applications.Selection.pairwise_ranked` still consumes pairwise order, a permutation, and an optional-index hit to establish occurrence rank. Duplicated occurrences remain meaningful.
- `Examples.FunctionalBasics` retains its ordinary standard-library examples and names; no new notation or type assumptions have been introduced into it by `R`.

`SymmetricCosts` imports the existing `Potential` layer, but this exact repair does not modify that layer. The later XP01 concern recorded in the shared preflight is not an incompatibility of the initial `P` prefix.

### Build-input identity boundary

The following actual repository files also have equal bytes at all three revisions. They were identified by root-tree enumeration and compared in full; no inference about installed artifacts or successful compilation follows from this table.

| Path | Bytes | Lines | Common ordinary SHA-256 |
|---|---:|---:|---|
| `lean-toolchain` | 25 | 1 | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | 444 | 13 | `76966dfb4ea744d75d4bbe20ed3a6c576a17145d23f36ba44c4422673c51b04f` |
| `lake-manifest.json` | 3,138 | 96 | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |
| `flake.nix` | 637 | 28 | `0dc6835949ecc2a9e28e9fff16aeb4fa46eca74d1a92132d9a3a236974409f37` |
| `flake.lock` | 564 | 27 | `8489579a33350261a210f64e54d9442fece9c04fedf7ce8e6c5543010471238f` |

## 5. Per-module compatibility findings

### 5.1 `Applications/Resources/InsertionSort.lean`

Its imports are `Applications.Resources.CallCount`, `Applications.Sorting.Sort`, and `Mathlib.Tactic.Linarith`. Its `Resources.InsertionSort` namespace introduces the prefix's own `insertRun` and `sortRun` without replacing the existing sorting API.

The relevant dependency is actual measured sequencing: the nonempty sort calls `CallCount.tick (bind (sortRun r xs) (insertRun r x))`. Thus insertion consumes the sorted tail returned by the first computation. The value bridge to `List.insertionSort`, the recurrence using that actual result, and the length argument used in the bounds retain the same `bind` and `tick` meanings under `R`.

The insertion and sort base counts remain one. The lower bound `2 * xs.length + 1`, triangular upper bound, best/worst cases, and stable-key contract do not acquire the repair's `refinedCost`, cache, finite-catalogue, or positivity hypotheses. The source does not request an order, equality instance, or inhabitant for an unrelated payload merely to sort by a key.

Finding: no repair-induced signature or import mismatch. This does not independently validate the prefix's induction, arithmetic, or automation proofs.

### 5.2 `Examples/InsertionCosts.lean`

Its imports are the preceding prefix core and `Applications.Selection.Rank`. The examples connect actual `sortRun` values and costs to the core bounds and the old occurrence-rank API. Empty, singleton, repeated-key, already ordered, descending, and early-tie observations remain observations of the same declared execution.

In particular, the generic key contract separates a `Nat` key from arbitrary payload data, and the rank connection uses the measured output together with permutation and sortedness. Neither connection needs the new refinement/sharing modules. The early head tie can terminate insertion despite an unsorted remaining tail; no repair theorem silently adds an input-sortedness condition to that exact run.

Finding: unchanged rank and stable-sort interfaces support the written statements at source level. The concrete saved counts are not being replaced by refined-event or shared-demand costs.

### 5.3 `Examples/ListLibrary.lean`

Its imports are `Mathlib.Data.List.Intervals`, `Mathlib.Data.List.MinMax`, `Mathlib.Data.List.Chain`, and `Mathlib.Data.List.Sort`. It has no resource-layer import. Its list observations use the standard library and retain their explicit distinction between total optional observations and proof-domain operations.

The saved minimum statements keep their stated local algebraic assumptions, and the nontransitive adjacency example does not assert a false general pairwise conclusion. The repair changes neither these Mathlib pins nor the module's imports. Its set-style observations do not introduce payload equality by way of the new cache machinery.

Finding: no source dependency on a changed Chapter 1 API; no new order/default assumption enters the Empty cases described in section 6.

### 5.4 `Applications/Resources/ListCalls.lean`

Its imports are `Applications.Resources.CallCount`, `Applications.Resources.SymmetricCosts`, and `Mathlib.Algebra.BigOperators.Group.List.Basic`. It uses distinct payload universes for mapping and the unchanged measured pair operations.

`mapRun` charges each supplied callback observation and each list invocation; `filterRun` also charges callbacks for discarded elements. Both retain cost `sum (callback observations) + xs.length + 1`. The source's constant-callback bounds remain input-local. `takeRun` and `dropRun` project the actual existing split execution; their count stays `min k xs.length + 1`. Separately sequencing both operations retains two such charges and is distinct from consuming one split result.

`lookupRun` returns an `Option`, has one entry at an empty list or a root hit, and charges the traversed suffix recursively. Its total extension has count `min k xs.length + 1`; the valid-index statement explicitly assumes `k < xs.length` and returns `some xs[k]` with count `k + 1`. The repair does not replace invalid queries with a default payload.

Finding: every direct resource interface consumed here is byte-identical. New identity-based sharing is not automatically inserted into callback occurrences, list traversal, or the separate take/drop sequence.

### 5.5 `Examples/ListCalls.lean`

Its imports are the preceding prefix core and `Applications.Resources.ListReversal`. The actual-result connections remain substantive: `map_then_length` applies length to the returned mapped list, and `append_then_length` applies length to the returned concatenation. The latter count remains `2 * xs.length + ys.length + 2`, by the existing append and length equations.

The callback example on `[2, 2, 3]` continues to charge all three occurrences; filtering away occurrences does not erase their evaluation costs. The saved map/filter count 11 and map-followed-by-length count 15 therefore refer to the ordinary model. The separate-versus-fused split example keeps counts 6 and 3, respectively. None should be rewritten using the new shared-demand examples, where equality of an explicit cache identity is the sharing criterion.

The generic map/length theorem retains independent source and target universes. Empty optional lookup and Empty take/drop statements retain their exact total values and one-entry counts.

Finding: the saved composition and boundary cases consume unchanged public laws. No source-level repair is indicated.

### 5.6 `Examples/FunctionalNotation.lean`

Its imports are `Examples.FunctionalBasics`, `Examples.ListLibrary`, `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Order.Archimedean.Real.Basic`, `Mathlib.Algebra.Order.Floor.Ring`, `Mathlib.Data.Int.DivMod`, `Mathlib.Data.Set.Lattice`, `Mathlib.Data.Set.Prod`, `Mathlib.Data.Set.Finite.Basic`, `Mathlib.Order.Interval.Finset.Nat`, and `Mathlib.Order.Interval.Set.Defs`.

The module uses standard notation and introduces no parser framework. It retains its type-specific natural/real/integer boundaries, finite versus infinite set-index convention, and separate list/multiset observations. `finiteIndexProduct` and the additive declarations generated by `to_additive` live in `Examples.FunctionalNotation`; no new Chapter 1 declaration occupies those names.

The final `P` correction is the explicit `empty_index_type` theorem, not a replacement of the indexing domain with an inhabited one. The changed Chapter 1 sources do not alter `FunctionalBasics`, the used arithmetic/library inputs, or the notation module's local finite-set definitions.

Finding: no repair-induced import, declaration-name, or domain mismatch. The final Empty-index addition must survive the later content integration unchanged.

## 6. Empty and universe boundaries that must be preserved

| Saved declaration or domain | Exact boundary retained | Compatibility reason |
|---|---|---|
| `Examples.ListLibrary.empty_payload_queries` | For `List Empty`, `head?` and optional index return `none`; `tail` and `dropLast` return `[]`. | No inhabitant or default payload is required. |
| `Examples.ListLibrary.empty_payload_minimum` | `List.min?` on `[] : List Empty` is `none`, using the explicitly empty-domain `Min` operation. | The example does not obtain an impossible `Empty` value or require an inhabited order. |
| `Examples.ListCalls.empty_payload_lookup` | `lookupRun ([] : List Empty) 20 = (none, 1)`. | The optional total extension and empty recursive-entry count remain unchanged. |
| `Examples.ListCalls.empty_payload_split` | For every `k`, take and drop on `[] : List Empty` both return `([], 1)`. | Existing `splitRun` is payload-polymorphic and its empty case needs no payload value. |
| `Examples.FunctionalNotation.empty_index_type` | The empty `Set Empty` indexed sum is 0 and product is 1, with `Empty.elim : Empty → Nat`. | Finiteness is attached to the empty set; no inhabitant of the index type is introduced. |
| `Examples.ListCalls.map_then_length` | Source and target payloads may inhabit independent universes. | The retained `Measured`/`bind` signatures support this already at `B`. |
| Insertion's generic key contract | Payload has no assumed order or equality; the key supplies the comparison structure. | The unchanged `insertionOn_spec` keeps its typeclass assumptions on keys. |

An insertion operation with an explicit `x : α` of course needs that actual input value. This is not an `Inhabited α` constraint and does not invalidate the empty-list sort boundary for an uninhabited payload type. No new artificial Empty insertion witness is proposed here.

The new Chapter 1 examples themselves also keep empty-domain observations: refined append accepts `List Empty`, and the empty shared-demand catalogue uses `Empty` without manufacturing a result. Those additional examples do not impose their catalogue structure on the six prefix modules.

## 7. Aggregate import boundary

The complete root diffs add these exact imports at the same pre-existing tail of `SquareApplications.lean`:

| From `R` | From `P` |
|---|---|
| `Examples.CallModels` | `Examples.InsertionCosts` |
| `Examples.SharedDemand` | `Examples.ListLibrary` |
| | `Examples.ListCalls` |
| | `Examples.FunctionalNotation` |

A combined root must retain all six, together with the pre-existing imports. The core prefix modules enter through their examples' actual imports; no additional new public wrapper is needed to explain their reachability. Choosing one branch's whole root would omit the other branch's public examples even though the individual modules' APIs are compatible.

This is a concrete content-integration concern, not evidence that the source contracts conflict. The exact reconciliation recipe and reconstruction-map splice belong to the separately assigned architecture report. No aggregate root or documentation map was written by this author.

## 8. Limits and handoff

The result supports carrying the exact saved prefix forward for the already planned integration after Chapter 1 acceptance. It supplies no reason to change one of the six sources merely to accommodate this exact repair. It also does not authorize that integration, alter its six-module focused scope, or waive any combined focused/full validation, audit, mathematical assessment, or acceptance step already recorded by the root workflow.

Byte equality of dependencies rules out a changed source signature in those files. It does not establish that a previously saved proof elaborates, that the eventual merged source is identical to the saved inputs, or that imports and declarations coexist in a compiled aggregate environment. No such claim is made. Historical focused successes mentioned in the input preflight remain historical evidence, not success of this combined candidate.

If the accepted Chapter 1 source differs from exact `R`, or if the chosen prefix differs from exact `P`, the present compatibility conclusion does not automatically cover that change. The root should use the actual successor diff to decide what bounded follow-up is required; this report starts no additional review loop.

Only `fdsa-control/reviews/chapter02-prefix-source-compatibility.md` was written for this task. The file was then read back in full, and writes stopped. Its final byte/line count and ordinary SHA-256 are supplied in the separate author handoff so that this document need not contain a self-referential digest. No Lean source, index, ref, worktree, cache, compiler/checker state, local ticket scope, or prefix was altered.
