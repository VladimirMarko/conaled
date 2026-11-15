# Stage07: actual endpoint-step interface

## Immutable candidate and requested focus

- Candidate: `7950275f345d1077e23730e1975b6dac7460be87`.
- Tree: `fcdb36aa2fc1fa19efbb5fdf950de47f1ce350e3`.
- Parent: `d82ee6286de99a032eaf5fd925e6b87f48e0fb36`.
- Branch: `work/fdsa-ch03-random-selection`; clean.
- Commit: `feat(selection): formalize actual endpoint steps (#174)`; actual exit0, tool `04df4c`, command-local ChatGPT identity.
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Two new files add 258 lines, 15 core public declarations and 12 example public declarations. There are no new private helpers. Cumulative source scope is **14 files, 266 public names and17 authored private helpers**. All12 prior files are byte-identical, preserving all256 prior headers, contexts, definition bodies and proofs. The old23 authored definitions remain exact; the only new definition is the logical `EndpointPivot` predicate, so the cumulative authored definition count is24. There is no new selector, sampler, assigned work function or source-cost function.

This pair is **uncompiled**. Root's sole serial focused targets are:

```text
Applications.Resources.RandomSelectionEndpoints
Examples.RandomSelectionEndpoints
```

## Prior actual success and unchanged evidence

The all-equal pair passed at parent `d82ee628`: owned1656 CLOSED exit0, terminal `a5a63b`, root full closure `c1d4bb`. Examples Built in67s; the core was cached from its earlier successful build. Complete outer log, closure, terminal and result read: `3f52b4`.

- Outer10,349bytes; SHA-256 `d032586fe3045770de87eace64add91b461954210c93bd7b3cbfe80ea69b9962`.
- Native10,065bytes; SHA-256 `00f096de63ddfda7c6659122afd11a963f51f840f7da935e88aabecb517794c0`.
- Native body matches the outer body at byte127.

All214 earlier own records and all14 actual equal-pass records are hash-preserved. The prior hold's258 bound files were reverified, including both earlier equal failures. Earlier mean/drift/tail failures, the single interruption without terminal credit, and all previous successful evidence remain intact. The inherited full verification record belongs to accepted `c1cefe4`, not this new candidate.

## Mathematical claims and full quantifiers

`EndpointPivot k xs i` names an **actual current occurrence**. It says that the looked-up value is a maximum when `k=0`, and a minimum when `k>0`. This predicate is meaningful for duplicates, but the one-element removal theorem explicitly requires `xs.Nodup`.

The partition lemmas use the existing `partition3` specification. A distinct member has equal bucket exactly `[p]`; the opposite strict bucket is empty at a minimum or maximum. Both actual strict partitions inherit Nodup. Partition length conservation then proves that the selected endpoint child has exactly one fewer element.

Minimum/maximum occurrence existence uses the pinned nonempty `List.min`/`List.max` API and indexed membership, so it works on arbitrary unsorted inputs without an inhabited payload, finite carrier or distinctness premise. Under Nodup, two endpoint occurrence witnesses are equal, using the injectivity of indexed lookup.

The measured-step theorems derive directly from `stepRun_eq`:

- A minimum occurrence at positive rank selects the actual right child at rank `k-1`, with local source cost `2*n+i+7`. This statement also covers invalid positive worker ranks; validity is only added where needed.
- A maximum occurrence at rank0 and size greater than1 selects the actual left child at rank0, with local source cost `3*n+i+4`. Its equal-length traversal is not charged because that source branch is not reached.

`exists_endpoint_child` covers **every arbitrary Nodup list and every valid worker rank**, when size exceeds1. It produces an actual endpoint occurrence and child with the actual `stepRun` branch equation, Nodup, exact one-element decrease, valid predecessor rank, and equality of the child's and parent's sorted-index specifications. The rank is always its natural predecessor, which stays zero after zero. There is no sorted-list or endpoint-target-rank restriction.

These are local prerequisites of C03-064. They do not claim a whole-path probability, triangular attainment or an unbounded family. Those remain explicit next-stage obligations. The full frozen83-row scope is preserved.

## Cases calculated before source

The independent expected model was saved and executed before source creation (`febedc`). It recursively counts actual length, lookup and stable-partition calls, executes the same source branch tests and enumerates every current occurrence with exact rational mass. It checked all719 distinct permutation/rank cases of sizes1 through5, then stored13 illustrative whole paths and7 local steps. This is expected-case arithmetic, not universal Lean proof or validation credit. Complete model read: `c27771`; complete illustrative outcomes: `fd745c`.

The12 example declarations cover:

| Case | Fixed expected behavior |
|---|---|
| Unsorted minimum | `[3,1,2]`, rank1,index1 -> `(0,[3,2])`, cost14. |
| Unsorted maximum | `[3,1,2]`, rank0,index0 -> `(0,[1,2])`, cost13. |
| Interior-rank switch | Rank1 on `[3,1,2]` chooses a minimum; rank0 on `[3,2]` then chooses a maximum, actual child `[2]`, cost10. |
| Negative minimum | `[3,-2,8,0,5]`, rank3,index1 -> `(2,[3,8,0,5])`, cost18. |
| Negative maximum | Same input, rank0,index2 -> `(0,[3,-2,0,5])`, cost21. |
| Generic singleton | Rank0 returns the singleton value directly at source cost9. |
| Duplicate countercase | `[4,4,4]` is not Nodup; rank1,index0 returns4 immediately at active cost15. |
| Invalid singleton | `[7]`, rank1,index0 enters the empty child at active cost9; the existing empty continuation adds2. |
| Empty boundary | No natural worker rank is valid on the empty list. |
| Generic occurrence | Every nonempty input has a current endpoint occurrence, including duplicates. |
| Generic valid target | Arbitrary distinct valid nonsingleton input has the exact child and target-specification preservation. |
| Unique occurrence | Distinctness identifies the endpoint index itself. |

The new empty-list arithmetic example deliberately uses `omit [LinearOrder α] in`: its statement does not need a payload order. This is disclosed in every new declaration inventory; no old implicit context changes. All other new source contexts, headers and quantifier groups are recorded.

## Exact source, assessment and explicit-@ input

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| Endpoint core | 8619 | `952fe60e22d84332a502b5bf30c485c618d13b6e36f0c2e783551bb3c53b807d` |
| Endpoint examples | 2944 | `a8daeae4626353eb82b613d081a88737a26b556942cdd456ecc73a0af3f45c1a` |
| Exact two-file patch |12422|`df60fef361c387dc37e50780a40de1fd9b217463a21e77e26492cb1dae9354a1`|
| `Statements266-stage07.lean` |15352|`61aec968e952e701066db6b5802fe87b2356a3c52bba4f533f0a4b865bc7bc33`|
| Independent finite model |5599|`7edb978daacc882721553f8a5f0a2b094f36b8571988e405e28703be5fdaa2c7`|
| Independent expected cases |16751|`69f3d90737a56bff4719f8c4c208b1f65ea585c8d9e94d72216ac4f9b77506fe`|

Core Git blob: `c8c991c4846de7424235d039b5dda56176266b30`; examples blob: `da1f616656f8f99be43f967fb79308842b3b1d83`. The prepared explicit-@ input retains all239 previous names in order, appends all27 new public names, imports the new examples, and retains every prior printing option. The preparation binds this exact candidate/tree and all14 source blobs. It is input only, not actual type output.

The full two new sources were read in `2abd44`. Exhaustive assessment `948d94` covers all27 new headers, the single logical definition, every claim/case group and the whole283-header cumulative source inventory. The two no-index diff captures returned the expected status1 for new files; these are not validation failures. The staged patch exactly matches the retained diff; its whitespace check and the actual local commit exited0.

## Required next stage and hold

The next source stage must describe the specified endpoint sequence as a property of the **existing actual trace and step states**. It must prove exact full-outcome mass through the real `run_cons` bind. The recorded first index distinguishes branches; `prepend` is injective, so isolating one outer occurrence and its actual child gives parent mass `(1/n)*child_mass`. No independence assumption about successive sizes is needed. The source-verified read-only helper route is author support only and remains uncompiled. In ENNReal, use the finite-cast side conditions of `ENNReal.mul_inv`; generic unrestricted inverse-product reasoning is invalid at0/infinity.

The universal induction must retain all arbitrary Nodup inputs and every valid rank, construct a trace satisfying the endpoint policy, and prove both mass `1/n!` and `2*W=n*(n+1)`. Derive support from nonzero finite factorial inverse, then reuse actual `run_value`/`run_valid` and `run_source_bridge`. An unbounded Nat range family must instantiate the universal theorem, with actual quadratic source lower and upper bounds. Singleton base and empty/invalid boundary restrictions must stay explicit.

No author Lean/Lake, environment/cache/output/dependency/profile action, canonical control edit or external mutation occurred. No new focused/type/full-check/audit/independent-review/immediate-verification/Chapter3 acceptance credit is claimed. The original inaccessible Karp source remains disclosed; no quotation or source recovery is invented.

All14 source files and own provenance writes are now HELD pending root's actual focused terminal or explicit release.
