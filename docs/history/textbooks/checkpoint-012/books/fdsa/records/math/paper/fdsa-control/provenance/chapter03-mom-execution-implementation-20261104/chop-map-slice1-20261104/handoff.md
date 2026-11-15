# Measured chop/map candidate — source handoff

Candidate `557d00df979d95788f093e55551abd02f17dd049`, tree `2c002d179b0a7ce7623e8bedf3eb560dbd741a1a`, parent `759589ec63d359231330f732b42c96591a53325e` on `work/fdsa-ch03-mom-execution`.
The command-local ChatGPT commit `feat(resources): measure chunking and median maps (#174)` closed with actual exit 0 (`aa6f60`). The worktree is clean. This candidate has not been compiled.

## Exact scope and targets

The four additive files are `Applications/Resources/Chunks.lean`, `Applications/Resources/SelectionMedians.lean`, `Examples/ChunkCalls.lean`, and `Examples/SelectionMedians.lean`. Root focused targets are:

- `Applications.Resources.Chunks`
- `Applications.Resources.SelectionMedians`
- `Examples.ChunkCalls`
- `Examples.SelectionMedians`

All eight inherited source files remain byte-identical to the post-incorporation baseline. That baseline contains exact authorized pivot corrections ac8 then bc269 as local27c0beb then759589, with passing auxiliary4604 preserved. No other branch, source, tooling, dependency, runtime or canonical control was changed. All26 protected earlier provenance records and the held0125 preparation/reconciliation remain exact. Root's two SelectionRecurrence paths are reserved and absent from this slice.

## Actual execution and intended claims

`Resources.Chunks.chopRun` evaluates separate measured take and drop calls at every positive, nonempty recursion. The returned drop drives a length-decreasing recursive call, independently of cost or value assumptions. The value is proved equal to the existing `chop` adapter. The exact positive-size count is `2*n + 3*ceil(n/d) + 1`; size zero and empty calls each cost1. The uniform bound is `5*n+1`, with equality for d=1. Actual chunks retain every occurrence, are nonempty, have size at most d and number exactly the natural ceiling.

`Resources.SelectionMedians.slowMedianValueRun` extracts a payload from the actual successful optional slow-median run, retaining its actual count. Nonemptiness rules out none; no inhabitant, fallback, Option cleanup pass or separately evaluated specification payload is used. Occurrence-rank uniqueness then establishes the existing lowerMedianValue correspondence. A nonempty chunk of at most5 costs at most47.

`mapSlowMedianRun` uses the existing actual measured map over proof-carrying reached chunks. Its count is the sum of actual callback counts plus m+1; generic bound `(d^2+4*d+3)*m+1` is retained for the generalized-group exercise. At five, the bounds are48*m+1 and10*n+48. attach and proof extraction are explicitly source-model adapters; no Lean allocation/runtime bound is asserted.

`chunkMediansRun` executes chopping once, then the actual map on its returned chunks. It preserves the prior mathematical `chunkMedians` value and charges exactly the two actual component observations. For positive d the closed expression is `2*n + 4*ceil(n/d) + sum(actual slowMedianRun costs) + 2`. The generic bound retains d; the book's actual preparation bound is15*n+49.

## Connected cases and mathematical assessment

All68 public declarations received source-level statement assessments in `source-inventory-and-statement-review.json`:4 definitions and64 theorems, with no private named declarations, anonymous instances or anonymous examples. Complete source reads are0da72f (both resource files, then final Chunks read7fbae0), afbe2e (both examples); complete assessment read437749 and all explicit prepared names read5616c4. Actual elaborated types remain unobserved.

The independent finite targets prepared before source creation include zero-size, singleton groups, short-final and oversized groups, full five-groups, duplicates, and size21. Concrete formal cases also reuse the already checked auxiliary/pivot examples through public correspondence APIs:

| Input | Group size | Chop count | Median map count | Combined count |
|---|---:|---:|---:|---:|
| empty input |5|1|1|2|
| [7,2,4] |0|1|1|2|
| [7,2,4] |1|16|22|38|
| [7,2,4] |2|13|19|32|
| [7,2,4] |10|10|17|27|
| range10 |5|27|43|70|
| range7 |5|21|32|53|
| six fours |5|19|29|48|
| range21 |5|58|92|150|

Not every reference-table component is a separate new theorem; the source inventory identifies the exact formal cases. The map of [[7,2],[4,4]] is explicitly [2,4] with cost22. Empty Fin0 examples exhibit absence of an inhabitant requirement. Replacing only the first take/drop pair by a single split gives10 instead of the actual13; this is explicitly not a claim about a fully fused alternative. Generic examples expose membership, size caps, rank, preservation, group-parameter bounds and the five-group budgets. Arbitrary duplicates remain allowed throughout.

## Validation boundary and next work

The only new executed validations are exact source/record identities, explicit inventory consistency, source and case assessment, staged/unstaged whitespace checks, the exact four-path commit and clean-state checks. `precommit-validation.json` preserves actual successful staging/check outputs; no Lean or Lake command was run by this author. The prepared `ChopMapStatements68-candidate1.lean` contains an exhaustive explicit-@ name list under the existing detailed-print profile and is unexecuted.

The parent is sole compiler owner. Focused compilation is required for this immutable candidate, followed later by applicable full candidate/audit gates, actual type assessment, complete independent Standards and Spec reviews and immediate verification before any acceptance. This slice does not claim C3 or book completion, full validation, acceptance or a run<=F theorem.

After the focused terminal and release, continue actual nested selection with one recursive median call and at most one strict-side call, a noncircular membership/valid-rank termination certificate, optional invalid/empty behavior, branch-sensitive exact source charges and the actual execution bound by root's checked scalar F. Root's draft F interface was supplied, but its commits have not been incorporated or imported. No cost, value or termination law may be assumed as the desired conclusion.

Source and own provenance are HELD after the separate author-hold record pending root's exact candidate check and next assignment.
