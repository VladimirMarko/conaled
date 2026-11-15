# Import footprint prerequisite — independent Standards review, round 3

Date: 2026-11-02. Reviewer: `/root/prerequisite_review/standards`.
Validation status inspected at 22:16:04 UTC.

## Outcome and exact scope

**Standards: Blocked; complete fixed-base static assessment finished.** There
are **0 new or unresolved Standards code/prose findings**, no worst code/prose
severity and no heuristic-only request. IMPORT-VAL-004 remains a pending
validation finding. Its proposed direct-provider repair is statically
supported but has no terminal compiler result. The required exact full
candidate check, matching verification record and final verify are also
missing. This report does not approve the candidate.

- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Candidate: `901f734161920a76f3b399a575805b9a1d31e971`.
- Narrow diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...901f734161920a76f3b399a575805b9a1d31e971`.
- Frozen checkout: `/workspace/scratch/ca9a61d0bf30/import-correction-r3`.
  Exact candidate HEAD and empty porcelain status were independently observed.
- Narrow scope: six files, three commits, 16 additions and 2 deletions; no
  exclusions. The commits are `226ebae`, `324962e` and `901f734`.
- Linked #10013 round 5 uses unchanged fixed base/merge base
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`, with the complete fourteen-file,
  five-commit candidate, 955 additions and 2 deletions.

The complete independent Standards assessment, full SharedList statement and
connected-case review, architectural findings, input identities and validation
history are preserved in
[shared-persistence-standards-r5.md](shared-persistence-standards-r5.md).
This ticket-specific record is part of that same axis, not another review
loop. The prior `324962e` report remains explicitly PARTIAL / Blocked, and the
earlier static reviews remain Blocked rather than being promoted to approval.

The saved original request, union clarification, SharedList requirements v2
and import-footprint requirements v1 are unchanged. Applicable candidate
AGENTS, code-review/review-loop, statement-review, architectural/domain/glossary
and ADR rules, README validation and heuristic guidance are unchanged and
were applied to the complete scope. The frozen prerequisite accepts no book
or thesis chapter and excludes the separate main/Chapter 2/foundation/pure
and Chapter 3 research work named in the dispatch.

## Independent preservation and provider assessment

I independently matched all fourteen manifest hashes to committed candidate
files, confirmed both fixed merge bases, and compared each of the six import
consumers directly against fixed base `70a1477`. Removing only `import ` lines
leaves identical bytes, including line terminators, in every file. The
matching non-import SHA-256 values are recorded in the linked full report.
All declaration statements, definitions, proof bodies, local options,
comments and cases are preserved; this is not a claim that elaborated
environments or compiled kernel artifacts are identical.

| Changed consumer | Provider and affected-use assessment |
| --- | --- |
| `Applications/FRP/Spec.lean` | The direct real, Finset sorting and finite-set evidence modules correspond to its actual definitions and proofs. Existing local category/map imports remain. The complete frozen-file analysis from the earlier round remains applicable. |
| `Applications/FRP/Equivalence.lean` | The real, Finset maximum/cardinality, finite-range, lexicographic-order, natural-interval and specific arithmetic-tactic providers correspond to its enumeration/order proofs and counterexamples. No all-library replacement is introduced. |
| `Applications/FRP/Demand.lean` | Actual pinned `Mathlib.Order.SuccPred.Nat` supplies `Nat.instSuccAddOrder` and imports the API containing `[simp] Order.lt_add_one_iff`. This supports the unchanged strict-successor proof after `simp_all [next]`; it does not weaken the earlier-registration conclusion. |
| `Applications/FRP/Finite.lean` | Actual pinned `Mathlib.Data.Set.Finite.Lattice` declares `Set.Finite.biUnion`, precisely the finite union result used by `finiteHistory`. |
| `Examples/FRP.lean` | Actual pinned `Mathlib.Algebra.Order.Archimedean.Real.Basic` provides the real Archimedean instance and imported `exists_nat_gt` API used by the unchanged ticks finite-history proof. |
| `Examples/IndefiniteService.lean` | Actual pinned `Mathlib.Data.Nat.Size` declares `Nat.size_pow : size (2 ^ n) = n + 1`, which directly supplies the missing rewrite in the unchanged contradiction of a uniform natural bit-size bound. |

The last file's only change from `324962e` is the single natural-size import.
I read its complete existing client code and inspected the provider at line
94. The provider file hash is
`ab4306e1e29d9b254dd41af7e206591130414598403577921c7877e9919c249b`;
the clean pinned Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The affected consumer assessment covers Frontier, Finite, Engine, Temporal,
Examples.FRPDemand, Examples.FRP, Examples.IndefiniteService and their ordinary
SquareApplications integration. Existing distinctions among finite
predecessors/history, simultaneous-event order, strict switching, demand
provenance, truthful frontier evidence and fairness remain intact. The
indefinite-service stream, compiled-delay, composition, productivity and
representation examples retain their premises and expected results. No
connected case has been deleted or weakened.

There is no toolchain/dependency pin, check script, cache guard, source policy,
audit root, axiom allowlist or public entrypoint change in the narrow diff.
Complete downstream elaboration and the exhaustive audit remain mandatory.
The source/provider comparison files supplied by the implementation worker
are supporting evidence; the assertions above were checked independently.
No performance improvement is claimed from unmatched development runs.

## Stable findings

| Finding | Independent disposition on `901f734` |
| --- | --- |
| **PERSIST-VAL-001** | **Retained fixed with prior compiler evidence.** The same redundant success-branch tactic removal remains in the full candidate, with the unchanged 664-job focused SharedList success. It does not approve the current full candidate. |
| **IMPORT-VAL-001** | **Fixed with focused compiler evidence; full gate pending.** The direct successor-order provider is present, its instance/simp mechanism was independently read, and the unchanged Demand source matches the successful focused evidence. The original compiler failure remains recorded. |
| **IMPORT-VAL-002** | **Fixed with focused compiler evidence; full gate pending.** The actual finite-union provider and unchanged Finite source match the focused compilation. The original `biUnion` failure is preserved. |
| **IMPORT-VAL-003** | **Fixed with focused compiler evidence; full gate pending.** The real Archimedean provider and unchanged example match the successful second focused run. The first run's `exists_nat_gt` failure remains preserved. |
| **IMPORT-VAL-004** | **Proposed repair statically supported; terminal compiler verification pending.** The exact previous full-check failure, unknown `Nat.size_pow` at line 104 with an unsolved False goal at line 101, remains in `../validation/import-footprint-324962e-observed-errors.json`. The direct theorem provider is correct for that unchanged proof, but the current focused run is unfinished. |

The second r2 focused record
`../validation/import-footprint-r2-focused-r2.json` has exit code 0,
`inputs_unchanged: true` and equal before/at-start/after maps. I independently
matched all **23 recorded source/config hashes** to committed `901f734` blobs.
Although that development run names then-current HEAD `226ebae`, its exact
recorded corrected source inputs match this candidate. Its pinned offline Nix
command builds Examples.FRPDemand and Examples.FRP with one Lean thread; the
log ends successfully with **1134 jobs**. The first run compiled Demand,
Examples.FRPDemand and Finite before exposing IMPORT-VAL-003; the second uses
normal Lake outputs for those modules and compiles the repaired FRP example.
The first failure is not relabeled success.

This supports the three particular repairs without treating development
evidence as full-candidate approval. The earlier ordinary cache-copy record
for `324962e` states no source inconsistency and explicitly
`approval_copied: false`, `acceptance: false`. Its copied outputs do not confer
approval, and normal guards/invalidation plus the complete stock check remain
required on the successor.

No new Standards code/prose finding ID is allocated. One stable validation
finding, IMPORT-VAL-004, is still pending compiler verification, separate from
the missing full acceptance gate.

## Validation and continuation

At 22:16:04 UTC, the active focused record
`../../active-validation/import-footprint-r3-focused-r1.json` identifies exact
`901f734`, its private build directory, the pinned offline Nix environment and
target `Examples.IndefiniteService`. Before and at-start maps contain the same
60 source/config/provider hashes, all independently matched to the frozen
inputs. There is no terminal end/exit code, final after snapshot or final
unchanged-input result; the log continues dependency compilation. Source
confidence alone does not close IMPORT-VAL-004.

Full `901f734` validation has not started according to the current dispatch.
The live known-failing full `324962e` run cannot approve this new candidate.
`import-correction-r3/.lake/verification.json` was absent at inspection, and
no final verify evidence was supplied. Required completion is exact full
terminal success under the unchanged `./check.sh --candidate HEAD`, covering
all 957 integrated modules and exhaustive proof audit, a matching verification
record, and immediate final `./check.sh --verify-candidate HEAD`. Terminal
focused evidence, or matching exact full-build coverage, must also resolve
the remaining validation finding. Both independent axes must pass the same
candidate; this report supplies only Standards.

On unchanged `901f734`, the complete static assessment can be retained while
new terminal evidence is independently assessed. A changed candidate requires
renewed complete fixed-base review and stable finding history. I performed no
compilation and modified no frozen source, dependency or build output. Only
the two assigned round reports were written after checkpoint021 release.

## Result

| Scope | Fixed base | Candidate | Count / worst severity | Standards outcome |
| --- | --- | --- | --- | --- |
| #10018 round 3 | `70a1477d822efd4fdcec2007280f650bb4695eda` | `901f734161920a76f3b399a575805b9a1d31e971` | 0 Standards code/prose findings; no worst code/prose severity. One pending validation finding, plus missing full gate. | **Blocked; static assessment complete** |
| Linked #10013 round 5 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` | `901f734161920a76f3b399a575805b9a1d31e971` | Same Standards findings count and validation limitations across the complete fourteen-file scope. | **Blocked; static assessment complete** |
