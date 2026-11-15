# Import footprint prerequisite — independent Spec review, round 3

Date: 2026-11-02. Reviewer: `/root/prerequisite_review/spec`.
Validation status inspected at **22:20:51 UTC**.

## Outcome and scope

**Spec: Blocked; full fixed-base static assessment complete.** There are
**0 new or unresolved Spec implementation findings**, no worst implementation
severity, and one existing validation finding still open: **IMPORT-VAL-004**.
Its direct-provider repair is statically supported but lacks terminal compiler
evidence. The exact full-candidate build/audit, matching verification record
and final verification also remain unavailable.

- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Candidate: `901f734161920a76f3b399a575805b9a1d31e971`.
- Narrow diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...901f734161920a76f3b399a575805b9a1d31e971`.
- Narrow scope: six files, three commits (`226ebae`, `324962e`, `901f734`),
  16 insertions and 2 deletions; no exclusions.
- Frozen checkout: `/workspace/scratch/ca9a61d0bf30/import-correction-r3`.
  Exact candidate HEAD and empty porcelain status were independently observed.
- Linked #10013 round 5 retains base/merge base
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`, with the whole fourteen-file,
  five-commit scope, 955 insertions and 2 deletions.

The complete independent assessment, full SharedList statement review,
all six exact preservation hashes, provider mechanisms, focused-input matching,
stable findings and continuation are in
[`shared-persistence-spec-r5.md`](shared-persistence-spec-r5.md). This is one
Spec axis with linked scopes, not a second review loop.

My previous completed static Spec assessment was `226ebae`; it remained
Blocked. **Spec did not review `324962e`**, and the corresponding Standards
assessment remains explicitly **PARTIAL / Blocked**. No absent axis result or
old approval is invented for the successor. Original request, book/thesis union
clarification, SharedList v2 and import-footprint v1 are unchanged; I matched
all four requirement hashes independently. This prerequisite accepts no
chapter or concurrent main/Chapter 2/foundation/pure/Chapter 3 work.

## Independent preservation and provider assessment

All fourteen manifest source hashes match both committed and working candidate
bytes. For every changed import consumer, direct comparison against fixed base
`70a1477` leaves identical bytes after removing only import-command lines. All
definitions, statements, proofs, examples, options and comments are retained.
No other path changes in #10018; the latest delta from `324962e` is one import
in `Examples/IndefiniteService.lean`.

| Consumer | Independently assessed import purpose |
| --- | --- |
| `Applications/FRP/Spec.lean` | Direct real-number, Finset sorting and finite-set evidence providers replace the aggregate while local category/map imports remain. Its complete prior source assessment remains applicable. |
| `Applications/FRP/Equivalence.lean` | Direct finite-predecessor enumeration, maxima/cardinality, finite-range, lexicographic order, natural intervals and arithmetic tactics retain the unchanged event-equivalence development and counterexamples. |
| `Applications/FRP/Demand.lean` | `Mathlib.Order.SuccPred.Nat` supplies `Nat.instSuccAddOrder` and publicly imports `[simp] Order.lt_add_one_iff`, restoring the simplification used by the unchanged strict earlier-registration proof. |
| `Applications/FRP/Finite.lean` | `Mathlib.Data.Set.Finite.Lattice` supplies the actual `Set.Finite.biUnion` theorem for the existing finite union of finite occurrence-index sets. |
| `Examples/FRP.lean` | `Mathlib.Algebra.Order.Archimedean.Real.Basic` supplies the real Archimedean instance and general `exists_nat_gt` API used by the unchanged ticks finite-history argument. |
| `Examples/IndefiniteService.lean` | `Mathlib.Data.Nat.Size` supplies `Nat.size_pow : size (2 ^ n) = n + 1`, precisely the missing rewrite in the unchanged contradiction of a uniform natural representation-size bound. |

The actual pinned providers and consumer proof contexts were inspected, not
inferred solely from the correction notes. Relevant unchanged uses include
Frontier, finite/native correspondence, the complete demand client, Engine,
Temporal, FRP examples, the full indefinite-service client and its source APIs.
The statements retain strict registration provenance, finite predecessor versus
finite history, ordered duplicates, source honesty and scheduling assumptions,
and model-level resource/representation limits. No connected case or expected
result was weakened. Source-byte equality does not imply identical elaboration
environments, so complete downstream validation remains mandatory.

The narrow diff retains the public entrypoint, toolchain/dependency pins,
verification scripts, integrity guards, source policy, exhaustive audit-root
selection and axiom allowlist. No performance improvement is claimed from
unmatched focused runs.

## Stable findings and focused evidence

| Finding | Independent Spec disposition on `901f734` |
| --- | --- |
| **PERSIST-VAL-001** | **Retained fixed with prior compiler evidence.** The adapter's redundant success-branch tactic remains removed; unchanged 664-job focused evidence supports that correction. |
| **IMPORT-VAL-001** | **Fixed with focused compiler evidence; full gate pending.** Provider/instance/simp mechanism, unchanged proof and successful focused input identity independently matched. Original diagnostic retained. |
| **IMPORT-VAL-002** | **Fixed with focused compiler evidence; full gate pending.** Actual finite-union theorem and successful unchanged consumer inputs independently matched. Original diagnostic retained. |
| **IMPORT-VAL-003** | **Fixed with focused compiler evidence; full gate pending.** Real Archimedean provider/API and successful corrected example independently matched. The first focused run remains failed. |
| **IMPORT-VAL-004** | **Unresolved pending terminal compiler verification; proposed repair statically supported.** The prior unknown `Nat.size_pow` and False goal are preserved. The new import matches the existing proof, but its focused target is unfinished. |

All **23** source/config hashes in the successful r2 focused record match
committed `901f734` blobs. Before, at-start and after maps agree;
`inputs_unchanged` is true and exit code is **0**. The log ends with **1134
jobs** completed. The then-current HEAD field says `226ebae` because this was
a pre-capture development run; the exact recorded corrected bytes match this
candidate. It verifies the three specific repairs, not full acceptance.
The first run's exit **1**, individual Demand/Finite/client successes and
later `exists_nat_gt` failure remain visible.

For the current r3 focused target, **59** candidate source/config hashes and
the actual pinned Nat.Size provider hash match all **60** before/at-start
inputs. Mathlib is clean at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The provider hash is
`ab4306e1e29d9b254dd41af7e206591130414598403577921c7877e9919c249b`.
There is no terminal after map, exit code or unchanged-input conclusion yet.

No new Spec finding ID is allocated. IMPORT-VAL-004 remains an existing
required-build blocker, separate from the zero semantic findings and missing
whole-candidate acceptance evidence.

## Validation and continuation

At **22:20:51 UTC**, the active r3 focused record and log still show ongoing
`Examples.IndefiniteService` compilation for exact `901f734`, with
`acceptance: false`. Full `901f734` validation is not started according to
the current dispatch; no result is supplied. The old known-failing `324962e`
run cannot approve the successor. The new checkout's `.lake/verification.json`
was absent and final verify evidence was unavailable.

Resolve IMPORT-VAL-004 with terminal focused or matching successful full-build
evidence. Acceptance also requires successful stock
`./check.sh --candidate HEAD` for **all 957 integrated modules and the
exhaustive proof audit**, matching `.lake/verification.json`, and immediate
`./check.sh --verify-candidate HEAD` for this exact candidate. Both independent
axes must pass it. Neither source confidence nor focused success substitutes
for that full gate.

Retain this completed static assessment while examining new terminal evidence
on unchanged `901f734`. A changed candidate needs another complete fixed-base
round with all historical outcomes and finding IDs preserved. I ran no compiler
and changed no source, dependency, output or coordinator record; only the two
assigned Spec reports were written.

**Result:** #10018 base `70a1477d822efd4fdcec2007280f650bb4695eda`, linked
#10013 base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`, common candidate
`901f734161920a76f3b399a575805b9a1d31e971`; **0 Spec implementation findings,
no worst implementation severity; IMPORT-VAL-004 still pending compiler
verification; both scopes Spec Blocked with static assessment complete**.
