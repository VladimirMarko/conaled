# Shared persistence and import prerequisite — independent Spec review, round 5

Date: 2026-11-02. Reviewer: `/root/prerequisite_review/spec`.
Validation status inspected at **22:20:51 UTC**.

## Outcome

**Spec: Blocked; complete fixed-base static assessment finished.** There are
**0 new or unresolved Spec implementation findings**, with no worst
implementation severity. **IMPORT-VAL-004 remains unresolved pending terminal
compiler verification of its statically supported import repair.** Full
exact-candidate validation, the matching success record and final verification
are also unavailable. The unresolved validation finding is separate from the
zero semantic/specification findings; this is not candidate approval.

This is the retained independent Spec axis for local #10013 round 5 and linked
#10018 round 3. The ticket-specific result is
[`import-footprint-spec-r3.md`](import-footprint-spec-r3.md). Both reports record
one assessment with two fixed scopes, not another review loop.

My last completed static Spec assessment was candidate `226ebae`, recorded in
`shared-persistence-spec-r3.md` and `import-footprint-spec-r1.md`. It remained
Blocked and its later observed compiler failures are preserved. **I did not
review `324962e`.** Spec was held before dispatch on that candidate; Standards'
round-4/linked-round-2 reports remain explicitly **PARTIAL / Blocked**. Neither
that partial assessment nor any older static report is promoted to approval
of `901f734`.

## Immutable complete scope

- Candidate: `901f734161920a76f3b399a575805b9a1d31e971`.
- Frozen checkout: `/workspace/scratch/ca9a61d0bf30/import-correction-r3`.
  Read-only inspections resolved exact candidate `HEAD` and returned empty
  porcelain status at initial and final inspection.
- #10013 fixed base and independently confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Full diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...901f734161920a76f3b399a575805b9a1d31e971`.
- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Narrow diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...901f734161920a76f3b399a575805b9a1d31e971`.
- Full scope: **14 files, 5 commits, 955 insertions and 2 deletions**.
  Narrow scope: **6 files, 3 commits, 16 insertions and 2 deletions**.
  No exclusions within either scope.
- Commit sequence: `ad73001` SharedList implementation; `70a1477` adapter-tactic
  correction; `226ebae` direct imports in FRP Spec/Equivalence; `324962e` three
  consumer imports; `901f734` the natural-size provider import. The full SHAs
  and titles are preserved in `../validation/import-footprint-candidate-r3.json`.

The complete scope contains the four SharedList semantic modules, its resource
module, `Examples/SharedList.lean`, `SquareApplications.lean`, frozen
`docs/research/pfds-shared-persistence.md`, and all six import consumers below.
I independently matched **all fourteen manifest file hashes** to both committed
candidate blobs and the working files. The original eight SharedList/integration/
documentation files are byte-identical to my last completed assessment at
`226ebae`. The latest delta from `324962e` is exactly one import line in
`Examples/IndefiniteService.lean`; the entire earlier import scope remains
part of this assessment.

Main `conaled`, Chapter 2 `99a29dc`, foundation `a3feaff`, pure `ea8afa`, and
Chapter 3 research are outside this candidate. No chapter is accepted and no
book/thesis implementation frontier advances through this prerequisite review.

## Requirements, guidance and evidence use

I independently matched all four saved requirement fingerprints to the current
manifest: original `REQUEST.md`, union clarification `REQUEST-union-v2.md`,
unchanged SharedList requirements version 2 and import-footprint version 1.
The whole task continues to cover the union of the book and thesis. Both
sources are available; availability alone is not inspection or proof coverage.
The bounded prerequisite requirements have not changed.

The current candidate's AGENTS and example-driven statement-review guidance
were reread. Candidate guidance under the code-review/review-loop,
architecture/domain/glossary, relevant ADRs 0001/0002/0010 and README validation
paths is unchanged from the retained full review. I applied that guidance,
including usable premises, exact meanings, quantifier/domain checks, explicit
resource models and connected public uses. The frozen implementation note and
saved source-to-statement assessment were reread; the latter remains background
evidence, not a substitute for either acceptance axis.

The coordinator records, earlier reports, original diagnostics, correction
research, source comparisons and focused-build records were read. Standards'
new report is another axis's outcome, not evidence that replaces my own
provider, source, input-identity or specification assessment. The comparisons
and dispositions below were independently established.

## SharedList requirements and statement reassessment

The retained full mathematical assessment remains applicable to the unchanged
candidate bytes and reused interfaces. This round covers every family against
the original #10013 base; it does not review only the latest import line.

| Required family | Current-candidate assessment and connected evidence |
| --- | --- |
| Fresh allocation and old versions | `Store.vacant` supplies actual frontier freshness to `allocate_extends` and the existing `Durability.extends_put`. `allocate_retains` preserves an arbitrary old represented root, independently of the new tail. `allocate_represents` separately constructs the new list. The retained `[3]` and `[2,3]` case uses these generic results and head correctness; `allocate_next` supplies the one-cell increment at each of its two allocations. |
| Usable representation and fuel | `Represents` follows occupied cells with strictly decreasing tail addresses, without constraining unrelated cells. `unique` gives a unique list observation at a root, not a unique root per value. `length_le_next` follows from occupancy/vacancy and strict descent; `load_represents` constructs valid instances for all finite lists. The public frontier fuel is therefore sufficient on represented inputs, not an assumed-success premise. |
| Actual append path copying | The raw operation follows heap tails and allocates the copied left prefix after recursion. `appendRun_correct` connects its actual result to concatenation, old-cell extension, exactly left-length new cells, left-length-plus-one visits and the exact original right root after the prefix. `append_shares` retains both inputs and verifies the two copied cells; `append_client` consumes the composed head result. |
| Partial indexed replacement | Success requires `i < length` and proves `List.set` agreement only there, `i+1` allocations/visits, old-cell retention and equality of the actual untouched-tail roots. Validity and `advance_prefix` prevent the sharing equality from being merely two failed traversals. The index-1 case preserves the old list and uses the public theorem. Failure includes index equal to length and returns `none`, not `List.set`'s out-of-range no-op; recursive allocations are mapped only over success. |
| Failure and observations | Encountered missing reads and non-null exhausted fuel fail. Null cases retain their documented one-visit distinction. Raw traversals do not validate untraversed roots or tails. Empty-tail failure and successful singleton removal remain `none` versus `some none`. Optional relational adapters preserve failure/success, while subsequent head observation may intentionally forget a distinction. Public clients use `Relational.compose`. |
| Suffix values and graph sharing | The operation returns the roots it actually follows through the original element heap, including null. `suffixesRun_correct` preserves `List.tails` order, visits, entry counts and distinct roots without requiring distinct payloads. Successful traversal yields `SuffixChain`; closure and independent graph reachability identify the reachable addresses; `nonnull_nodup` makes the enumeration duplicate-free. `suffixes_storage` connects those results to the actual run. |
| Storage counterexample and bounds | The retained equal-valued distinct-root counterexample omits an actually reachable cell and fails closure. Thus value equality and distinct roots alone are still not treated as storage evidence. `sharedSpace` requires the graph interpretation and counts reachable element cells plus outer root-list cells; the explicit `IsBigO` results concern `n+1` and `2*n+1` count expressions. |

`Reaches.here` still means zero-edge address reachability, without independently
asserting occupancy. Successful suffix chains and represented-input premises
supply occupancy in the reviewed storage application. No generic live-cell
claim is inferred from bare reachability. The fixed-cell model still excludes
payload size, allocator metadata, traversal-stack space, reclamation, physical
retention and finite capacity. Heap reads and natural-address arithmetic are
not asserted constant-time Lean operations. No crash-persistence, branch-safe
amortization or machine-runtime conclusion is introduced.

The preserved examples construct their premises and consume public contracts.
The unchanged public entrypoint imports both `Examples.SharedList` and the
resource module, retaining all six new Lean modules in the required integrated
build/audit closure. I found no new vacuity, circular premise, weakened case,
unjustified scope reduction or mathematical discrepancy.

## All six import consumers: exact preservation

I compared each committed candidate file directly with fixed #10018 base
`70a1477`, removing only lines beginning `import ` and retaining all remaining
bytes and newline structure. Every comparison is equal:

| Consumer | Equal non-import SHA-256 |
| --- | --- |
| `Applications/FRP/Demand.lean` | `5efb68e7873b49f74f29dc6db557ffa1ff9667f3590e8c1b5f981db863feb3c0` |
| `Applications/FRP/Equivalence.lean` | `063f840af1065f9af828204d4c56dd6a314a49aa59a2f193332b175fd3f22188` |
| `Applications/FRP/Finite.lean` | `7b0284ad643243c0bf20061d164feaef4f68029cb7b97a6f10fb3d4ce588af86` |
| `Applications/FRP/Spec.lean` | `1d59e171221416cb3eabc47bc74b788d347a3f2456379228d5101bb64632e35a` |
| `Examples/FRP.lean` | `72a799f7804b7e0a5651d2e1a218e74b8071726bb0b582aaceb91e87f0183194` |
| `Examples/IndefiniteService.lean` | `1a5ce27ad026bb55452a3106e8783ce94ff7f95a06a5a2bbe4971dd9ff52a652` |

The values match the supplied fixed-base comparison record, independently of
its assertions. No other path changes in the narrow diff. All declaration
statements, definitions, proof scripts, examples, options and comments remain
unchanged. This is source-byte preservation; it is not a claim of identical
elaborated environments or proof artifacts after changing imports.

The public entrypoint, verification/build scripts, integrity guards, toolchain,
dependency pins, source policy, exhaustive audit-root selection and axiom
allowlist have not changed in #10018. Full downstream compilation and audit
remain mandatory. No matched timing or memory benchmark is supplied, so no
performance improvement is inferred from source reduction or focused runs.

## Provider, proof and affected-use assessment

### Original direct imports in Spec and Equivalence

These two complete files remain identical to the previous reviewed candidate.
Their direct providers still correspond to their real-number, finite-set,
sorting, finite-predecessor enumeration, lexicographic-order, natural-interval
and arithmetic-tactic uses. Their semantics retain ordered simultaneous
occurrences, the finite-predecessor/finite-history distinction and strict
switching. I retained the previous full source assessment and checked the
current fixed-base preservation and provider context. The later failures
demonstrate why that static assessment did not establish full integration.

### IMPORT-VAL-001: strict registration provenance

The unchanged `Demand.pending_registered` conclusion requires a registration
at a **strictly earlier** transition. In the newly registered successor case,
the proof calls `simp_all [next]`, then supplies witness `n` and `le_rfl`.
I inspected the actual pinned provider: `Mathlib.Order.SuccPred.Nat` publicly
imports `Mathlib.Algebra.Order.SuccPred` and supplies `Nat.instSuccAddOrder`.
The imported `[simp] Order.lt_add_one_iff`, under the required order/successor
instances, rewrites `x < y + 1` to `x ≤ y`. This restores the simplifier context
that makes the existing witness proof appropriate; it does not weaken the
theorem's strict earlier-transition statement.

I read the complete Demand module and `Examples.FRPDemand`, including the
direct provenance use, known-empty answer, ordered duplicates, no repeated
emission, inhabited progress witnesses, stalled-source and starved-processing
counterexamples. Engine and Temporal use the same Demand operations and
contracts. Source honesty, availability and processing fairness remain
separate, explicit assumptions; no restored import supplies them as facts.

### IMPORT-VAL-002: finite union of finite occurrence sets

`FRP.Native.finiteHistory` forms the union of finite index sets over the
event's finite past support. The actual pinned
`Mathlib.Data.Set.Finite.Lattice` declares `Set.Finite.biUnion` with exactly
the finite-index-set and per-member finite-set premises used by `s.biUnion`.
The consumer still constructs those premises from finite past support and
finite list lengths. No finiteness coercion, proof rewrite or strengthened
assumption is introduced. The finite/native carrier bridge and ordered,
duplicate-preserving merge applications remain unchanged.

### IMPORT-VAL-003: natural bound above a real timestamp

`Examples.FRP.ticks_finiteHistory` still uses `exists_nat_gt t` to bound a
real timestamp by a natural number, then restricts occurrence indices to a
finite initial segment. The actual
`Mathlib.Algebra.Order.Archimedean.Real.Basic` supplies the real Archimedean
instance and imports the general API; the inspected `exists_nat_gt` statement
has the appropriate strictly ordered semiring and Archimedean requirements.
The infinite future remains unbounded as a whole, while every history prefix
is finite. The import does not change that distinction or its roundtrip case.

### IMPORT-VAL-004: unbounded natural representation size

I read the complete `Examples.IndefiniteService` client and the actual pinned
`Mathlib.Data.Nat.Size` provider. At line 94 the provider declares
`Nat.size_pow : size (2 ^ n) = n + 1`. The unchanged example assumes a uniform
bound, applies it to `2^bound`, rewrites to `bound+1 ≤ bound`, then uses the
existing `omega` contradiction. The new import supplies precisely the missing
rewrite. Its file hash is
`ab4306e1e29d9b254dd41af7e206591130414598403577921c7877e9919c249b`.

The example continues to distinguish a fixed field count from a uniformly
bounded representation size. Its neighboring retained cases cover finite
delay traces, stream composition, explicit work/arena/retained-cell bounds,
parallel and pure composition, compiled-source connection, an inhabited finite
wait environment, and redundant-complement state transport. The source APIs
still state model-level bounds; the IO adapter explicitly retains trusted
host allocation and IO completion rather than proving physical heap bounds.
The history-length counterexample is also unchanged. No case, expectation,
proof body or target assumption has been weakened.

The static provider repair is supported, but the exact focused target has not
completed. Consequently IMPORT-VAL-004 remains unresolved as a validation
finding; no new speculative mathematical finding is allocated for it.

## Focused evidence identity and stable dispositions

The pinned Mathlib checkout is clean at manifest revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The four requirement hashes and all
candidate source/configuration identity checks described above matched.

For the earlier second focused correction run, I independently matched all
**23 recorded source/config hashes** in
`../validation/import-footprint-r2-focused-r2.json` to committed `901f734`
blobs. Its before, at-start and after maps are equal; it records
`inputs_unchanged: true` and exit code **0**. Although its then-current HEAD
was `226ebae`, the recorded corrected working-source inputs match this
candidate. The pinned offline Nix command builds `Examples.FRPDemand` and
`Examples.FRP` with one Lean thread; the log ends with **1134 jobs** completed
successfully.

The first focused run remains recorded as exit **1**. It compiled Demand,
Finite and the demand client, then exposed unknown `exists_nat_gt`. The second
run retains the repaired inputs and compiles the corrected FRP example through
ordinary Lake reuse. This is evidence for the three particular corrections,
not a successful full-candidate check or a reason to relabel the first failure.

For the currently running r3 focused check, all **60** before/at-start inputs
match: **59** committed candidate source/config files plus the pinned
`Mathlib.Data.Nat.Size` provider. The maps are equal, but there is no terminal
after snapshot or unchanged-input result yet.

| Stable finding | Independent Spec disposition on `901f734` |
| --- | --- |
| **PERSIST-VAL-001** | **Retained fixed with prior compiler evidence.** The success-branch redundant tactic removal remains, the failure branch and mathematical contract are unchanged, and the retained 664-job focused result verifies that correction. Full acceptance remains separate. |
| **IMPORT-VAL-001** | **Fixed with focused compiler evidence; full gate pending.** Actual successor-order provider/instance/simp mechanism and unchanged Demand proof were independently assessed; successful focused inputs match the candidate. Original diagnostic retained. |
| **IMPORT-VAL-002** | **Fixed with focused compiler evidence; full gate pending.** Actual finite-union theorem, constructed finiteness premises and matching successful consumer inputs were independently assessed. Original diagnostic retained. |
| **IMPORT-VAL-003** | **Fixed with focused compiler evidence; full gate pending.** Actual real Archimedean provider/API and the unchanged finite-history witness match the successful second run. The first focused failure remains a failure. |
| **IMPORT-VAL-004** | **Unresolved pending terminal compiler verification; proposed repair statically supported.** The original unknown `Nat.size_pow` and resulting False goal remain recorded. The direct provider matches the unchanged proof, but current focused execution has no terminal result. |

There are **0 new or unresolved Spec implementation findings** and no new
`PERSIST-SPEC` or `IMPORT-SPEC` identifier. One existing validation finding
remains open, in addition to the missing full acceptance gate. No source or
requirement correction is requested by the completed static assessment.

## Required validation and continuation

At **22:20:51 UTC**, the active
`../../active-validation/import-footprint-r3-focused-r1.json` identifies exact
`901f734`, its private build directory and target `Examples.IndefiniteService`.
It has a start time but no end time, exit code, final after map or final
unchanged-input result; `acceptance` is false. The log continues dependency
compilation. Partial progress does not close IMPORT-VAL-004.

Full `901f734` validation has not started according to the current dispatch;
no full result for it is supplied. The known-failing `324962e` run remains
recorded as running and cannot approve its successor. The new checkout's
`.lake/verification.json` was absent, and final verification evidence was
not supplied. No prior success record or approval may be copied to this candidate.

Required continuation on unchanged `901f734` is:

1. Terminal focused evidence, or matching successful exact full-build coverage,
   resolving IMPORT-VAL-004 with unchanged input identity.
2. Successful terminal stock `./check.sh --candidate HEAD` for the exact
   candidate, covering **all 957 integrated project modules**, source/coverage
   and integrity checks, and the exhaustive proof audit.
3. Matching `.lake/verification.json` and immediate final
   `./check.sh --verify-candidate HEAD` resolving to
   `901f734161920a76f3b399a575805b9a1d31e971`.

Both independent axes must assess their required evidence and pass the same
candidate before acceptance. The completed static assessment can be retained
while new terminal evidence is reviewed. A changed candidate requires the
next full fixed-base round with every historical finding/outcome preserved.

I performed no compilation and changed no frozen source, dependency, build
output or coordinator record. Only the two authorized Spec reports were
written. Root owns compilation, corrections and final delivered-candidate
verification.

## Result

| Scope | Fixed base | Candidate | Count / worst severity | Spec outcome |
| --- | --- | --- | --- | --- |
| #10013 round 5 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` | `901f734161920a76f3b399a575805b9a1d31e971` | 0 Spec implementation findings; worst implementation severity: none. IMPORT-VAL-004 pending compiler verification, plus missing full gate. | **Blocked; static assessment complete** |
| #10018 round 3 | `70a1477d822efd4fdcec2007280f650bb4695eda` | `901f734161920a76f3b399a575805b9a1d31e971` | Same complete-scope Spec finding count and validation limitations. | **Blocked; static assessment complete** |
