# Shared persistence and import prerequisite — independent Standards review, round 5

Date: 2026-11-02. Reviewer: `/root/prerequisite_review/standards`.
Validation status inspected at 22:16:04 UTC.

## Outcome

**Standards: Blocked.** The complete fixed-base static assessment is finished
with **0 new or unresolved Standards code/prose findings**, no worst code/prose
severity, and no heuristic-only change request. The required exact-candidate
validation is incomplete. IMPORT-VAL-004 remains a visible validation finding
whose proposed repair has been assessed statically but lacks a terminal
focused result. The full candidate check has not started according to the
current dispatch; no matching verification record or final verify evidence is
available.

This is the retained independent Standards axis for local #10013 round 5 and
linked #10018 round 3. It is not a passing review. The earlier completed
static reviews and the explicitly **PARTIAL / Blocked** review of `324962e`
remain historical outcomes, not approvals of this successor. The ticket-specific
report is [import-footprint-standards-r3.md](import-footprint-standards-r3.md).

## Immutable scope

- Candidate: `901f734161920a76f3b399a575805b9a1d31e971`.
- Frozen checkout: `/workspace/scratch/ca9a61d0bf30/import-correction-r3`.
  Read-only inspections resolved HEAD to that candidate and returned empty
  porcelain status. The pinned Mathlib checkout was also clean, at
  `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- #10013 fixed base and independently confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Full diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...901f734161920a76f3b399a575805b9a1d31e971`.
- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Narrow diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...901f734161920a76f3b399a575805b9a1d31e971`.
- Full scope: **14 files, 5 commits, 955 additions, 2 deletions**.
  Narrow scope: **6 files, 3 commits, 16 additions, 2 deletions**. No exclusions
  within either frozen scope.

The complete commit sequence is:

1. `ad730010ab1929bbd7a16a035c7990a6f328b178` — SharedList implementation.
2. `70a1477d822efd4fdcec2007280f650bb4695eda` — redundant adapter-tactic fix.
3. `226ebaef53b9eba97bef4b3b6ca364fdea488c69` — direct FRP import lists.
4. `324962e733886e66d6cd92af6cb68627ed4c8f1d` — three consumer provider imports.
5. `901f734161920a76f3b399a575805b9a1d31e971` — direct natural-size theorem import.

The fourteen files are the four SharedList semantic modules, its resource
module, `Examples/SharedList.lean`, `SquareApplications.lean`, the frozen
`docs/research/pfds-shared-persistence.md`, and the six import consumers listed
below. The original eight SharedList/integration/documentation files are
byte-identical to `226ebae`. The latest delta from `324962e` is only
`import Mathlib.Data.Nat.Size` in `Examples/IndefiniteService.lean`. I independently
matched all fourteen manifest SHA-256 values to committed candidate blobs.

Current main `conaled`, Chapter 2 `99a29dc`, foundation `a3feaff`, pure `ea8afa`
and Chapter 3 research are separate scopes. This bounded prerequisite accepts
no chapter and does not advance the book/thesis acceptance frontier.

## Requirements, standards and evidence use

The requirements remain saved `REQUEST.md`, `REQUEST-union-v2.md`,
`shared-persistence.md` version 2 and `import-footprint.md` version 1. I
independently recalculated their four unchanged fingerprints and matched
`../validation/import-footprint-candidate-r3.json`. The full book and thesis
are available under the union request; this does not enlarge this bounded
candidate into chapter acceptance or permit weakening its validation.

The applicable candidate AGENTS, code-review skill, shared review-loop,
example-driven statement-review guidance, architectural quality/domain/glossary
rules, ADR index and applicable ADRs 0001, 0002 and 0010, language-direction
criteria, README validation rules and subordinate review heuristics were read
in the retained full review. I independently confirmed the fourteen guidance
files are unchanged from `226ebae` and retained their application here. No
additional scoped AGENTS, CODING_STANDARDS or CONTRIBUTING rule applies to
these paths. Local tracking and no external publication follow the user's
instructions.

The retained full Standards analysis, all earlier findings/outcomes, the source
statement assessment, the candidate's frozen implementation note, and the new
correction evidence were considered. I independently reread all four
SharedList semantic modules, the resource module, connected cases and frozen
note on this candidate. Existing heap, measured-resource, asymptotic and
relational-interface analysis remains applicable because those inputs are
unchanged. The partial `324962e` review was completed by inspecting the actual
providers, matching focused input identities, reviewing the new client and
reassessing the entire fixed-base scope; it was not relabeled as completed.

## Architecture and methodology assessment

`Store` uses the existing `Durability.Heap`, `Extends`, `put` and `extends_put`
facilities. Their fresh-write preservation needs vacancy, not the later crash
protocol's assumptions. `Store.vacant` supplies that premise. `Represents`
separately connects a root to a finite list through actual occupied cells and
strictly decreasing tail addresses. It neither constrains unrelated cells to
be lists nor identifies observational equality with root identity.

Append and update follow heap links and expose both value semantics and actual
root-sharing conclusions. `Resources.Measured` remains the existing ordinary
value/observation pair; frontier differences count modeled allocations and the
recursion separately counts visits. The observation layer specializes existing
`RelRep`, `RelSquare` and `Relational.compose`. There is no competing container
hierarchy, total malformed-heap decoder, injectivity requirement, runtime
refinement claim or undeclared setting-transport mechanism.

The module placement, reuse and public integration satisfy the applicable
architectural and ADR guidance. `SquareApplications` retains the existing
entrypoint imports and adds both `Examples.SharedList` and
`Applications.Resources.SharedList`; the semantic modules are reached through
ordinary imports. The model states the missing physical-sharing obligation,
and the retained equal-valued unshared-root case demonstrates why value-level
suffix observations alone do not establish that obligation. Connected examples
construct premises and consume the public results, including fresh allocation
and preservation of old versions.

The new SharedList Lean modules retain explicit `autoImplicit false` and
`warningAsError true`. No added proof placeholder, application axiom, unsafe
declaration or native-evaluation proof shortcut was identified in the changed
source. This source inspection does not establish the exhaustive proof audit.

## Statement and connected-case assessment

| Family | Assessment on the complete candidate |
| --- | --- |
| Representation and allocation | `Represents.unique` establishes a unique list observation at one root, without unique representation. `allocate_retains` preserves arbitrary previously represented roots by heap extension. `allocate_represents`, `prepend_correct` and `load_represents` construct satisfiable valid states; old/new-root and both-heads applications use these results. |
| Fuel and malformed traversal | `Represents.length_le_next` supplies public fuel from occupied-cell vacancy and strict descent. `advance_prefix`, `advance_mono` and `advance_end` describe actual reads. Encountered missing cells and non-null exhausted traversal fail; null base cases retain their specified behavior. The contracts do not assert validation of an untraversed tail or right root. |
| Append | `appendRun_correct` relates actual heap traversal to `xs ++ ys`, all-old-cell retention, exactly the left length in allocations, left length plus one in visits, and the original right root after the copied prefix. Connected append/head cases use these conclusions and composed correctness. |
| Update | A successful in-range update establishes `List.set`, exactly `i + 1` allocations/visits, old-version retention and equality with the original untouched tail root. Validity and `advance_prefix` prevent equality of two failed traversals from masquerading as sharing. At or beyond the length, failure returns no output store and counts length plus one visits; retained cases preserve that distinction. |
| Optional observations | Empty-tail failure and successful singleton removal remain `none` and `some none`. `optionalRepresentation` preserves success/failure. A composed head observation may forget information without equating those representations. |
| Suffix values | `suffixesRun_correct` links actual roots to standard `List.tails` in order, including the null suffix, with exact visit/root-list/non-null counts. Strict address descent supplies root distinctness without assumptions about payload equality. |
| Suffix storage | Successful execution yields an actual-tail `SuffixChain`, then `ClosedRoots`; independent `Reaches`/`ReachableFrom` identify reachable addresses with the non-null enumeration. `nonnull_nodup` prevents double counting, and `suffixes_storage` links these facts to the count. The equal-valued but unshared counterexample is retained. |
| Resource bounds | The linear results instantiate `Resources.isBigO_of_nat_bound` with explicit constants and eventual thresholds for proved count functions. The standard asymptotic interface is preserved without claiming machine-time or actual Lean-allocation bounds. |

I checked the statements, relevant definitions and clients for vacuity,
circular hypotheses, mismatched quantifiers/domains and concealed equality
claims. No Standards defect was identified. `Reaches.here` means zero-edge
address reachability, not occupancy for arbitrary heaps; successful chains
and represented inputs supply occupancy for the reviewed storage result.
The modeled shared-space count includes element cells and outer root-list
cells, and excludes unrelated heap cells, payload size, allocator metadata,
stack usage, reclamation and finite machine capacity. No arbitrary branching
amortization or machine-memory result is claimed.

## All-six import preservation and providers

I independently compared the fixed-base and candidate Git blobs, preserving
all original line terminators while removing only `import ` lines. All six
non-import byte sequences are identical. This covers declaration statements,
proof bodies, local options, examples and comments; it does not claim that
compiled environments or kernel artifacts are identical.

| File | SHA-256 of identical non-import bytes at `70a1477` and `901f734` |
| --- | --- |
| `Applications/FRP/Demand.lean` | `5efb68e7873b49f74f29dc6db557ffa1ff9667f3590e8c1b5f981db863feb3c0` |
| `Applications/FRP/Equivalence.lean` | `063f840af1065f9af828204d4c56dd6a314a49aa59a2f193332b175fd3f22188` |
| `Applications/FRP/Finite.lean` | `7b0284ad643243c0bf20061d164feaef4f68029cb7b97a6f10fb3d4ce588af86` |
| `Applications/FRP/Spec.lean` | `1d59e171221416cb3eabc47bc74b788d347a3f2456379228d5101bb64632e35a` |
| `Examples/FRP.lean` | `72a799f7804b7e0a5651d2e1a218e74b8071726bb0b582aaceb91e87f0183194` |
| `Examples/IndefiniteService.lean` | `1a5ce27ad026bb55452a3106e8783ce94ff7f95a06a5a2bbe4971dd9ff52a652` |

Provider assessment used actual source in the pinned Mathlib checkout, not
only the implementation worker's comparison:

| Consumer | Provider and unchanged-use assessment |
| --- | --- |
| `Spec` | Direct real-number, finite-set sorting and finite-set evidence imports correspond to the actual facilities used. Existing local function-category and Cartesian-map imports remain. The complete-file review from `226ebae` remains applicable. |
| `Equivalence` | Direct real arithmetic, Finset maximum/cardinality, finite range, lexicographic product order, natural intervals, linear arithmetic, numeric normalization and positivity providers correspond to its order/enumeration proofs and retained counterexamples. The complete-file review from `226ebae` remains applicable. |
| `Demand` | `Mathlib.Order.SuccPred.Nat` supplies `Nat.instSuccAddOrder` and imports the successor/addition API. Its `[simp]` theorem `Order.lt_add_one_iff` accounts for the unchanged `simp_all [next]` reduction in `pending_registered`. The strict earlier-registration contract remains unchanged. |
| `Finite` | `Mathlib.Data.Set.Finite.Lattice` defines `Set.Finite.biUnion`, combining finite outer support with finite inner sets. This is the actual theorem required by the unchanged `finiteHistory` proof. |
| `Examples/FRP` | `Mathlib.Algebra.Order.Archimedean.Real.Basic` supplies the real Archimedean instance and the imported general `exists_nat_gt` API. The unchanged ticks example chooses a natural above its real cutoff and derives finiteness from `Iio`. |
| `Examples/IndefiniteService` | `Mathlib.Data.Nat.Size` declares `Nat.size_pow : size (2 ^ n) = n + 1`. The unchanged proof specializes a purported uniform bound to `2 ^ bound`, rewrites by this theorem, and closes the impossible successor inequality. The import names the exact missing provider. |

The inspected `Mathlib/Data/Nat/Size.lean` SHA-256 is
`ab4306e1e29d9b254dd41af7e206591130414598403577921c7877e9919c249b`.
The declaration is at line 94, with the namespace and implicit natural argument
expected by the unchanged proof.

The affected consumer inventory includes Spec to Frontier/Finite, Equivalence
to Finite/Examples.FRP, Demand to Engine/Temporal/Examples.FRPDemand, Finite to
Examples.FRP, and both example modules to SquareApplications. I retained the
earlier complete Spec/Equivalence/Finite/FRP/Frontier review, reread Demand and
the relevant proof/client sections, inspected Engine's state/step/refinement
and transfer interface, and read complete Temporal and IndefiniteService
sources. These preserve the distinctions among finite predecessors, finite
history, ordered simultaneous occurrences, strict switching, demand
registration, truthful frontier evidence and independent fairness hypotheses.
The retained indefinite-service applications cover stream/compiled-delay and
composition behavior, productivity and representation transport, together
with the unbounded-size/history witnesses; no case or expected result changed.

The import-only diff changes no toolchain/dependency pin, build script, guard,
source policy, audit root, axiom allowlist or public integration entrypoint.
No all-library replacement or local proof shim was introduced. A complete
build remains necessary because import environments affect downstream
elaboration even when all declaration source bytes are preserved. This review
makes no timing or memory improvement claim.

## Stable findings and independent dispositions

| Stable finding | Evidence and current disposition |
| --- | --- |
| **PERSIST-VAL-001** | **Retained fixed with prior compiler evidence.** `70a1477` removes only the redundant success-branch `change` in `updateSquare`; the failure branch, theorem, hypotheses and operations are unchanged, and the warning policy remains. `../validation/persistence-focused-r2.log` explicitly compiles Observation and Examples.SharedList and ends successfully with 664 jobs. This proves the particular linter repair, not full successor acceptance. |
| **IMPORT-VAL-001** | **Fixed with focused compiler evidence; full candidate validation pending.** The original strict-successor proof failure is retained in `../validation/import-footprint-226ebae-observed-errors.json`. The actual successor instance/simp provider above and matching focused input evidence support the Demand import repair without weakening its theorem or proof. |
| **IMPORT-VAL-002** | **Fixed with focused compiler evidence; full candidate validation pending.** The original `biUnion` resolution failure remains recorded. The direct `Set.Finite.biUnion` provider and matching focused compilation establish the specific Finite import repair. |
| **IMPORT-VAL-003** | **Fixed with focused compiler evidence; full candidate validation pending.** The first correction run's missing `exists_nat_gt` failure is preserved. The inspected real Archimedean provider and successful second focused run establish the specific example import repair. |
| **IMPORT-VAL-004** | **Proposed repair statically supported; terminal compiler verification pending.** `../validation/import-footprint-324962e-observed-errors.json` preserves the unknown `Nat.size_pow` at `Examples/IndefiniteService.lean:104:6` and unsolved goal at `101:56`. The new direct provider supplies the exact theorem, and all non-import bytes are unchanged. The current focused run has no terminal result, so this validation finding remains open rather than being declared fixed. |

The successful earlier correction record
`../validation/import-footprint-r2-focused-r2.json` names development HEAD
`226ebae` with the corrected then-uncommitted sources. Its before, at-start and
after maps contain the same 23 source/config hashes, `inputs_unchanged: true`
and exit code 0. I independently matched **all 23 hashes to committed
`901f734` blobs**, with no mismatch. The pinned offline Nix command builds
`Examples.FRPDemand` and `Examples.FRP` with `LEAN_NUM_THREADS=1`; the log ends
`Build completed successfully (1134 jobs)`.

That successful log reuses the normal Lake outputs for Demand and Finite
compiled in the first focused correction run, and compiles the repaired FRP
example in the second. The first log records Demand, Examples.FRPDemand and
Finite compilation, followed by the `exists_nat_gt` failure; its failure is
retained. This paired, input-matched evidence is sufficient for the specific
IMPORT-VAL-001 through 003 dispositions. It is not approval of a full candidate
or a matched performance benchmark.

The earlier `324962e` cache-copy record was inspected by metadata, not treated
as validation. It records ordinary complete outputs selected using identical
source bytes, 599 modules/4193 files copied, no source inconsistencies and
`approval_copied: false`, `acceptance: false`. No success/approval record from
that candidate can approve `901f734`. Normal guard/invalidation and the
unchanged complete check remain mandatory.

There are **0 new Standards-specific code/prose findings**, and no new
`PERSIST-STD` or `IMPORT-STD` ID is allocated. There is **1 pending stable
validation-finding disposition**, IMPORT-VAL-004, in addition to the missing
full acceptance gate. Its previous-candidate compiler failure is not erased
by source-only confidence in the proposed repair.

## Exact validation state and continuation

At 22:16:04 UTC, the current focused record
`../../active-validation/import-footprint-r3-focused-r1.json` identifies exact
HEAD `901f734161920a76f3b399a575805b9a1d31e971`, its private build directory and
the pinned offline Nix command for `lake build Examples.IndefiniteService` with
one Lean thread. Its 60-entry before and at-start snapshots are equal; I
independently matched all sixty recorded file hashes to the available frozen
inputs. It records a 22:02:16 UTC start but **no end, exit code, final after
snapshot or final `inputs_unchanged` result**. The corresponding live log
continues compiling dependencies and contains no terminal target success.
It therefore does not yet close IMPORT-VAL-004.

The full `901f734` check has not started according to the current dispatch.
The still-running full `324962e` check already has the recorded compiler
failure and cannot approve a changed candidate. At inspection,
`import-correction-r3/.lake/verification.json` was absent. No final candidate
verify evidence was supplied.

Required continuation evidence is:

1. The terminal focused result and unchanged source/provider identities for
   the IMPORT-VAL-004 correction, or exact full-build evidence covering that
   target and those identities.
2. Successful terminal execution of the unchanged full
   `./check.sh --candidate HEAD` on exact `901f734`, covering all 957 integrated
   project modules, mandatory guards/source coverage and the exhaustive proof
   audit.
3. The resulting matching `.lake/verification.json` for that candidate and
   validated inputs, followed by immediate final
   `./check.sh --verify-candidate HEAD` evidence for the same candidate.

The coordinator must also retain the independent Spec outcome on this exact
candidate. Neither focused success nor this complete static assessment can
replace either axis or the full validation requirements.

On unchanged `901f734`, this axis can retain the completed static assessment
and independently assess supplied terminal evidence. A changed candidate
requires renewed complete fixed-base review with both axes and all stable
findings retained. No frozen source, dependency or build output was modified,
and no compilation was performed by this reviewer. Only the two authorized
round reports were written after release of the checkpoint021 hold.

## Result

| Scope | Fixed base | Candidate | Findings / worst severity | Standards outcome |
| --- | --- | --- | --- | --- |
| #10013 round 5 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` | `901f734161920a76f3b399a575805b9a1d31e971` | 0 Standards code/prose findings; worst code/prose severity: none. IMPORT-VAL-004 remains pending compiler verification; the full gate is unavailable. | **Blocked; static assessment complete** |
| #10018 round 3 | `70a1477d822efd4fdcec2007280f650bb4695eda` | `901f734161920a76f3b399a575805b9a1d31e971` | 0 Standards code/prose findings; worst code/prose severity: none. Same one pending validation finding and missing full exact gate. | **Blocked; static assessment complete** |
