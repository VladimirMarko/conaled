# Chapter 2 — independent Spec review, corrected round 3

## Outcome

**Blocked pending exact integrated validation.** The full-scope static Spec
assessment is complete, with **zero new or unresolved implementation or
source-coverage findings** and no requested source correction. The import
corrections are appropriate direct providers for the preserved proofs.
IMPORT-VAL-004 still needs terminal compiler evidence, and CH02-PRE-005 still
requires the complete exact chapter build/audit, matching record and final
verification. Neither an interrupted check nor a prerequisite check approves
this chapter candidate.

- Reviewer: `/root/chapter02_review/spec`, continuing the same independent axis.
- Date: 2026-11-02.
- Fixed full-chapter base: `82501d108f33c62d21b5e0d0f7d2376b902d8d49`.
- Candidate: `99a29dcd02eb529fbefbb675e244a8c47b78cdef`.
- Read-only checkout: `validation-chapter02-r3`, branch `pfds/ch02-review-r3`.
- Full diff: `git diff 82501d108f33c62d21b5e0d0f7d2376b902d8d49...99a29dcd02eb529fbefbb675e244a8c47b78cdef`.
- Scope: 42 files, including 39 Lean files, 4,468 insertions and 4 deletions,
  33 commits. No exclusions. The complete commit list is retained in
  `chapter02-99a29dc-dispatch.md`.

## Exact scope and reuse of the completed assessment

I independently confirmed candidate HEAD, clean checkout and the original
fixed merge-base. All 42 file hashes in
`../validation/chapter02-candidate-r3.json` match the current checkout, and its
file set exactly equals the full fixed-base diff. I also compared every hash
from the 38-file round-1 manifest to this candidate: **all 38 are unchanged**.
The complete candidate-to-candidate diff adds only four import commands in
the four previously unchanged consumer files described below.

The complete source/statement assessment in `chapter02-spec-r1.md` therefore
remains applicable evidence for every Chapter 2 formal definition, proof,
example, public-entrypoint change and source-documentation byte. This round
reassesses the full scope using that matching analysis, the expanded manifest,
the changed import contexts, the affected consumer statements and the new
validation evidence. It does not reduce review to four lines or treat the old
Blocked outcome as approval of a new candidate.

Requirements and applicable repository standards are unchanged. The saved
specification hashes match the earlier chapter requirements and current
dispatch:

| File under `session/requirements/` | SHA-256 |
| --- | --- |
| `REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `chapter02.md` version 1 | `240b6bfec9f9e8599f1034abc309499928c8472edf76481b553ef99ce40ff944` |
| `import-footprint.md` version 1 | `cf8fb3133b83ac59fdf6fd46b818d8b279d96385f5de50da843ef9b7fd62444d` |

The import requirement expressly permits adding direct providers for recorded
transitive-import failures while preserving proof bodies, statements, examples,
toolchain, dependency pins and every acceptance mechanism. No requirement
weakening or change of chapter source scope is involved. The original book
and thesis union remains the eventual task; this candidate still covers the
recorded Chapter 2 scope and its shared-list/import prerequisites only.

## Four consumer corrections

I read each affected proof and the relevant definitions in the pinned Mathlib
provider source. I independently compared all six import-prerequisite files
against fixed prerequisite base `70a1477d822efd4fdcec2007280f650bb4695eda`:
after removing only import-command lines, every remaining byte, including
newline structure, is identical. The two original narrowed FRP headers are
unchanged from the chapter's round-1 candidate.

| Finding | Consumer and added provider | Spec assessment |
| --- | --- | --- |
| IMPORT-VAL-001 | `Applications/FRP/Demand.lean`; `Mathlib.Order.SuccPred.Nat` | The existing `pending_registered` proof simplifies a successor comparison before using `le_rfl`. The provider imports the `[simp]` theorem `Order.lt_add_one_iff` and supplies `Nat.instSuccAddOrder`. The actual theorem still requires a registration at a strictly earlier transition; neither its statement nor witness was weakened. |
| IMPORT-VAL-002 | `Applications/FRP/Finite.lean`; `Mathlib.Data.Set.Finite.Lattice` | The existing `finiteHistory` proof calls `Set.Finite.biUnion` to combine a finite set of timestamps with finite occurrence-index sets. This is the module defining that operation. The independent finite-history interpretation, union index set and downstream bridge are unchanged. |
| IMPORT-VAL-003 | `Examples/FRP.lean`; `Mathlib.Algebra.Order.Archimedean.Real.Basic` | `ticks_finiteHistory` chooses a natural above a real timestamp with `exists_nat_gt`. The provider exposes the Archimedean API and `Real.instArchimedean`, which justify the existing natural bound. The example still permits an unbounded infinite future while proving every past finite; it does not replace that property with a bounded-event premise. |
| IMPORT-VAL-004 | `Examples/IndefiniteService.lean`; `Mathlib.Data.Nat.Size` | The provider defines exactly `Nat.size_pow : size (2 ^ n) = n + 1`. The preserved counterexample applies an alleged uniform size bound to `2 ^ bound`; this rewrite gives `bound + 1 ≤ bound`, contradicted by the existing arithmetic step. No finite-field/representation-size distinction or expected result was changed. The provider is statically correct; terminal checking remains pending. |

The first three changes are commits included by `c372c47`; the fourth is
`99a29dc`. Their limited role is to restore required mathematics to the import
environment. Identical source bodies alone do not certify elaborated kernel
artifacts, successful compilation, the complete dependency closure or a
performance improvement. The unchanged integrated validation must establish
the applicable compilation and audit claims.

## Full chapter coverage retained

The detailed mathematics and connected-use assessment remains in the complete
round-1 report. All of its examined source bytes are unchanged here:

- Generic stack operations and separate relational laws; independent List and
  custom-stack realizations; sufficient append fuel, exact primitive count,
  direct-list correspondence, observable empty failures and composed clients.
- Actual shared-list copying, retained old roots, untouched-tail identity,
  suffix order/closure/reachability/distinctness and the explicit linear space
  model. The all-integer update still follows decrement recursion, proves exact
  nonnegative execution equality and traverses to empty on negative indices.
- Ordered Mathlib tree values with independent whole-tree membership,
  all-descendant strict ordering, finite unique contents, baseline comparisons
  and the sharp valid skew-tree family. Generic set clients retain their laws.
- Actual shared baseline insertion with exact comparison/visit/cell counts,
  off-path root identity and the stronger matched-endpoint/descendant theorem.
- Candidate membership, duplicate abort and the combined physical insertion
  with one outer handler, identical original state on duplicates, zero cells
  and the comparison bound on that same combined execution.
- Complete and paired size-balanced shared constructors, unfolded-versus-cell
  size distinctions, exact counts, actual equal/reused child roots, recursive
  balance and the documented linear/logarithmic model-work qualifications.
- Key-only finite maps with arbitrary payloads, independent whole-tree meaning,
  overwrite and finite-domain laws, actual physical bind/lookup, preserved
  overwritten-endpoint children and nested optional observations.
- Existing square composition, connected nonvacuous examples, public import
  integration, contextual source dispositions and explicit separation from
  later lazy evaluation, trace/debit and whole-union obligations.

No import correction modifies the meanings, quantifiers, assumptions, cost
conventions, fuel-sufficiency proofs, physical identity claims or example
expectations assessed there. The source-policy/coverage/audit gates remain
necessary even though their source and entrypoints are unchanged.

## Retained findings

| ID | Current Spec disposition |
| --- | --- |
| CH02-PRE-001 | Static implementation closure remains verified: exact matched nonempty root, strict-ancestor cell count, old version and every descendant observation, with nonempty-child and failed-deeper-path examples. |
| CH02-PRE-002 | Static implementation closure remains verified: actual abort/combined traversals and a joint same-execution comparison/sharing result; exact original-state duplicate return and zero allocation. |
| CH02-PRE-003 | Static implementation closure remains verified: `WrittenAt`, endpoint child identity and the root-replacement case with two nonempty children. |
| CH02-PRE-004 | Static implementation closure remains verified: integrated baseline, optimized and map adapters with composed observation clients. |
| CH02-PRE-005 | **Open mandatory exact chapter validation gate.** Source integration and manifest consistency are established; full build/audit, success record and final verification for `99a29dc` are absent. |
| IMPORT-VAL-001..003 | Direct-provider repairs have matched focused compiler evidence. This does not establish the prerequisite's full gate or the chapter gate. |
| IMPORT-VAL-004 | **Pending terminal compiler verification.** The exact provider and unchanged proof have been inspected, but the attempted focused check did not reach a successful target completion. |

No new CH02-SPEC implementation finding is introduced. Historical reports and
failed/interrupted validation outcomes are retained; no disappearing diff or
source correction erases their evidence requirements.

## Validation evidence and limitations

I inspected the 1,134-job focused correction record
`../validation/import-footprint-r2-focused-r2.json`: terminal exit 0,
`inputs_unchanged: true`, and identical before/start/after maps. All 23 recorded
source/config hashes match the present chapter checkout. This supports the
first three provider repairs and their existing focused clients. It does not
cover the complete chapter or establish resolution of IMPORT-VAL-004.

The interruption records preserve the later limitations accurately:

- `runtime-interruption-20261102-2240.json` records disappearance of the old
  `324962e` full run without a terminal result. Its known `Nat.size_pow`
  compiler failure remains retained; the cause of runtime loss is unknown.
- `import-footprint-r3-focused-interruption-r1.json` records the separately
  owned `901f734` focused run as interrupted without a terminal record. The
  target did not complete; no target-success or compiler-failure conclusion
  is invented from its partial dependency progress.
- `import-footprint-r3-cache-copy.json` records 657 completed ordinary project
  outputs transferred for the corrected prerequisite check, with
  `approval_copied: false` and `acceptance: false`. This is cache preparation,
  not a substitute for validation or a transferred approval.
- `import-footprint-901f734-full-r1.json` identifies the root-owned stock full
  check of prerequisite candidate `901f734161920a76f3b399a575805b9a1d31e971`
  as running. That candidate is different from the chapter candidate.

At this review, `validation-chapter02-r3/.lake/verification.json` does not
exist. No exact full `99a29dc` build, exhaustive audit or final verification
result has been supplied. The earlier Chapter 2 focused-evidence qualifications
also remain: constructor and physical-map runs used the earlier observation
module, with the current added optional observer separately focused-checked.
None of these partial or older results is represented as an integrated pass.

I did not compile, signal a process, modify frozen inputs/build outputs, or
change any source, index, ref, dependency, requirement or gate. The only file
written by this continuation is this assigned report. Initial metadata-reading
used the older manifest key name and produced a read-only `KeyError`; the
subsequent inspection used the actual `files` schema and confirmed all 42
hashes. That failed metadata read is not counted as validation.

## Required continuation

Supply the exact chapter's successful stock `./check.sh --candidate HEAD`
terminal result, complete audit, matching `.lake/verification.json`, and
`./check.sh --verify-candidate HEAD` immediately before acceptance. Reconcile
the prerequisite gates independently. Reuse this static assessment only while
candidate, requirements, standards and relevant input identities match. Any
source revision requires both retained axes to reassess the complete revised
candidate against the original fixed chapter base.

**Final status:** base `82501d108f33c62d21b5e0d0f7d2376b902d8d49`;
candidate `99a29dcd02eb529fbefbb675e244a8c47b78cdef`; zero unresolved
implementation/source-coverage findings; no worst implementation severity;
IMPORT-VAL-004 terminal evidence and CH02-PRE-005 exact gate remain pending;
**Spec Blocked**.
