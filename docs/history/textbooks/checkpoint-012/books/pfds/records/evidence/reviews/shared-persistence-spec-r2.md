# Shared persistence — independent Spec review, round 2

Date: 2026-11-02.
Reviewer: `/root/architecture_inventory/chapter01_spec`.

## Scope and outcome

- Fixed base/merge base: `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Previous candidate: `ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Clean isolated checkout: `/workspace/scratch/ca9a61d0bf30/validation-persistence`.
- Full scope: `git diff BASE...CANDIDATE`, same eight files, 939 additions,
  commits `ad73001` and `70a1477`; no exclusions.
- Requirements unchanged: original `REQUEST.md` and `shared-persistence.md` v2.
- **Spec outcome: Blocked pending full exact-candidate validation.**
- Static implementation findings: **zero**.

## Full-scope review and correction

The previous candidate's full mathematical statement review is preserved in
`shared-persistence-spec-r1.md`. I reassessed this candidate against the same
requirements, inspected the candidate-to-candidate diff and the affected
`updateSquare` proof, and confirmed that the other seven files are unchanged.
The complete fixed-base scope remains under review; this is not approval of
only the one-line correction.

The only source correction removes an unused `change` tactic from the successful
update branch. The theorem type, operator, partial value specification,
representation relation, hypotheses and proof dependencies are unchanged.
The proof still invokes `updateRun_success`, rewrites the actual result,
unfolds the option interpretation and discharges the represented-value goal.
The failure branch and its explicit failure theorem are unchanged. Removing
the unused tactic addresses a fatal linter gate, not a semantic discrepancy.

Prior analysis therefore continues to support every unchanged family:
fresh allocation and arbitrary old-root preservation; satisfiable list
interpretations and frontier-derived fuel; actual link-following append and
update with exact prefix-copy counts; explicit out-of-range/malformed traversal
failure; suffix value order, actual-tail chains, reachable-address coverage and
non-null distinctness; modeled linear counts; and ordinary relational-square
clients with connected positive and negative examples. No new Spec finding
or unresolved implementation finding was identified.

The earlier suffix-space counterexample remains meaningful and its correction
remains present. A count of suffix values or distinct roots alone is not being
treated as graph-space evidence; the actual-tail and closure/reachability
theorems supply the missing connection. Abstract cell/visit counts still make
no claim about Lean runtime allocation, physical latency, reclamation or
arbitrary branching amortization.

## Validation evidence and remaining gate

I observed the isolated checkout at the supplied candidate SHA with an empty
porcelain status. The focused log `persistence-focused-r2.log` ends with a
successful 664-job build and explicitly records compilation of the corrected
Observation module and `Examples.SharedList`. The log identifies the live
implementation checkout as dirty during that focused run, so it is useful
development evidence rather than a substitute for clean isolated candidate
acceptance. The coordinator also reports prior focused compilation of the
other added modules.

The first full check of `ad73001` was intentionally interrupted for resource
sequencing and supplies no success record. The new isolated Nix command
`env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD` is running for `70a1477`,
with log `session/validation/persistence-70a1477-check.log`. Full compilation,
the exhaustive axiom audit, the exact-candidate verification record and final
`./check.sh --verify-candidate HEAD` have not yet been supplied to this review.

I did not compile, mutate the candidate or treat the focused build as full
acceptance. Those remaining validation gates prevent this axis from passing.
They do not create a speculative mathematical finding.

## Result

**Spec: Blocked on validation; zero implementation findings.**
This result concerns cross-cutting ticket 10013 only. Chapter source-coverage
and acceptance gates remain independent and unresolved.

Base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; candidate
`70a1477d822efd4fdcec2007280f650bb4695eda`.
