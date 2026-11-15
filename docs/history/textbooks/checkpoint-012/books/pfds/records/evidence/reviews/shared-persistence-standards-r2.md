# Shared persistence prerequisite — Standards review, round 2

Outcome: **Blocked pending required integration validation**.
Unresolved code/prose findings: **0**. No chapter acceptance is implied.

## Pinned full scope

- Local ticket: #10013; requirements remain `REQUEST.md` and
  `shared-persistence.md` version 2.
- Fixed base and confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/validation-persistence`.
- Full diff: `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...70a1477d822efd4fdcec2007280f650bb4695eda`.
- Commits: `ad73001` and `70a1477`.
- The same eight files as round 1 are in scope, now with 939 added lines;
  no exclusions. Observed HEAD equals candidate and working-tree status is clean.

This is a full-scope review against the stable base. The prior report's
architectural, statement and connected-case analysis is retained for unchanged
content; this is not reuse of approval, since round 1 never passed validation.
The reviewer confirmed that the entire candidate delta from round 1 is the
single proof-script correction below and reread the complete affected adapter
module. Applicable standards, requirements and other code remain unchanged.

## Compiler-discovered correction

The first candidate contained an unused `change (optionalRepresentation α).Rel _ _`
in the success branch of `SharedList.Observation.updateSquare`. The compiler's
`unusedTactic` lint was fatal under `warningAsError`. This was a real mandatory
validation failure, not a semantic counterexample, and the earlier static
review did not claim to have established compilation.

Commit `70a1477` removes only that success-branch tactic. The failure-branch
`change` remains. The theorem statement, operation definitions, success/failure
specification, proof hypotheses and public consumers are unchanged. The proof
still uses `updateRun_success`, rewrites the actual returned result and reduces
the optional representation to the proved list relation. No mathematical
assumption was added or weakened to repair the lint failure.

The focused build log now records compilation of the corrected adapter and
`Examples.SharedList`, ending in `Build completed successfully (664 jobs).`
The root reports terminal exit 0 and successful focused compilation of all new
modules. This is adequate evidence that the specific fatal lint failure is
fixed; it is not the required integrated acceptance result.

## Full-scope Standards outcome

The round-1 conclusions remain supported for the current candidate:

- Existing fresh-write, measured-result and relational composition interfaces
  are reused without a competing abstraction hierarchy.
- Representation validity, list observation, roots, modeled allocations and
  structural visit counts remain separate.
- Actual root traversals establish append/update sharing; public fuel is proved
  sufficient on represented finite inputs.
- Partial-operation failure is preserved; untraversed raw roots are not
  silently claimed to be validated.
- Suffix storage interpretation uses actual-tail closure, independent graph
  reachability and duplicate-free root enumeration. The counterexample to
  value-only sharing inference is retained.
- Checked applications use the public theorems and construct their validity
  premises; resource bounds are explicit model-level claims.
- All new modules remain included through `SquareApplications`; no source,
  theorem, runtime or whole-chapter claim was broadened.

No new Standards finding was identified. The compiler-discovered issue has
been corrected and is recorded above rather than misclassified as a semantic
defect. There are no unresolved prior Standards code/prose findings.

## Required validation remains open

- The old candidate's full check was intentionally interrupted. It produced
  no complete build/audit success and supplies no candidate acceptance record.
- The new exact-candidate Nix command is running:
  `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`.
- Current full-check log:
  `session/validation/persistence-70a1477-check.log`.
- Focused-build log:
  `session/validation/persistence-focused-r2.log`.

At review time the new full log showed ongoing successful compilation but no
completed integrated audit. A pass still requires successful full completion,
the matching `.lake/verification.json`, and immediate final
`./check.sh --verify-candidate HEAD` evidence for this exact candidate. The
reviewer did not compile, mutate source or start a competing validation process.

## Result

Base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; candidate
`70a1477d822efd4fdcec2007280f650bb4695eda`.

**Standards: Blocked pending exact-candidate integrated build, exhaustive proof
audit and final verification; 0 unresolved code/prose findings.** The focused
build fixes the known lint failure but does not close the integration gate.
