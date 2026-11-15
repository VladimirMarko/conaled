# Local 10023 — independent Standards review, round 1

**Outcome: Blocked, with one unresolved source finding and one required-validation blocker.**
Source findings: 1, High. Validation blockers: 1, High. This is not candidate
acceptance or a chapter-completion result.

Reviewer: `/root/signed_potential_review/standards`, 2026-11-03.

## Immutable scope and governing requirements

- Base and merge base: `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
- Candidate: `9c47a052ef96b528a85660d4c632704ca03144fe`.
- Diff: `git diff 5e048f781aa04be9ce993f1e7455bdc82df22bff...9c47a052ef96b528a85660d4c632704ca03144fe`.
- Commits: `6797860` (generalize signed potential accounting) and `9c47a05`
  (correct ordered-addition lemma sides). Six files, 527 insertions and
  23 deletions; no exclusions.
- Full requirements: `requirements/signed-potential.md`, version 1, SHA256
  `bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`,
  together with `requirements/REQUEST.md` and `requirements/REQUEST-union-v2.md`.
- Existing retained review record: `reviews/signed-potential.md`; no earlier
  independent Standards findings were recorded for this task.

The frozen source was read from the restored isolated `signed-potential`
checkout and compared with the pinned diff. Its HEAD remained the candidate
and its Git status remained clean. Root's
`validation/signed-potential-recovery-review-r1.json` pins all six changed-file
hashes. This review does not change the base, candidate, source, Git refs,
tracker, requirements, or historical evidence.

Applied candidate `AGENTS.md`, README development/build/audit requirements,
`docs/agents/architectural-quality.md`, domain guidance and glossary,
ADR0001 and ADR0010, relevant language-direction generality/specialization
criteria, the shared review procedure, `code-review` heuristics, and
`example-driven-development` with its worked example. No additional applicable
`CODING_STANDARDS.md`, `CONTRIBUTING.md`, or nested `AGENTS.md` was found for
these six files. The user's local-only tracking and no-GitHub-write instruction
overrides the normal tracker destination.

## Source finding

### SIGNED-POT-STD-CODE-001 — Fractional Real steps omit their noncomputable boundary

**Severity: High. Status: Unresolved.**

Candidate locations:

- `Examples/SignedPotential.lean:109–110`,
  `Examples.SignedPotential.FractionalSavings.step`.
- `Examples/SignedPotential.lean:139–140`,
  `Examples.SignedPotential.DebtSign.step`.

Both are ordinary `def` declarations containing Real division (`3 / 2`,
`1 / 2`, and `1 / 4`). The file has no enclosing noncomputable section and
neither declaration is marked `noncomputable`. At the exact pinned Mathlib
revision, Real inversion is noncomputable, as are its `Inv`, `DivInvMonoid`
and `Field` instances. These divisions therefore introduce a noncomputable
dependency into definitions for which Lean is asked to generate executable code.

This is a source-level compilation defect identified from the candidate and
its exact dependency provider. **No compiler diagnostic for these definitions
was observed in this recovered environment**, and none is fabricated here.
The preserved focused round 2 log does not reach a completed
`Examples.SignedPotential` target.

Primary provider inspected:
[Mathlib/Basic/Real/Basic.lean at the pinned revision](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Basic/Real/Basic.lean).
Its SHA256 is
`f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f`.
Relevant declarations are `inv'` at line 86, the `Inv` instance at line 113,
`instDivInvMonoid` at line 476, and `instField` at line 481. The fetched bytes
are temporary input at
`session/tools/signed-potential-standards-040/RealBasic.lean`, excluded from
checkpoint payloads under the established tool-input policy. The URL and hash
make the evidence reacquirable.

The applicable standards are README's required successful integrated build
and explicit proof/execution boundary, ADR0001's allowance for noncomputable
mathematical specifications with separate executable realizations, and the
example-driven-development requirement that retained cases compile through
their public connections. This is not a request to weaken the theorem
statements or change the independently fixed fractional expectations.

**Required correction:** mark these two mathematical step definitions
`noncomputable def`, or supply a genuinely computable and mathematically equal
construction. The minimal annotations preserve the existing terms, public
statements, expected values, and proof obligations. Then run the affected
focused closure and mandatory full candidate gate. This finding must be
reviewed on the corrected immutable candidate; a textual annotation alone
cannot supply the missing compiler evidence.

The finding does not call for making the whole resource library noncomputable.
The same pinned Real provider explicitly retains computable ring/additive
instances. `PotentialTransport.Counter.realStep` only casts Nat observations
through that additive structure, so no analogous division defect was identified
there.

## Required-validation blocker

### SIGNED-POT-STD-VAL-001 — Exact-candidate build, proof audit and final verification are unavailable

**Severity: High. Status: Unresolved; outcome blocked.**

The source and handoff do not establish a successful complete focused run for
this candidate, its own isolated stock `./check.sh --candidate HEAD`, exhaustive
axiom audit, matching `.lake/verification.json`, or immediate final
`./check.sh --verify-candidate HEAD`. Those are mandatory under the README,
review procedure and requirements' completion section. Approval of an earlier
candidate or a subset of targets would not discharge them.

Evidence was checked directly:

| Record | Observed status and permitted interpretation |
| --- | --- |
| `validation/signed-potential-r1.json` and `.log` | Frozen predecessor `6797860` ended with exit code 1. Its three ordered-addition proof repairs are present in `9c47a05`; the failed run is preserved. |
| `validation/checkpoint039-progress/signed-potential-r2.json` | Records candidate `9c47a05` and status `running`, without terminal exit code, end time or final-input comparison. It is not a complete success record. |
| Corresponding partial round 2 log | Reports built Potential, SignedPotential, BinaryCounter, SymmetricCosts, BinaryCounter.Decrement, RandomAccess.End and SymmetricWorkload targets. It does not establish completion of the two new example modules, FIFO closure, all requested targets, or any whole-project gate/audit. |
| `validation/recovery-040-interruptions.json` | Preserves both original partial records unchanged and records unknown terminal outcomes after recovery. |
| `environment/recovery-040.md` and `environment/recovery-040-approval.json` | No restored Nix/Lean environment or supported namespace route is available; the explicit standard `/nix` creation request was rejected before execution. |

Round 1 record SHA256:
`c0a823bace74f6085c460421d6a686fe31339184b6b28fc10101da9db82aa2b2`.
Round 1 log SHA256:
`47879b0c2e4e967c13470b97e11ab86995db7f6b42bbba52575d346c8cc766ff`.
Round 2 partial record SHA256:
`c78596d7f9beefecc773ad5405f7992cef8153d7af4e2e53edbf37e7682eefec`.
Round 2 partial log SHA256:
`3f59d2aa6cad01d8f884c1ae98361e8a1078b60da39c522343c98c79eaa41d17`.

**Required resolution:** restore the unchanged pinned Nix environment, retain
frozen inputs and existing concurrency rules, validate the corrected candidate's
affected closure, then perform its own full candidate check/audit and retain
the verification record. Reconcile that exact evidence in both retained review
axes and run final stock candidate verification immediately before acceptance.
The earlier integration-predecessor gates and chapter order also remain open;
this bounded review cannot approve them.

## Remaining standards assessment

No additional source/prose standard violation was identified in the inspected
scope. This assessment is subordinate to both unresolved findings above.

### Architecture and preserved use

The candidate generalizes the existing `budget` and potential lemmas in place,
reuses `Measured`, `run`, and `reweight_run`, and introduces no second executor,
parallel hierarchy, new source language, or record that assumes the desired
whole-run conclusion. Budget accumulation follows actual first projections,
with separate universes/types for observations and charges. The exact telescope
requires an additive monoid without commutativity, cancellation or order. The
inequality theorem adds a preorder and monotone addition on both sides. The
cost-only theorem states nonnegativity of the actual final potential explicitly.

The signed formulas require only `Add`/`Sub` for their definitions and an
additive commutative group for their balance laws. The debt theorem is derived
from the savings theorem at negative potential, retaining both boundary terms;
it does not duplicate execution induction. The two small budget transport
lemmas serve the concrete counter client and do not create an unused transport
framework. Additivity and order-preserving transport remain separate.

Old Nat convenience statements and explicit argument order are retained.
Unchanged BinaryCounter, SymmetricCosts, RandomAccess.End and FIFOContracts
uses were inspected, including their retained example consumers. No semantic
weakening or source incompatibility was identified by inspection. The unused
observation zero in `FIFOContracts.abstractBudget` still needs actual
elaboration coverage after budget codomains are decoupled; the author report
correctly reserves a type-only annotation for an actual diagnostic. This is
part of the validation blocker, not a demonstrated additional defect.

### Examples and statement-review methodology

The full author reports preserve independently fixed expectations, distinguish
an absent public connection from an artificial numerical failure, and retain
the original failed round and exact proof-only repairs. The source examples
use the public laws rather than merely compute detached arithmetic:

- Int charges 4 and -2, the positive prefix, and the nonzero-initial suffix use
  `run_potentialCharge_exact` with actual run observations.
- The cost-1/negative-final-potential example uses that exact law to refute the
  cost-only conclusion and explicitly falsifies its nonnegative-terminal premise.
- Fractional Real savings and opposite-sign debt examples use the same public
  group theorems; their mathematical expectations remain intact despite CODE-001.
- The existing binary increment is lifted through an additive observation map;
  `reweight_run`, `budget_map`, and `budget_congr_state` retain its state,
  measured write count and trajectory. Its local law feeds the generic telescope.
- Ordered words distinguish concatenation order without a commutative instance.
  Independently typed Nat observations and word charges exercise intermediate
  states through `budget_append`.

Hypotheses are local and established for the actual examples; no source
derivation was found to assume its own target whole-run result. Empty behavior,
sign conventions, final-potential direction and initial boundaries were inspected.
This is source-level statement review, not a substitute for Lean elaboration
or the exhaustive audit.

### Imports, scope and integration

Changed core imports name concrete algebraic providers and do not introduce
Real analysis, logarithms or tactic umbrellas into the generic resource core.
The example modules use named Real/cast/free-monoid providers and specific
arithmetic tactics. The two new public-entrypoint imports reach both new
clients and the signed core; the existing Lake globs retain them in integrated
coverage. No build tool, pin, proof-budget setting, source-policy guard,
axiom-audit rule or linter suppression is changed. No admission, application
axiom or native/unsafe proof shortcut was found in the candidate diff.

API documentation distinguishes algebraic debt identities from shared consumable
credit, work/forcing correspondence, payment chronology and actual-runtime
bounds. It retains the outstanding chapter/algorithm obligations. Module layout,
ordinary Lean interfaces and Conventional Commit messages follow the applicable
standards. `git diff --check` reported no whitespace errors. No compiler,
build, policy scanner, audit, candidate verifier, runtime test or remote write
was run by this reviewer.

## Handoff

Review base: `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
Reviewed candidate: `9c47a052ef96b528a85660d4c632704ca03144fe`.
**Standards outcome: Blocked; 1 unresolved High source finding and 1 unresolved
High validation blocker.** Preserve both IDs across the minimal correction and
its full-scope re-review. No formal or chapter acceptance is granted.
