# Local 10023 — independent Standards review, round 2

**Outcome: Blocked. No unresolved source/prose findings; one High
required-validation blocker remains.** The round 1 noncomputable-boundary
finding is fixed by source review on this candidate. No compiler, proof-audit,
candidate acceptance or chapter-completion result is asserted.

Reviewer: `/root/signed_potential_review/standards`, 2026-11-03.

## Fixed scope and review reuse

- Fixed base and merge base:
  `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
- Corrected candidate: `d24c443ba22019613b1ce646d6eed7279c791ad6`.
- Previous candidate: `9c47a052ef96b528a85660d4c632704ca03144fe`.
- Full review diff: `git diff 5e048f781aa04be9ce993f1e7455bdc82df22bff...d24c443ba22019613b1ce646d6eed7279c791ad6`.
- Full scope: the same six files, three commits (`6797860`, `9c47a05`,
  `d24c443`), 527 insertions and 23 deletions; no exclusions.
- Requirements remain `requirements/signed-potential.md`, version 1, SHA256
  `bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`,
  with the same `REQUEST.md` and `REQUEST-union-v2.md` governing scope.

This continues the same review loop and finding IDs. The full round 1 report
`reviews/signed-potential-standards-r1.md` is preserved byte-for-byte with SHA256
`a629a56cd96e248d070c655881a5fd2fc95b5f263e4abf7c5dfa299bf577dd61`.
Its complete standards and unchanged-source analysis are reused under
`docs/agents/review-loop.md`'s reuse rules; its blocked outcome is not converted
to approval.

I inspected the exact correction, root's implementation/statement-review report
`research/signed-potential-noncomputable-correction-r1.md`, preserved patch
`validation/signed-potential-noncomputable-correction.patch`, and complete
candidate manifest `validation/signed-potential-recovery-review-r2.json`.
Independent Git/object comparisons confirmed that five source files are
byte-identical to round 1, the sixth differs only by the two qualifiers below,
all six live files match the corrected commit, the base is still the merge base,
and the isolated checkout is clean at `d24c443`.

| File | SHA256 at corrected candidate | Review disposition |
| --- | --- | --- |
| `Applications/Resources/Potential.lean` | `690b48d41dc0b4b21a62e29d1a67c8b0494b3a0ca9de378e07cca82f415f961e` | Byte-identical; complete round 1 analysis reused. |
| `Applications/Resources/SignedPotential.lean` | `c839b1e32b3182c5789d05934ea253139d91c338917c1207616fe0043b0ce222` | Byte-identical; complete round 1 analysis reused. |
| `Examples/PotentialTransport.lean` | `5fa86b8dec422ca73c6a8c4853a6a2719b2f3892c0bac57b6a58becb18dd3c7c` | Byte-identical; complete round 1 analysis reused. |
| `Examples/SignedPotential.lean` | `745400e50b758413a9087c64a9a9fe99a268236afb46618be02ecd5d82c034fc` | Two qualifiers inspected; all other text byte-preserved. |
| `SquareApplications.lean` | `d5f96d925f272187870e3831a33d2f2ee544ddabb149978fbe9ef65dbd8bb581` | Byte-identical; integration analysis reused. |
| `docs/research/pfds-signed-potential.md` | `e7ebb2dd51fec8706a0bba38da9e9a6c0a2eb3aa3a688c5b80a66e6f7cb8dfe5` | Byte-identical; scope/boundary analysis reused. |

The applicable AGENTS, README, architectural/domain guidance, glossary,
ADRs, language-direction criteria, example-driven-development guidance and
review heuristics are unchanged. Toolchain, dependency pins and validation
tools are also unchanged. No refreshed semantic requirement or standards
exception was introduced.

## Findings retained and reassessed

### SIGNED-POT-STD-CODE-001 — Fixed with source-review evidence

Original severity: **High**. Corrected candidate locations remain
`Examples/SignedPotential.lean:109–110` and `:139–140`.

Both actual declarations now explicitly state their noncomputable boundary:

- `Examples.SignedPotential.FractionalSavings.step` is `noncomputable def`.
- `Examples.SignedPotential.DebtSign.step` is `noncomputable def`.

The exact `9c47a05` to `d24c443` diff contains no other change. This is the
minimal correction requested in round 1 for the Real division operations.
The pinned Real provider inspected in round 1 remains SHA256
`f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f` at
[the exact Mathlib revision](https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Basic/Real/Basic.lean).
Its noncomputable inverse/division instances justify these annotations;
its separate computable additive/ring paths do not justify marking the whole
resource library or the Nat-cast counter client noncomputable.

Types, bodies, namespace names, quantifier scope, theorem statements, proofs,
and independently fixed observations are preserved. Fractional savings still
uses modeled half-unit costs, potentials 0, 3/2, 0, charges 2 and -1, and total
1. The debt case still distinguishes savings charge 3/4 from debt charge 1/4
for complete cost 1/2 and terminal debt 1/4. Both remain connected through the
same public group identities and the actual final-potential condition. The
annotation adds no axiom, admission, stronger mathematical hypothesis, altered
expected value, proof-budget setting or audit exception.

The source defect is therefore **fixed at the declaration boundary**. This
disposition verifies the requested correction; it does not assert that the
complete module now elaborates or compiles. All required compilation and
integration evidence remains explicitly open under SIGNED-POT-STD-VAL-001.

### SIGNED-POT-STD-VAL-001 — Unresolved

Severity: **High**. Outcome: **Blocked**.

No new Lean compiler, focused build, stock full candidate check, exhaustive
axiom audit or final candidate verifier has run for `d24c443`. Root's recorded
`git diff --check` exit zero is only a source-format check. It is not formal
validation. The preserved earlier partial focused run targeted `9c47a05`,
not this corrected candidate; in addition to lacking a terminal result, it
cannot certify the subsequently changed example file.

The required evidence remains:

1. A terminal successful frozen focused run covering the eleven recorded
   core/client targets, including both new examples and the existing FIFO and
   potential-accounting consumers, with matching input evidence.
2. This exact corrected candidate's own isolated pinned-Nix stock
   `./check.sh --candidate HEAD`, complete project build and exhaustive audit,
   and matching `.lake/verification.json`.
3. Reconciliation by the retained Standards and Spec reviewers on that exact
   candidate and evidence, followed by immediate stock
   `./check.sh --verify-candidate HEAD` before acceptance.

`validation/recovery-040-interruptions.json` preserves the old runs' unknown
terminal outcomes. `environment/recovery-040.md` and
`environment/recovery-040-approval.json` retain the unavailable Nix/namespace
environment and rejected standard-store creation request. No permitted working
replacement environment or successful gate is supplied by the correction.
The predecessor integration gates and chapter order also remain in force.

## Full-scope conclusion

The same complete architecture and statement review from round 1 continues
to apply to the five byte-identical files and all unchanged portions of the
corrected example file. The candidate still generalizes the existing budget
and telescope with the stated minimal additive/order assumptions, preserves
Nat client interfaces, uses ordinary additive maps and the original measured
counter, retains order-sensitive and independent-codomain examples, and keeps
algebraic debt identities separate from persistent work/forcing claims.
The correction resolves the only identified source issue without changing
those properties or introducing a new source/prose standards violation.

This reviewer made no code, Git, tracker, shared-record or historical-report
changes and ran no compiler or formal gate. Only this new independent report
was written. The source finding closure must not be presented as Lean
validation or candidate acceptance.

**Base:** `5e048f781aa04be9ce993f1e7455bdc82df22bff`.
**Reviewed candidate:** `d24c443ba22019613b1ce646d6eed7279c791ad6`.
**Standards outcome: Blocked; 0 unresolved source/prose findings, 1 unresolved
High validation blocker.**
