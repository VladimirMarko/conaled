# Chapter 1 repair compiler findings and correction candidate

Recorded 2026-11-02 within the existing Chapter 1 loop. Full review base remains
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; original requirements, frozen
cost-model addendum and all retained Spec findings remain unchanged.

## Actual focused result

Candidate `a14977b9e316cc484ffad8a470d26b15615956c0` was clean throughout
focused attempt 1 in `conaled-ch01-review`. It ran from 16:02:01 to 16:08:38 UTC
under the pinned Nix environment with `LEAN_NUM_THREADS=1`:

```
lake --no-cache --rehash build Applications.Resources.CallComparison Applications.Resources.SharedDemand Examples.CallModels Examples.SharedDemand
```

The command exited **1**. The complete 11,375-byte log is
`chapter01-cost-models-focused-attempt1.log`, SHA-256
`71296de0b8e34fa0aa971935bfbedd6ef7f3ebf92edd2f06991b526c96223eec`.
Exact start/end source identity and result are in the matching provenance JSON.
`Applications.Resources.SharedDemand` compiled successfully. The failures were
in CallComparison and the SharedDemand examples; CallModels receives no
successful compilation credit from the reported dependent target.

These are ordinary elaboration/linter failures, distinct from the earlier
ENOSPC event. They do not establish a Lake integrity defect. No full guarded
repair build, exhaustive audit, final review or acceptance has passed.

## C1-ELAB-001 — Preserve natural casts through norm simplification

At CallComparison lines 110 and 117, unrestricted `simpa` expanded the cast of
`T x + 1` into real addition inside a norm. The cast natural inequality then
did not match the remaining absolute-value expression. The mathematical
nonnegative count comparisons and positivity premise are unchanged.

The correction uses `Real.norm_natCast` before expanding the count and only
the required multiplication/cast or `one_mul` simplifications. Both proofs
still consume the original natural inequalities, with constants two and one.
No premise, quantified domain or theorem statement is changed.

Status: implemented and source-read; compiler confirmation pending on the new
candidate. Original failing source remains in commit a14977b and the exact
diagnostics remain in the complete log.

## C1-ELAB-002 — Explicit example unfolding and resource names

The unused-work and repeated-prefix bridges at SharedDemand example lines 57
and 83 need the ordinary `empty` and private `catalogue` definitions unfolded
explicitly. The duplication proofs' unqualified `bind` and `pure` simp
arguments were ambiguous with standard typeclass operations, leaving
unsimplified expressions and consequent omega/unused-simp diagnostics.
An unnecessary `<;>` also triggered the unused-tactic linter.

The correction unfolds the two named definitions in their existing bridges,
qualifies `Resources.bind` and `Resources.pure` in proof scripts, and uses
sequential `congr 1` / `omega` where only one value goal remains. The unshared
two-goal proof retains its distribution. No linter or warning policy is disabled.
All definitions, statements, hypotheses and connected cases remain unchanged.

Status: implemented and source-read by the contributor and root; compiler
confirmation pending on the new candidate. Original source and diagnostics
remain available, including the secondary failures caused by the ambiguity.

## Committed correction and statement review

Correction candidate: `057e07cd0bd16c7877967aedc46aeefaca01a7a6`.
Parent: `a14977b9e316cc484ffad8a470d26b15615956c0`.
Commit: `fix(resources): resolve FDSA cost proof elaboration (#174)`.
Development branch: `work/fdsa-basics-cost-models`, clean after commit.
Two changed paths, 13 insertions and 9 deletions. Complete unstaged and staged
whitespace checks passed before commit; root read the complete combined diff.

| Path | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| Applications/Resources/CallComparison.lean | 5498 | 123 | 8d6d9324aa9dc71ceeaeaa04073f0f2a4f721a309995f0b623650bb19f01b520 |
| Examples/SharedDemand.lean | 7897 | 189 | 35bdb94053c0fd065f0a62b0bc6da1ef98be4919f7d6a37c62da65fb7e1fe47c |

Statement review: this patch changes only proof scripts. Natural-count norms,
the original eventual-positivity qualification, actual cache/value observations,
and both shared/unshared computations retain exactly their previous statements
and definitions. It introduces no new axiom, admission, shortcut, assumption,
tariff or source-coverage interpretation. This author-side assessment does not
replace either retained independent final review axis.

At 16:15:12 UTC the idle isolated validation checkout was switched cleanly to
057e07c; the transition is saved in
`../provenance/chapter01-repair-correction-start.json`. The same four-target
focused retry and the complete guarded candidate gate remain pending.
Both final axes must still review the full 14-path scope from the original
base, including these corrections and all original findings, then final
candidate verification must match. Neither compiler finding is closed by
this source-only correction record.

## Second focused result and further proof-only corrections

Focused attempt 2 at clean candidate `057e07cd0bd16c7877967aedc46aeefaca01a7a6`
ran from 16:19:31 to 16:25:34 UTC and exited **1**. Exact metadata is in
`../provenance/chapter01-cost-models-focused-attempt2.json`. Its complete log
has 7,172 bytes and SHA-256
`d4e90060c9d214920ba0394802050838f15526e3e410101fe13dfd0d28b314f2`.
CallComparison compiled successfully, providing focused compiler confirmation
of C1-ELAB-001. The unchanged SharedDemand core was reused successfully.
No whole-candidate validation or final-review approval follows from that result.

C1-ELAB-002 retained one failure at SharedDemand example line 83: the restricted
simplifier did not reduce the catalogue's Boolean condition and first projection.
Commit `94d9af50df283dee3a314025a8c24859445b5793` removes `only` from that existing
`simpa`, allowing the ordinary Boolean/if/projection simplifications. The same
`request_stores` public theorem remains the case's connection. No other errors in that module were reported in the second attempt; the module
as a whole did not compile successfully. The contributor and root read this one-line correction.

### C1-ELAB-003 — Remove redundant example proof syntax

The first actual CallModels compilation in attempt 2 reported two linter errors:
line 42 used `<;>` where the simplifier leaves only one goal, and line 101 supplied
an unused `Nat.mul_mod` simp argument. Commit
`503081dccdbe64188eceb6524724fc445c840d68` makes `simp` then `omega` sequential
and removes only that unused argument. Root read the exact diff. No linter,
warning policy, import, mathematical statement, premise or expected case changes.

Both local commits passed staged/unstaged whitespace checks and left the
worktree clean. They descend from 057e07c without changing prior history.
Current correction candidate: **503081dccdbe64188eceb6524724fc445c840d68**.

| Path | Bytes | Lines | SHA-256 |
| --- | ---: | ---: | --- |
| Applications/Resources/CallComparison.lean | 5498 | 123 | 8d6d9324aa9dc71ceeaeaa04073f0f2a4f721a309995f0b623650bb19f01b520 |
| Examples/SharedDemand.lean | 7892 | 189 | 690df2fa9ac3a16a8f6763589987cee2241447fa6292f3792b12a7c28edbc2be |
| Examples/CallModels.lean | 4188 | 105 | c1d13360a1229f21bf749d7e7db463eaf9d094089d6c2aa7c92171540e5616ac |

The idle isolated checkout was switched cleanly from 057e07c to 503081d;
`../provenance/chapter01-repair-example-correction-start.json` records the
transition. Focused attempt 3 uses the same four targets and pinned environment.
C1-ELAB-002/003 await that compiler result; all findings retain final-review
confirmation as applicable. Original review base, full 14-path scope, frozen
requirements and SPEC-001/002/003/V001 remain unchanged and open.

## Final focused confirmation at 07e480f

Focused attempt 3 at clean 503081d exited 1 at 16:30:51 UTC. Its 5,116-byte log
has SHA-256 `98ecbe0090279c14f8a6d40b8ec1092b6d77a7d4e4259bb135af65f7a8b4971a`.
Examples.CallModels compiled successfully, confirming C1-ELAB-003 at the focused
level. The only reported failure was `unnecessarySimpa` at the cache example:
the existing simplifier invocation already closed its goal.

Commit `07e480f6ec9958d4975bb90151005b84f2907614` follows the compiler's instruction
to use `simp` and removes the now-redundant supplied proof term. The arbitrary
request-prefix case still consumes the public `request_hit`,
`run_preserves_cached` and `request_miss` laws, retaining the actual cache and
returned value. Its independently stated result is unchanged. No definition,
statement, assumption, expected result, import or warning policy changed.
The complete one-file diff and staged/unstaged whitespace checks were reviewed;
the development worktree was clean after commit.

Final Examples/SharedDemand.lean: 7844 bytes, 188 lines,
SHA-256 `5b0e374c3d57a9a681d49b9ae0b1bff41a6f60490efadc79cd2d3432b7737fc9`. The other two corrected-file
identities remain as recorded for 503081d.

Focused attempt 4 at clean **07e480f6ec9958d4975bb90151005b84f2907614**
ran from 2026-11-02T16:31:17.922975+00:00 to 2026-11-02T16:31:33.989321+00:00 and exited **0**.
All four required focused targets completed successfully under the same pinned
Nix/Lean environment with LEAN_NUM_THREADS=1. Its complete log has
3394 bytes and SHA-256 `06cfb75ecf8a74fe25f48f3869cefe6359ab5d2ac4bad92c8beff0adc0e99ae9`;
exact start/end identity and command are in
`../provenance/chapter01-cost-models-focused-attempt4.json`.

C1-ELAB-001/002/003 now have focused compiler confirmation. This is not full
candidate acceptance: source policy/coverage, guarded full build, post-build
integrity, exhaustive audit, both retained final review axes and immediate
candidate-record verification remain. Original base, full 14-path scope,
requirements and SPEC-001/002/003/V001 are unchanged and open.
