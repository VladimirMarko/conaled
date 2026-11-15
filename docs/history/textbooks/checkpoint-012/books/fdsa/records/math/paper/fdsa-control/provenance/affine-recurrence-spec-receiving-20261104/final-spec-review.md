# XR01 final independent Spec review — receiving candidate c1cefe45

**Current outcome: PASS for the Spec axis, with zero unresolved findings, at `c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5` (tree `b62fe504a38948e61c6377a4e7661b639c28c08c`).** This is the final continuation of the original XR01 review. It supersedes the dated Blocked/pending dispositions only for this exact candidate and evidence; all earlier reports, source assessments and failed attempts remain unchanged. This report does not perform integration or claim Chapter 3 acceptance. The root still owns the other final axis, immediate candidate verification and exact accepted-branch update.

## Fixed scope and retained source assessment

The original review base is `c28ba71863d2a35ee1c3a089caa90464e4cca692`, and the original draft is `d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2`. The receiving integration base is accepted Chapter 2 `2da5708478a1d943a9214b5b386ec2db16cd9eca`. The actual receiving lineage is Q → `4df3bc95b96342250c9b3ff946773449e308e11b` → this exact candidate, with the isolated original change incorporated by cherry-pick and then the recorded one-byte syntax correction. This is not an assertion that the original draft is a merge ancestor.

The complete frozen requirements remain `reviews/affine-recurrence-requirements.md`, SHA-256 `5873700a349c359d15873829f1399a20225fa80eaa980e7ad9f1e4c8f774dd02`. All five original paths remain in scope: the resource theorem, its complete example module, `SquareApplications.lean`, the affine recurrence note and the reconstruction map. The complete explicit authored surface is **21 public names: 19 theorems and two definitions**, with no authored private names, anonymous examples or new instances. Generated declarations remain covered by the full audit; their counts are not substituted for the explicit name inventory.

The full original mathematical/source review and pinned book-method correspondence are retained through the exact identities in `reviews/affine-recurrence-spec-preparation-20261104.md` and its `source-assessment.json`. The complete receiving source and documentation assessment is retained through `reviews/affine-recurrence-spec-receiving-20261104.md`, `source-and-prepared21-assessment.json`, `source-reconciliation.json` and `source-readback-and-hold.json` in this directory. All five receiving paths, all 21 authored headers, the exact root/map/note changes and the applicable instructions were already independently assessed. None of those assessments is replaced by a narrower compiler-only review.

In particular, the core is exactly the original draft's core; the only example-source change is the recorded removal of the space immediately after the opening absolute-value bar at the integer example. The accepted Q root is preserved with the one additional `Examples.AffineRecurrence` import; no XP01 implementation is imported. The map retains the accepted Q content plus XR and the exact historical Chapter 1 qualifier, and the note uses dated preparation/evidence wording. The prior reconciliation established 1,655 other Q paths unchanged. No current snapshot of unrelated author branches is part of this final review.

## Mathematical and actual-type assessment

Every complete type printed by the actual qualified run was read directly: **all 294 native lines, all 17,154 bytes and all 21 ordered blocks**, without omissions, diagnostics, filtering or a header-only shortcut. The output, exact block hashes and individual semantic dispositions are in `actual21-complete-type-assessment.json`. The actual statements preserve the following complete scope.

| Actual positions | Statements and assessment |
|---|---|
| 1 | The universe-polymorphic two-branch theorem has exactly `CommRing`, `LinearOrder`, `IsStrictOrderedRing` and `Archimedean` assumptions. Arbitrary signed `f`, `rho`, `K`, `C`, `D`, natural branch maps and cutoff are quantified before the premises. `rho < 1`, the eventual sum-of-branch-sizes inequality and the eventual recurrence inequality imply nonnegative affine coefficients bounding **every** natural input. There is no hidden field, nonnegative-`f` premise, supplied prefix bound, child-decrease assumption or uniformity across an extra parameter. |
| 2–4 | The actual natural `quarter` function and its two equations retain the base region `n ≤ 1` and the positive branch `n > 1`, with natural division by four and `2 * quarter (n / 4) + n + 1`. The definition's body, termination and connection to these equations remain covered by the retained source review and current full validation. |
| 5–10 | All six actual values remain `quarter 0 = 1`, `quarter 1 = 1`, `quarter 2 = 5`, `quarter 4 = 7`, `quarter 8 = 19` and `quarter 16 = 31`. |
| 11 | The rational affine bound is on the cast **actual quarter function**, with nonnegative rational coefficients and every natural input; it is not an unrelated assumed recurrence. |
| 12–16 | The signed client is `Nat → Int`, has base value −1, is nonpositive, satisfies the exact recurrence with two `signed 0` children and coefficient −1, and receives a nonnegative-coefficient affine upper bound over integers. This retains the signed, non-field client rather than silently specializing the core to a field or nonnegative costs. |
| 17–18 | The generic negative-square upper bound requires no Archimedean or field instance. The corrected concrete statement actually elaborates to `-(2 : Int)^2 ≤ 0 ∧ abs (-(2 : Int)^2) = 4`. These examples preserve the distinction between a one-sided upper bound and an absolute-value/norm bound. |
| 19–21 | The parameterwise conclusion is `∀ p, ∃ A B, ... ∀ n, ...`, with coefficients allowed to depend on `p`. Both natural and integer counterexamples reject a single pair of coefficients for all `p,n`; the natural zero input remains in their quantified domain. No uniform family conclusion is introduced. |

The original proof analysis of the arbitrary finite prefix, eventual strict decrease derived from the aggregate branch-size premise, signed coefficient handling and choice of affine constants is retained. The actual core type confirms the intended generality and all-input conclusion. The finite connected clients and parameter-boundary counterexamples remain substantive checks of the public theorem. The pinned book method was previously read in full within its stated boundary; prior attributed AFP inspection remains attributed prior evidence, with no new original-theory read or rebuild claimed. The existing later-chapter exclusions and algorithm-specific obligations are unchanged.

The executed input is the exact 1,651-byte `Statements21.lean` from `chapter03-affine-receiving-correction1-20261104`, SHA-256 `1e048fe6242d26aca2a1afad7451d048072536ce4f2f5abea2cec9da839519a7`. It contains both defining imports and all 21 explicit-`@` checks in the original order. The supported options are `pp.universes`, `pp.explicit`, `pp.fullNames`, `pp.deepTerms`, `pp.proofs` set true and `pp.maxSteps = 1000000`. The actual output contains no omitted term/proof markers. The finite steps limit is not called unlimited. Its unchanged preparation comment is a historical artifact; the later closed execution records establish its actual execution.

## Qualified execution and input identity

The actual type run is `affine-recurrence-receiving-statements21-attempt1-20261104`: owned session 55717 closed with outer/native exit 0 and terminal chunk `bb0312`. Its exact command was the qualified one-thread `lake env lean` invocation on the bound input file, in the same private project used by the successful full check. Initial and final candidate identity are exact and clean. Its copied verification is the successful full-check record, not a new audit produced by printing types.

The complete pre/post observations were independently read and their **entire identity objects compared without path, trace or other normalization**. They agree on both immutable defining sources, the full six-file set of local compiler artifacts/hashes/traces, all ten configuration files, all nine clean dependency records and all twelve runtime components, as well as the exact program, names, roots and six external import names. The two-source closure and one local import edge were independently reconstructed from the immutable candidate; all source/blob and configuration identities agree. The saved qualified accepted-Q configuration, dependency and runtime dictionaries also match exactly.

The chronology is successful full completion at 19:07:11.708668 UTC, pre-observation at 19:09:27.140113, actual type command from 19:09:41.699183 to 19:10:01.129449, and post-observation at 19:10:10.183160. Both capture commands actually exited 0. The unchanged recorder has SHA-256 `4df281f3f427ec462a6973b9177fcc3f825b57b19fa8e205780f17cfaa89b5b7`. Qualification uses the actual stock Lake build and integrity checks, the retained official native environment and exclusive unchanged ownership, the actual command, and stable inputs together; matching fingerprints alone are not treated as loaded-object validation. No reviewer compiler, live-output capture or process polling was used.

## Complete normal candidate check and audit

`affine-recurrence-receiving-full-attempt2-20261104` is an actual successful full normal candidate check at this exact immutable source: owned session 66741 closed 0, terminal `487100`. I read all **2,617 native log lines / 304,174 bytes** in 17 bounded contiguous chunks, then the complete outer wrapper, and independently reconciled the concatenation to the complete 304,402-byte outer log. `full-attempt2-read-progress.json` records every range/hash/read boundary; `full-attempt2-audit-and-warning-assessment.json` records the independent row and warning reconciliation.

The unchanged source guard passed. The pre-build integrity check found exactly the expected missing `SquareApplications.olean` after failed attempt 1; no other module was invalidated. The aggregate then built successfully (415 seconds reported for that target; 10,076 Lake jobs for the build). The post-build integrity check hashed 3,090 artifacts with zero inconsistent modules. The matching verification records normal incremental mode, the exact candidate, official Lean 4.35.0 and all nine exact pins. The established normal-versus-fresh rules remain in force; no fresh-trigger exception or weakened profile was introduced.

The exhaustive audit independently reconciles to **1,031 checked project modules; 1,029 audit rows; 47,828 kernel-safe declarations; 27,242 theorem declarations; zero unsafe runtime declarations; and exactly `propext`, `Classical.choice`, `Quot.sound` as the transitive axiom union**. These are whole-project counts. Every one of the 1,027 accepted-Q audit rows is unchanged. The two added rows are the core's one logical/theorem declaration and the example module's 30 logical/27 theorem declarations. The 31/28 increment includes generated declarations; it is distinct from the 21 authored public names/19 authored theorems.

All current warning contexts were read. The 653 warning headers consist of the exact accepted-Q 647-header multiset plus the six previously assessed XR module-import advisories. There are 552 module advisories and 101 other inherited warnings. No warning suppression or new mathematical/source diagnostic was introduced. The six new advisories are accounted for explicitly; this is not blanket approval of unrelated future warnings.

| Secured evidence | SHA-256 |
|---|---|
| Full check outer log | `cada5fe7ec2fed03ef1eb9295359e9b894cfcdf21b1d2f66e06730bf926b9a24` |
| Full check native log | `877aca4200b45501e2ae0a92d94a2a04355e58fa6de12bc0920353b8ba35a66f` |
| Matching full verification | `70459831c371d1c496c29b3e1edd0352d41d64a00d1ec8f2a3600ee6880f05c9` |
| Actual 21 native output | `afd6d3ab3f0afbc81eba682a50556ada9f9acf72f3bcf80bfea98b8b1c06be07` |
| Actual 21 outer output | `fbb86fb040e0700421f315af6a111a73e8ba2a54e4c7b151ec7097d1a997df0b` |
| Pre-input observation | `bed2ba7d8ba3c727ea67838e26f903f9da2318c1d9244fc12dccf4ad639b6a5b` |
| Post-input observation | `f27b1cbbd2cfd09e7e24cdee9d722d6df793419ac8c2984d4bf3b791e35abe5b` |

## Complete finding and attempt reconciliation

| Record or finding | Final Spec disposition |
|---|---|
| Original complete XR source assessment | Retained by exact identity; no new mathematical/source finding and no dropped requirement. |
| Inherited `XP01-DOC-001` | Resolved for the receiving candidate by the exact Chapter 1 qualifier already assessed. The original draft's historical wording and later correction remain recorded. No XP01 implementation is claimed accepted through XR. |
| `XR01-ELAB-001` | Resolved. The original failed focused result and exact one-byte header repair remain preserved. The successful focused pair, successful full check and directly read actual block 18 confirm the intended current statement. No equivalence to an unelaborated predecessor type is claimed. |
| Full attempt 1 | Preserved as an actual failure: outer/native 1, nested Lean 137 at `SquareApplications`, no audit or matching verification. Its cause remains unestablished. The complete held failure assessment is unchanged; successful attempt 2 supplies new validation rather than rewriting the old outcome. |
| Former pending actual/full gates | Resolved for this Spec axis by the actual complete full check, all 21 full types, exact qualified pre/post input interval and complete original-scope reconciliation above. |

**There are no unresolved Spec findings at the exact reviewed candidate.** The current Spec recommendation is PASS. `final-disposition.json`, `final-bound-inputs.json` and the separate `completion-and-hold.json` bind the final outcome, immutable evidence and saved-file readback. Earlier reports and failure records remain byte-identical. The root must still complete the other independent final axis and the immediate qualified verification/integration steps; this reviewer has performed none of those actions.
