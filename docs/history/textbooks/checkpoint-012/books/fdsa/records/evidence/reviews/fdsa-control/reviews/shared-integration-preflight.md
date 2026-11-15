# Saved shared drafts: future integration preflight

Recorded 2026-11-02. This is a bounded read-only integration plan, not an integration, source review, validation run, review approval, or change to any requirement.

## Prerequisite and present status

**The repaired Chapter 1 must be accepted before any shared branch is integrated.** Its currently saved repair is `a14977b9e316cc484ffad8a470d26b15615956c0`; the eventual accepted repair may be a correction successor R. Passing the unchanged old candidate `1aabd512284fe86254278ac631eda061d311050b` cannot accept that repair or resolve its source-completeness findings.

The old gate remains owned by root in `conaled-ch01-review`, session 80227. Its source and outputs were not changed or probed by this investigation. No chapter or shared unit is accepted. The original Chapter 1 review base remains `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, with the original requirements and cost-model addendum retained.

The report path was checked absent before investigation and again immediately before this sole write. Root released the checkpoint 0024 control-write hold before creation. No requirements, tickets, prior reports, refs, source files or validation state were modified.

All actual Git reads used the installed pinned Nix environment from the main checkout:

```text
/root/.nix-profile/bin/nix --extra-experimental-features 'nix-command flakes' --option build-users-group '' develop --command python3 -
```

The Python batches invoked only read-only Git operations: `show-ref`, `log`, `merge-base`, `diff --no-ext-diff`, `show`, and `worktree list --porcelain`, with optional locks disabled. The default sandbox did not expose Nix; the existing launcher was accessed through the session's approved escalation route. No merge, cherry-pick, checkout, merge-tree operation, ref write, compiler, project hash helper, cache action or network/pin change occurred.

## 1. Actual saved history

The read refs and parent records agree with the supplied tips. All listed task branches and the existing baseline/remote refs must remain recoverable.

| Saved branch | Exact current tip | Immediate relevant parent |
| --- | --- | --- |
| `work/fdsa-book` | `1aabd512284fe86254278ac631eda061d311050b` | Original Chapter 1 candidate on baseline `7c1b4a3…` |
| `work/fdsa-basics-cost-models` | `a14977b9e316cc484ffad8a470d26b15615956c0` | `1aabd512284fe86254278ac631eda061d311050b` |
| `work/fdsa-insertion-costs` | `697bcf242ce65d74815b5639bddb1c6e754dd10f` | `1aabd512284fe86254278ac631eda061d311050b` |
| `work/fdsa-list-foundations` | `c28ba71863d2a35ee1c3a089caa90464e4cca692` | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| `work/fdsa-affine-recurrence` | `d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2` | `c28ba71863d2a35ee1c3a089caa90464e4cca692` |
| `work/fdsa-builder-costs` | `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8` | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| `work/fdsa-accumulated-work` | `7c6bc92c276d39e84351324c442869b8ffa6758c` | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| `work/fdsa-permutation-minimum` | `ff3dd88082c6283df40bcd86a4363841a0360b12` | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| `work/fdsa-permutation-order` | `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8` | `ff3dd88082c6283df40bcd86a4363841a0360b12` |
| `work/fdsa-permutation-tail` | `a0597381f02eddd074ee96cabaa974f2062285f8` | `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8` |
| `work/fdsa-permutation-expectation` | `11923e9ffd17246b6f22c5594002a1ba0434e43c` | `a0597381f02eddd074ee96cabaa974f2062285f8` |
| `work/fdsa-permutation-joint` | `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e` | `11923e9ffd17246b6f22c5594002a1ba0434e43c` |

The exact foundation prefix before the potential extension is:

```text
1aabd512284fe86254278ac631eda061d311050b
→ 697bcf242ce65d74815b5639bddb1c6e754dd10f   insertion costs
→ 333f900d04be3153518e68cc8c10920f40a08e05   Appendix A
→ df116c2f6d834eeb952157505b5c93a9ab5497e8   Appendix B.1 list calls
→ c994c22b754db5300d28670dff6b6f83ad56df02   Appendix C notation
→ 50dc7df3649d9f4f33bc6b3464c2c9fb6399aa46   notation dependency/type fixes
→ c80eec92f5458eccfd1c34c8314d666c2a1e3847   Empty notation boundary
→ c28ba71863d2a35ee1c3a089caa90464e4cca692   XP01 potential extension
```

The arrows above are an ordered commit list, not an inferred acceptance sequence. The complete Chapter 2 list/notation prefix ends at c80eec9. Although that prefix has no separate branch head today, it remains reachable through the saved foundation and affine branches. No new ref was created for it.

`master`, `origin/master` and the advertised `origin/HEAD` still identify the original baseline; the other pre-existing remote-tracking refs are unrelated preserved history. There was no fetch or upload to GitHub.

## 2. Current path overlap and its limits

Across the independently developed current scopes, the common changed paths are:

- `SquareApplications.lean`
- `docs/research/fdsa-reconstruction-map.md`

The resource/probability core additions on the independent branches have distinct paths. XP01 alone changes two pre-existing resource implementation files: `Applications/Resources/Potential.lean` and `Applications/Resources/FIFOContracts.lean`. Joint-order development later extends `PermutationOrder.lean` within the linear probability chain; that is an intentional ancestor/descendant change, not a competing independent branch.

No merge was attempted, so these are inspected overlap and conflict-risk findings, not a claim that Git reported conflicts.

### Concrete shared-file regions

| Combination | Inspected overlap or interaction | Required reconciliation |
| --- | --- | --- |
| Repair and foundation prefix | Both add imports after the old root's final `FunctionalBasics`/`ListReversal` region. The map's repair hunk around old lines 193–206 overlaps the foundation's old end section around 206. | Retain both repair imports and all four foundation imports. Keep the repair's corrected cost-model/source-limit prose and all source coverage added by the foundation. |
| Builder and the repaired/foundation root | Builder adds `Examples.DifferenceListCosts` near the repaired call-model imports. Its reconstruction section is inserted after the repair's source-limit section. | Preserve the repair/foundation import union and the complete declared closure-cost boundary; do not resolve by taking an entire older root or map. |
| Accumulated work and probability chain | Both add imports after `Examples.MetropolisHastings`; both extend the reconstruction map at its earlier final region. | Retain each included scope's import and source-use section; the two probability developments are independent. |
| Potential and affine | Their additions are near the existing potential imports, but affine already descends from the potential commit. | Use the recorded ancestry; do not lose the preceding potential import or its compatibility edit. |
| Probability chain | Each stage adds its own main/boundary modules and source-use documentation; XU05 adds joint laws to Order. | Retain all earlier statements and cases. A future correction to an accepted predecessor must survive reconciliation with the saved later draft. |

Changes to the chapter table in the reconstruction map are also part of the scope. Current draft wording must not overwrite an accepted repair's corrected coverage or turn a future integration into an unsupported chapter-completion statement. Documentation conflicts require the same exact-scope preservation as source conflicts.

The inspected task diffs do not change the Lean pin, dependency manifest, Nix flake/lock, build checker or integrity policy. That fact supports the existing routine validation route only while those inputs remain unchanged; it is not an advance waiver for a later configuration change or integrity incident.

### Semantic interaction without a textual conflict

The repaired `SharedDemand.lean` imports `Applications.Resources.Potential` and calls `run_potential_exact`. XP01 generalizes budget/accounting while retaining the Nat public contracts and adds the known raw-zero type annotation in `FIFOContracts`. Therefore, combining XP01 with the repaired Chapter 1 must recheck the actual demand-model caller, the retained Nat potential clients and FIFO clients. A clean textual merge cannot establish this compatibility. The FIFO annotation is part of XP01 and must not be dropped as incidental cleanup.

The builder core imports `CallCount` and `Workload`; its shared execution dependency is not a reason to require XP01. The accumulated-work core is analytic Mathlib code; its measured examples use `Workload`/`CallCount`, not the generalized potential budget.

## 3. Source imports and acceptance dependencies are different

| Scope | Actual source dependency relevant here | Retained acceptance dependency |
| --- | --- | --- |
| X002 / Appendix A / XB01 / Appendix C | Insertion uses CallCount and Sorting; list calls use CallCount and SymmetricCosts; notation examples import FunctionalBasics and ListLibrary. | Repaired Chapter 1 first. Their existing combined-foundation review scope retains all exact component requirements. |
| XD01 builder | CallCount, Workload, Batteries DList; no source import of XP01, affine or accumulated work. | Repaired Chapter 1 and this unit's full matching gates. |
| XU01 minimum | Mathlib finite permutations and uniform measure. | Repaired Chapter 1 and XU01 gates. |
| XU02 whole order | Core is Mathlib-based; its boundary examples import the earlier minimum fixture. | FDSA-001 and XU01 acceptance before integration, per ticket. |
| XU03 conditional tail | Core imports Order; examples retain earlier order cases. | Repaired Chapter 1 and preceding minimum/whole-order acceptance. |
| XU04 expectation | Core imports Minimum; its conditional-placement boundary imports Tail. | Repaired Chapter 1 and preceding shared-base acceptance. |
| XU05 joint | Extends Order; main/boundary examples import Tail and earlier Order examples. They do not import Expectation. | **The frozen preceding-base dependency still requires XU04 before XU05.** Source-import independence does not authorize skipping it. |
| XP01 potential | Workload; changes generic accounting and preserves old Nat clients. | Repaired Chapter 1 and the existing foundation scope. |
| XR01 affine | Core imports Mathlib only. Its saved tip nevertheless descends from c28/XP01. | Repaired Chapter 1 and relevant shared foundations validated and reconciled, as frozen. |
| XW01 accumulated work | Core imports Mathlib analysis; examples use actual measured computations. | Repaired Chapter 1 plus XW01's own gates. It has no import dependency on the permutation chain. |

The XU05 result is stronger than the pair of marginal laws. However, linearity of expectation does not itself need this joint result. The book's Chapter 2 expected-cost proof must choose and justify its actual source/distribution/cost route. The existence of a later joint-law draft is not a reason to require unrelated results before starting deterministic sorting.

## 4. Smallest justified future ordering

Nothing in this section authorizes action while the current gate or Chapter 1 acceptance prerequisite remains outstanding.

### Stage A: accept the repaired Chapter 1 alone

Collect the old run's outcome, then validate a14977b or a correction successor R in the retained Chapter 1 loop. Keep the original chapter review base, original requirements, frozen addendum and all findings. The review scope is the full repaired chapter, not just the seven-file addendum delta.

Both final independent axes must pass the same repaired candidate with matching full verification and immediate candidate-record verification. Only then record Chapter 1 acceptance and make R the starting accepted base for shared integration.

### Stage B: Chapter 2 list and notation foundation

The smallest complete saved prefix for these existing scopes is c80eec9. Reconcile that whole prefix with accepted R in an isolated candidate. This brings X002, Appendix A, XB01 and Appendix C, including the two final notation fixes, while leaving XP01 and affine outside the candidate.

The existing tickets already describe a combined foundation review from the old base. Preserve their individual exact requirements and previous evidence while recording the newly incorporated accepted base and the combined candidate's full scope. The earlier insertion/Appendix A focused successes are useful historical evidence, not a passing build or review of this reconciled candidate.

A candidate containing this prefix can be validated and reviewed as the declared combined foundation scope; no module or boundary case may be omitted to reduce the gate. Promotion into accepted work follows that candidate's complete gates. This is not permission to integrate it before Stage A.

### Stage C: Chapter 2 closure costs and the needed ranking prefix

Reconcile XD01 builder costs next when the natural-run sorting bridge needs them. This is independent of XP01 and XR01. Retain the source asc/scanner and comparison-versus-construction obligations in Chapter 2; the shared closure model does not discharge them by itself.

For the chosen average-quicksort proof, use only the required accepted ranking prefix:

1. XU01 minimum.
2. XU02 whole relative order after XU01 acceptance.
3. XU03 conditional remaining order after its preceding base acceptance.

Each ticket's explicit acceptance prerequisite remains in force. An eventual merge of an entire saved chain is not a shortcut around those gates.

If the Chapter 2 proof actually uses the full joint/distribution route, continue through **XU04, then XU05**, with their matching acceptance steps. XU04 is a retained ticket/ancestry dependency of XU05 even though joint source imports do not require its expectation module. Do not cherry-pick around that requirement or rewrite it merely to shorten Chapter 2 integration. If only the expectation recurrence and marginals are needed, the chain can remain at the accepted tail prefix and the later two saved drafts remain queued. This is deferral of unused scope, not removal from the whole-book obligation.

Chapter 2 may proceed after its sequential predecessor is accepted; it need not wait for Chapter 3-oriented scalar/analytic units merely because they have already been drafted. It still requires its complete deterministic algorithms, stability, exact cost correspondences, all exercises and asserted average/worst statements before chapter acceptance.

### Stage D: later shared preparation without delaying Chapter 2

Defer the affine and accumulated-work units from the initial Chapter 2 prerequisite set unless a concrete Chapter 2 proof establishes a genuine need. XR01's actual immediate client is the selection recurrence; XW01's geometric drift client is especially the random-selection scan/tail argument. Their generality is not evidence that they supply the book's quicksort or mergesort cost laws.

For the saved affine history, first reconcile and accept the outstanding foundation/XP01 scope, preserving the Nat compatibility contracts, then the affine extension. Merging d64b4c8 wholesale otherwise brings XP01 by ancestry. The scalar theorem's import independence does not erase that included source or its requirements. No extraction/rebase of the affine patch is proposed here.

XW01 can be reconciled independently after its repaired-base prerequisite, with its complete measured examples and analytic boundary cases. It need not precede the permutation chain. Chapter 3 remains queued until Chapter 2 is accepted, regardless of when these cross-cutting units pass.

## 5. Reconciliation with a correction successor R

The safe future construction begins at the exact accepted R, which may differ from a14977b. Before any later source reconciliation, record the correction delta from a14977b to R and check its parent/merge-base relationship through read-only Git.

- If R descends from a14977b, the builder, accumulated and probability histories have a14977b as their known fork. Preserve R's corrections during the ordinary three-way reconciliation.
- The list foundation diverged at 1aabd51, so its merge base with an ordinary repair successor remains that older commit. Its two shared-file overlaps need deliberate combination with all repair additions.
- A future correction to an earlier shared unit likewise changes what later saved drafts must be reconciled against. In particular, XU05 reuses private Order helpers and must retain any accepted correction to them.
- If the eventual accepted repair does not have the assumed ancestry, stop the automatic plan and record a new exact base/scope disposition. Do not force an ancestry or replace accepted files with an old draft snapshot.

Use a new integration-candidate branch/checkpoint when the prerequisite is actually satisfied. Preserve the saved development refs and their historical commits; do not rebase, reset or force-rewrite them to make the graph look linear. Ordinary history-preserving merges can retain the supplied commits. The current plan performs none of those operations.

For every future reconciliation, compare the combined candidate with both the accepted base and each included saved scope. Record any resolution or adaptation. This comparison must show that it retained the accepted repair, the whole intended shared change and all earlier corrections; merely reporting a conflict-free merge is insufficient.

## 6. Source, cases and scope that must remain

The full repaired Chapter 1 changes fourteen paths from the original baseline. Retain:

- `Applications/Arithmetic/EuclidInduction.lean`.
- Resource `CallCount`, `ListReversal`, `CallComparison`, `SharedDemand`, and the `Measured.lean` universe-generalization contract.
- `Examples/FunctionalBasics.lean`, `Examples/ListReversal.lean`, `Examples/CallModels.lean` and `Examples/SharedDemand.lean`.
- The source provenance, call-model note, reconstruction map and all public imports.

For each shared scope actually included in a candidate, preserve its complete connected cases:

| Scope | Required retained source/case families |
| --- | --- |
| Foundation prefix | InsertionSort and ListCalls cores; InsertionCosts, ListLibrary, ListCalls and FunctionalNotation examples; complete list/notation source maps and Empty/partial-operation boundaries. |
| XP01 | Potential/FIFOContracts changes; MappedPotentialAccounting and all existing Nat potential/FIFO clients; the repaired SharedDemand caller. |
| XR01 | AffineRecurrence core/example, including signed data, finite prefix and quantifier boundary. |
| XD01 | DifferenceListCosts core/example and separate construction/invocation observations, arbitrary suffix and duplication boundaries. |
| XW01 | AccumulatedWork core plus both main and Boundary examples, including actual measured stages, dependent finite outcomes, q=0, N=0 and the missing-prefix-cap counterexample. |
| Probability chain | Minimum, Order, Tail and Expectation cores; both main and Boundary modules for each included stage; both Joint modules when XU05 is included; all earlier deterministic orientation, empty/null-event, overlap and changed-environment cases. |

All other pre-existing project imports and proof-audit roots remain. An unmerged deferred scope stays preserved on its saved refs and in checkpoints; an included scope may not have its examples or imports silently pruned. The whole-book chapter tickets, original frozen requirements, reconciled inventories, candidate records and findings remain outside the source diff in the control payload. No scope is accepted merely because its commits are ancestors of another draft.

## 7. Reuse the idle isolated normal cache, with separate evidence

The specific future reuse location is `/workspace/scratch/845aa1048b05/conaled-ch01-review`, currently detached at 1aabd51. Follow the recorded Chapter 1 handoff and `build-cache-checkpoint-preflight.md`:

1. Let the old check finish unchanged. Obtain its actual exit status and confirm its writers are quiescent through root's owned process/session evidence. A saved PID or a progress line is not proof that the gate or its descendants have finished.
2. Before any checkout change or new check, preserve the old log, exit/result record, reported commit, applicable configuration/pin identities, audit result and any actual `.lake/verification.json` in the control evidence. On success, verify the old record against the unchanged old candidate and retain the result. On failure or interruption, preserve that outcome without inventing a success record.
3. The old evidence remains labeled 1aabd51. It does not validate a14977b, R, or any combined candidate, and it cannot close the reopened source findings. Keep a historical copy outside the active verification-record path, because a new validation removes/replaces that path.
4. Once idle, use this same isolated checkout for the immutable repair candidate and later immutable combined candidates. Retain its normal Lake outputs in place and let the existing dependency tracking and before/after integrity guard decide reuse. Do not share a writable project build directory with another active checkout, copy private fresh-mode outputs into it, or transplant arbitrary artifacts/traces from other branches.
5. Continue the pinned environment and supported routine command form, including the already selected `LEAN_NUM_THREADS=1` where appropriate. Focused builds of the affected core/example targets precede the applicable full `./check.sh --candidate HEAD`; they do not replace it. The full gate retains source/public-coverage checks, clean candidate/dependency checks, input rehashing, both integrity guards, full build and exhaustive proof audit.
6. Save each candidate's actual success record separately before proceeding to a later candidate. Obtain both independent final review axes on that exact candidate and requirements, then run `./check.sh --verify-candidate HEAD` immediately before acceptance. A new correction commit requires matching renewed evidence.
7. The existing source-only-change mode ruling does not authorize ignoring a new pin/tooling change or integrity concern. If one occurs, apply the repository's fresh-mode/runbook requirements and retain the evidence. This plan neither investigates performance nor changes validation policy.

The optional separate build-state recovery artifact is not needed for source integration and is not implemented here. If root later elects to preserve it, its separate preflight requires quiescence, complete original artifact families and honest origin metadata. The normal source/history/control checkpoint remains cache-free and complete on its own. A saved historical verification JSON must never be installed as current acceptance evidence after restore.

## 8. Candidate reviews, refs and durability

Keep the original Chapter 1 review scope and retained findings until the repaired chapter is accepted. For later shared reconciliation, record the accepted incorporated base and immutable candidate, preserve the original component bases/requirements as provenance, and carry every unresolved finding forward. The repository review procedure permits recording a new incorporated integration base; it does not permit erasing old scope or treating an earlier preflight as final approval.

Use the existing implementation/review workflow rather than creating another loop for this plan. Both independent final axes must assess the complete included scope on the same combined candidate, including resolution edits and consequential compatibility. Earlier analysis of unchanged material can be retained with explicit identity evidence. No focused success, cache hit, ancestry, source preflight or independent finite calculation supplies missing full-candidate or final-review evidence.

Before future promotion, compare the exact delivered tree with the reviewed candidate and verify its candidate record. Record the accepted scope in local tickets, then create, expose and save the normal recovery checkpoint. Preserve all advertised refs, including existing branch and remote-tracking refs, and full reachable Git history; preserve the named original candidate SHAs even when later authoring advances a branch. Retain exact ref inventories, local tracking, requirements, review evidence and checkpoint receipts. No GitHub write is needed.

**Outcome of this preflight:** the current histories can be reconciled through a small Chapter 2-first sequence, with two main textual overlap paths and one identified later Nat-accounting compatibility surface. No integration, validation, acceptance or requirement change has been performed or authorized by this report.

