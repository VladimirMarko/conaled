# Chapter 1 independent Spec review — unified native continuation

Reviewer: `/root/chapter01_review_coordinator/spec`.
Date: 2026-11-03. This replaces the unavailable historical Spec agent within
the same logical Chapter 1 review loop. The previous independent reports,
source-completeness reopening and stable finding identifiers remain intact.

## Current outcome

**Passed.** The completed full-scope source review and matching successful
fresh candidate verification establish all required Spec evidence for
`07e480f6ec9958d4975bb90151005b84f2907614` against the unchanged original base.
SPEC-001, SPEC-002 and SPEC-003 are fixed with reviewed source and matching
validation evidence. SPEC-V001 is resolved by the actual terminal result and
matching verification record. Unresolved Spec findings: **0**; worst issue:
**none**. The terminal reconciliation below records the precise evidence.

Root's immediate `--verify-candidate HEAD`, the separate Standards outcome,
integration and acceptance checkpoint are subsequent caller-owned steps.
This Spec outcome does not claim that those steps have occurred or that any
later candidate is approved.

## Historical provisional outcome — before terminal evidence

**Blocked on matching complete candidate validation. Source review is complete;
no new mathematical, source-coverage or scope finding was identified.**

This is a provisional report while the root-owned fresh gate is running.
SPEC-001, SPEC-002 and SPEC-003 have adequate source repairs in the inspected
candidate, but are not closed before the matching full evidence is reconciled.
SPEC-V001 remains a separate validation blocker. This report does not authorize
Chapter 1 acceptance, integration, or advancement to Chapter 2.

## Immutable scope and evidence read

- Original fixed base and independently confirmed merge base:
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Reviewed candidate: `07e480f6ec9958d4975bb90151005b84f2907614`.
- The isolated `conaled-ch01-review` checkout was independently confirmed clean
  at that candidate. Review scope is `git diff BASE...CANDIDATE`, all fourteen
  changed paths, with no task-source exclusion.
- The six commits comprise the original basics implementation, substantive
  cost-model repair, and four proof-only corrections. The full later proof-fix
  diff from `a14977b9e316cc484ffad8a470d26b15615956c0` was inspected; it changes
  proof scripts, not definitions, statements, hypotheses or expected cases.
- The original unrelated untracked historical ZIP remains outside the task.
  No other unaccepted shared draft or Chapter 2 prefix is in this candidate.

Both frozen requirements were read and their exact fingerprints checked:

| Requirement | Bytes | SHA-256 |
| --- | ---: | --- |
| `chapter01-requirements.md` | 2672 | `7b7ce18bcfe9bb888ac9e99810a1095a823f9a67dbb54717c5bf673017a890ba` |
| `chapter01-cost-model-requirements.md` | 9471 | `1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1` |

The governing `REQUEST.md`, original and corrected Chapter 1 inventories,
`chapter01-round1.md`, complete initial Spec report and its superseding
reopening, addendum-sufficiency review, repaired Spec source preflight, author
statement review and compiler-findings history were read. Their relevant
source-analysis records match the retained fingerprints. The initial report's
superseded claim that the old candidate had no missing source obligations is
not reused as approval.

The official PDF was independently rehashed: 1,742,029 bytes, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`, matching the
July 27, 2026 edition. The complete Chapter 1 reading copy, printed pp. 1–10
(PDF pp. 7–16), was read against the candidate coverage. Source-recovery
provenance is `../provenance/source-recovery-20261103.json`. The book and its
extracted text remain research inputs, outside this report and deliverable.

Applicable candidate guidance was read through `AGENTS.md`: README's
environment/build/audit and proof-boundary rules, statement review in
`example-driven-development`, architecture/domain guidance, the glossary and
ADRs 0001/0010. The explicit user exception permits exact native Lean/Lake
without Nix, and the user requires local tickets/checkpoints rather than
GitHub writes. None of these exceptions changes formal scope or proof gates.

## Full Chapter 1 source and statement assessment

All fourteen changed paths were inspected. Necessary unchanged implementations
were also read: `Resources.Measured`, `Resources.Workload`,
`Resources.Potential`, `Resources.Growth`,
`Resources.TreeFlattening.appendWithCost`, and
`Resources.SymmetricCosts.reverseRun` with their relevant laws.

| Source scope | Candidate evidence and assessment |
| --- | --- |
| §§1.1–1.3, language/types/notation | `fdsa-reconstruction-map.md` maps the terminating functional language, Bool/Prop distinction, numeric types, sets, lists, option, pairs, unit, updates, multisets and typography to existing Lean interfaces. `Examples.FunctionalBasics` retains meaningful update, numeric-conversion, multiset, option/product/unit and comprehension cases. The source's Fibonacci and alias-pattern passages illustrate syntax without supplying a new complete algorithm specification. |
| Append equations and associativity | `append_equations` checks nil/cons behavior and `append_associative` consumes `List.append_assoc` over arbitrary lists/payloads. No new foundation replaces the standard operation. |
| Euclid computation induction | `Arithmetic.Euclid.induction` matches the source's quantifier order and nonzero-branch implication exactly. Its proof decreases the second natural argument using modulo. `gcd_equation` connects that orientation to standard gcd. The common-divisor application uses this rule and retains concrete satisfiable and zero-boundary cases. |
| Cost algebra | `CallCount.primitive_rule`, `arguments_rule`, `let_rule`, `if_rule`, `case_rule` and `tick` express actual measured-value composition. The bound value selects the body, and only the selected control arm contributes. Existing additive assumptions are local; no unnecessary commutativity is introduced. This is the declared algebraic interpretation of the source's metalanguage, not an unproved source translator. |
| Append call count | `appendRun` adds the terminal-call unit to the inspected recursive copied-cell append. Its nil/cons equations and `appendRun_exact` establish the actual source recurrence and `n+1`, rather than identifying two resource models by name. |
| Naive reverse and exercise | `naiveRun` recursively reverses the tail and then appends. Its value theorem preserves the ordered list, its cost recurrence retains both recursive computations, and its doubled exact identity proves the triangular exercise including the empty list. Natural division is derived from that identity. The separate quadratic bound is the printed bound. |
| Accumulator reverse | The reused `reverseRun` has the exact source equations, arbitrary-accumulator value and `n+1` work. `accumulator_exact`, agreement and cost comparisons preserve their distinct semantic/resource conclusions. Strict improvement alone requires a nonempty input. |
| Integration and checked clients | The list squares and continuation compose through matching measured boundaries; the native bind client retains both observations. The length-three counts are 10 and 4, and composition gives 14. Empty, singleton, distinguishable-order, duplicate and nonempty-accumulator cases expose relevant boundaries. Public imports include all new modules through the four example imports. |
| §§1.5–1.5.2 comparisons | The three repaired comparison obligations are assessed individually below. The source map explicitly corrects its former dismissal of mathematical prose claims. |
| §1.5.2 runtime and §1.5.3 discussion | The source explicitly declines a full compiler/runtime/hardware proof. The candidate preserves that conditional boundary and does not assert actual Lean allocation, wall time or a RAM implementation theorem. The preference for explicit bounds is explanatory; no additional master-theorem proof is claimed. |

The source's intermediate page-7 append translation appears inconsistent with
its zero-cost constructor convention. The candidate identifies that issue and
targets the unambiguous final recurrence. It does not silently change the
recurrence or introduce an axiom to reproduce an inconsistent intermediate
line.

The `erasureSquare` change is a universe-signature generalization allowing
natural observations for arbitrary-universe payloads. Its implementation and
semantic law are unchanged; old equal-universe specializations remain
representable. The new generic square/composition clients exercise the intended
use. Full downstream elaboration remains part of the pending candidate gate.

## SPEC-001 — uniform fine/coarse tariff comparison

**Initial source disposition:** source repair adequate; closure then pending
matching complete validation. This finding is now closed by the terminal
reconciliation below.

`Applications/Resources/CallComparison.lean:19–90` observes the same occurrence
list under two tariffs. `refinedCost` sums the entry unit and a nonnegative
extra charge per occurrence. It preserves repeated entries. The unconditional
lower bound and uniform local upper bound are derived by list induction;
the final whole-trace inequality is not an assumption.

`catalogue_refined_bounds` takes a fixed finite local-case catalogue and uses
its supremum to fix K independently of the trace. `refinedCost_isBigO` puts K
outside the eventual input quantifier. Both real-cast Big-O directions are
present for arbitrary filters. Empty traces and a zero extra tariff remain in
scope without a positivity premise, because refined work retains the entries.
Neither the catalogue law nor its examples assume finite payload types.

`Examples/CallModels.lean:17–76` supplies the required source client. Its
append branch trace has the explicit terminal and cons equations;
`appendEvents_cost` connects that trace to the actual `appendRun` observation.
The specified overheads 1 and 4 give `5*n+2` versus `n+1`, with the finite
Boolean catalogue giving factor 5. The comparison and asymptotic client use
the general public results. The duplicate-bearing length-three and empty
payload cases retain the independent expected counts.

The call-model explanation explicitly assigns local work to charged entries,
includes the root boundary before entry omission, and requires coverage and
separate bounds for unbounded primitives, bit widths or callbacks. It labels
the append tariff as illustrative. No machine-instruction claim or total-cost
premise substitutes for the required fixed-program argument.

## SPEC-002 — entry omission with the zero qualification

**Initial source disposition:** source repair adequate; closure then pending
matching complete validation. This finding is now closed by the terminal
reconciliation below.

`CallComparison.lean:92–121` proves the unconditional first inequality and the
factor-two upper bound under `1 ≤ T`. `tick_cost_comparison` connects them to
the actual entry operation; `tick_value` separately preserves the returned
value. The body-cost premise is satisfiable and exposes the intended domain.

The forward family theorem requires eventual positivity on an arbitrary
filter, while the reverse comparison is unconditional. The real casts are
explicit. No non-identically-zero premise is substituted for eventual
positivity, and no positivity requirement is silently discarded during the
proof-only norm/cast corrections.

`Examples/CallModels.lean:78–103` connects the family theorem to measured
programs, retains unchanged-value and zero-cost clients, and defines the
specified intermittent family. The family is nonzero at input 1 but zero at
an even input after every proposed cutoff. Its theorem refutes the forward
Big-O statement using that input, including arbitrary real comparison
constants through the standard asymptotic definition. Earlier measured entry
examples retain a concrete positive body cost. Documentation limits the result
to this one-entry boundary and does not advertise transitive multi-definition
inlining correctness.

## SPEC-003 — actual shared demand and an eager-catalogue bound

**Initial source disposition:** source repair adequate; closure then pending
matching complete validation. This finding is now closed by the terminal
reconciliation below.

`Applications/Resources/SharedDemand.lean:28–163` defines an actual option-cache
transition. A miss computes, stores and charges the fixed pure callback;
a hit returns its stored value and zero callback work. `Valid` constrains
stored values, with empty-cache validity, request/run preservation, and the
arbitrary-prefix demanded-value result proved separately from accounting.
The next request may repeat an earlier identity. Cached entries survive
arbitrary intervening requests, and nonempty repeated demand charges once.

Decidable equality is local to identity updates. Finiteness begins only at
catalogue accounting. Payload equality, ordering and inhabitance are absent.
The examples include infinite natural identities and an empty catalogue with
empty payloads, as well as equal values at distinct identities; they expose
the intended assumptions rather than forcing all identities or values equal.

`SharedDemand.lean:168–248` derives exact local remaining-work conservation
from the hit/miss transition and finite sum decomposition. It then uses the
inspected existing `run_potential_exact` over the actual measured executor.
Nonnegative natural work yields `run_cost_le_eager`. The desired final
inequality is not a simulation premise. Accounting correctly does not require
valid stored payloads; demanded-value correctness does.

`Examples/SharedDemand.lean` connects these laws to five demands costing 3,
the unused cost-1000 computation, preserved demanded values, arbitrary
intervening requests, empty requests and an empty catalogue. The duplication
example uses two actual requests under one sharing identity, proves the shared
layer equals one eager measured bind, and contrasts two unshared binds. Its
recursive families have equal values and derived counts `n+1` and
`2^(n+1)-1`, including the depth-four observations `(16,5)` and `(16,31)`.
These are connected computations, not unrelated numerical sequences named
after evaluation strategies.

The source and documentation explicitly require correspondence to an external
program's eager occurrences, stable observations and eager cost before using
the catalogue sum for that program. The theorem does not assert a universal
lazy-language simulation. Cache administration is excluded from this
callback-work observation. The defined sharing interpretation, and its
distinction from unshared call-by-name, satisfy the accepted bounded addendum
without weakening its mathematical obligations.

## Proof-correction and example continuity

The four commits after `a14977b` change only proof construction: preserving
natural casts through norm simplification, unfolding the concrete cache cases,
qualifying `Resources.bind`/`pure`, and removing redundant proof syntax.
The final arbitrary-prefix cache example still uses `request_hit`,
`run_preserves_cached` and the public miss equation. Its independently stated
value and zero-work conclusion is unchanged. No warning policy, hypothesis,
definition, source correspondence or cost tariff was weakened.

C1-ELAB-001/002/003 have retained focused compiler confirmation at this exact
candidate. The historical focused pass is supporting evidence; it is not the
new full project gate. No compiler, runtime test or proof-audit command was
started by this reviewer. The read-only `git diff --check BASE...CANDIDATE`
completed successfully.

## Historical provisional validation and stable disposition

The following records the state before the actual terminal evidence arrived.
It is superseded by the completed reconciliation and current dispositions below.

The root-owned new attempt is recorded under
`../provenance/chapter01-unified-fresh-attempt4/`. Its intended payload is
unchanged `./check.sh --candidate HEAD --fresh --jobs 1` through the supplied
native kit with one Lean thread. The coordinator reported that source,
coverage and compiler checks passed and fresh compilation is underway.
No terminal success or matching verification record was supplied for this
provisional disposition. Ordinary module-level axiom prints are not the final
exhaustive audit.

The selected fresh route checks private project outputs and reuses pinned
external dependency caches. Incremental output-integrity phases are not an
additional gate for this route. The retained Standards fixture-applicability
disposition adds no unrelated validator regression run to this formal change.
All actual source-policy/coverage, candidate/compiler/dependency identity,
complete compilation, exhaustive audit and successful-record requirements
remain in force.

| Stable finding | Current disposition | Remaining requirement |
| --- | --- | --- |
| SPEC-001, major | Source repair adequate; unresolved pending final validation | Complete matching gate and final evidence reconciliation |
| SPEC-002, major | Source repair adequate; unresolved pending final validation | Complete matching gate and final evidence reconciliation |
| SPEC-003, major | Source repair adequate; unresolved pending final validation | Complete matching gate and final evidence reconciliation |
| SPEC-V001, validation blocker | Unresolved | Actual terminal success, complete log and verification JSON matching candidate, compiler, dependencies and selected mode |

New source findings: **0**. Worst newly identified source issue: **none**.
Overall Spec outcome: **Blocked**. No chapter is accepted by this report.

After the complete evidence arrives, this same reviewer will reconcile it
against the inspected immutable candidate and update these dispositions.
Root must separately obtain the Standards outcome and perform immediate
`./check.sh --verify-candidate HEAD` before accepting or integrating the
candidate. A changed source candidate requires the full-scope continuation
of this loop; this report cannot approve a newer tip by implication.

## Terminal validation reconciliation — 2026-11-03

The same Spec reviewer resumed solely to reconcile completed validation with
the already inspected full fourteen-path candidate. No source changed and no
second source review, compiler, build, audit or verification command was run
by this reviewer.

The actual root-owned full fresh attempt is complete. The preserved recorder
and the kit's own command record both report exit **0**, with no timeout or
recorder error. The exact command remains the supplied unified kit's
`run --threads 1` route around stock
`./check.sh --candidate HEAD --fresh --jobs 1`. The recorder started at
2026-11-03T20:08:58.985393+00:00 and completed at
2026-11-03T21:08:58.959923+00:00, elapsed 3599.974328367 seconds. Initial and
final recorded source identity are the same clean candidate.

The following files under
`../provenance/chapter01-unified-fresh-attempt4/` were independently read and
their full byte identities checked:

| Evidence | Bytes | SHA-256 |
| --- | ---: | --- |
| `result.json` | 1186 | `8f2a76c0f6b3adfb3c1f4c92f8e1aa946ac476cbe3e253869bf0ae1d65ae7873` |
| `full.log` | 201415 | `751732fbf985a26956e27eef716bf88834d41e885494884cd80aa858d9f40af2` |
| `verification.json` | 861 | `8d9257a238ab4c2e0743a41851a080f403aa09b41f4bf34690496c1f9a7b0264` |

The retained `kit-command-record/result.json` independently agrees on the
actual command, working directory, single-thread setting and zero terminal
exit. The closed log contains all numbered fresh compilation entries from
1 through 960, followed by the audit and final `PASS: all 961 modules checked`.
It records successful source-policy and public-coverage/version checks,
3534.78 seconds of fresh compilation and 62.74 seconds of proof auditing.
Every one of the ten changed Lean source modules is explicitly present in
both the successful compilation sequence and the audit's module inventory.

The exhaustive audit reports 45,074 kernel-safe declarations, 24,929 theorem
declarations and 959 project modules with audit roots. Its transitive axiom
union is exactly `[propext, Classical.choice, Quot.sound]`; zero kernel-unsafe
runtime declarations were excluded from logical roots. The final audit
explicitly passes every kernel-safe project declaration. This is the completed
exhaustive result, not an inference from ordinary per-module axiom prints.

The verification JSON states `result: passed`, candidate
`07e480f6ec9958d4975bb90151005b84f2907614`, mode `fresh`, and official Lean
4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. All nine recorded
dependency revisions exactly match the candidate's `lake-manifest.json`.
The compiler matches `lean-toolchain`. The retained verification bytes were
independently compared with the actual isolated checkout's
`.lake/verification.json`; they are identical. Read-only Git checks still
find a clean exact candidate and the original base as merge base. Both frozen
requirement digests remain unchanged.

The complete closed log has no reported error or failed phase.
`warning-observation.json` preserves the nonfatal warning inventory and
identifies all 37 warning-bearing source files as blob-identical to the
original base. The already reviewed candidate does not alter the warning
policy. These warnings do not negate the actual passing compile/audit result
or introduce a new Spec finding.

### Final stable finding dispositions

| Stable finding | Final disposition | Evidence |
| --- | --- | --- |
| SPEC-001 | **Fixed with review evidence** | The full source assessment above establishes uniform local-tariff coverage, finite-catalogue bounds, both asymptotic directions and the connected actual append client; the exact candidate's complete fresh build and exhaustive audit now pass. |
| SPEC-002 | **Fixed with review evidence** | Reviewed pointwise/eventual positivity, actual tick/value connections and zero/intermittent counterexamples are checked in the matching successful full candidate. No hypothesis or intended case was weakened by the proof corrections. |
| SPEC-003 | **Fixed with review evidence** | Reviewed actual cache transitions, validity/value laws, structural at-most-once accounting, catalogue bound and shared/unshared clients are checked in the matching successful full candidate, with the stated external-program/runtime limits retained. |
| SPEC-V001 | **Resolved by matching completed validation** | Actual exit 0, complete closed fresh-build/audit log, unchanged candidate/pins/compiler and matching successful verification JSON identified above. |

The earlier three source omissions, the compiler-fix history, failed or unknown
historical runs and the provisional blocked outcomes remain preserved. Their
history is not overwritten by this later success. All required Spec evidence
now matches this one immutable candidate; no new or unresolved Spec finding
remains.

**Final Spec outcome: Passed**, with **0 unresolved findings** and no worst
issue, for base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` and candidate
`07e480f6ec9958d4975bb90151005b84f2907614`. Root must still reconcile the
separate Standards result and immediately run the stock
`./check.sh --verify-candidate HEAD` before acceptance/integration. This
report neither runs that command nor claims that subsequent acceptance,
integration or the acceptance checkpoint has already occurred.
