# Chapter 1 independent Spec review — round 1

Reviewer role: independent Spec axis under the existing Chapter 1 review loop.
Reviewed on 2026-11-02.

## Current outcome after source-completeness reopening

**Outcome: Findings-present, with validation also blocked.** There are three
unresolved source-completeness findings, `SPEC-001`–`SPEC-003`, each of major
severity for chapter acceptance. `SPEC-V001` remains a separate validation item.
The full check of this unchanged candidate cannot resolve missing source claims.

The original assessment below is retained as review history. Its assertions
that source review was complete and no further source obligations remained are
**superseded** by the reopening addendum at the end of this record. The initial
review missed mathematical comparison claims expressed in the source's prose.
That was a scope-review error, not a change to the original user request.

## Initial assessment (superseded completeness conclusion)

**Initial outcome: Blocked on pending complete candidate validation.**

Mathematical/source review is complete. **Code or scope findings: 0.**
No defect severity applies. This is not yet an acceptance approval.

## Pinned scope

- Base and merge-base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `1aabd512284fe86254278ac631eda061d311050b`.
- Diff: `git diff 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd...1aabd512284fe86254278ac631eda061d311050b`.
- Commit: `1aabd51 feat(resources): formalize FDSA basics (#174)`.
- All nine changed paths were included. The isolated candidate checkout was
  clean and still at the supplied SHA when inspected.
- The original unrelated untracked historical checkpoint ZIP is excluded;
  no task source is excluded.

Requirements read: `REQUEST.md`, `tickets/FDSA-001.md`, the original Chapter 1
inventory, and the pinned book's complete Chapter 1 text (printed pp. 1–10).
Source edition: July 27, 2026, with the digest in the saved provenance manifest.
Applicable AGENTS, statement-review guidance, architectural/domain guidance,
glossary, ADRs 0001/0010 and README validation guidance were also read.

The acceptance scope of this review is Chapter 1. The complete book remains
the eventual request; neither this candidate nor this report closes that scope.

## Source coverage and mathematical assessment

| Source obligation | Candidate witness and assessment |
| --- | --- |
| §§1.1–1.3: total functional language, standard types, syntax and notation | The source map explicitly uses Lean's total definitions and standard libraries. `Examples.FunctionalBasics` checks meaningful update, coercion, multiset, option/product/unit and set uses. This avoids inventing unrequested semantics or parallel foundations. |
| Append equations and associativity | `append_equations` and `append_associative` connect to ordinary `List` append and its library associativity theorem. Quantification is over arbitrary lists and payloads. |
| Euclid computation induction | `Arithmetic.Euclid.induction` matches the exact source schema, with recursive premise guarded by `n ≠ 0`; the proof decreases the second argument using `Nat.mod_lt`. There is no circular or impossible premise. |
| Gcd equation and application | `gcd_equation` uses the source's second-argument orientation. `gcd_common_divisor` actually uses the new induction rule; its concrete divisor example supplies satisfiable premises. The `(0,0)` case is retained. |
| E/T cost rules | `Resources.CallCount` supplies measured-value laws for zero-cost primitives, argument evaluation, function-entry charging, let, if and selected case arms. Their stated scope is an algebra of observations, not a verified source-to-cost compiler. |
| Append cost recurrence and exact count | `appendRun_nil`, `appendRun_cons` and `appendRun_exact` supply the source equations and `length + 1`. The actual existing `TreeFlattening.appendWithCost` recurrence was inspected: its cell count is converted by one final-call charge rather than silently equated with the source count. |
| Naive reverse equations and result | `naiveRun` explicitly recursively reverses the tail and appends the head. `naiveRun_value` proves ordered-list equality with `List.reverse`; it does not attribute the naive cost to Lean's optimized reverse implementation. |
| Naive reverse cost recurrence | `naiveRun_cons_cost` counts the recursive tail computation, separate append call count and one current entry. The empty cost is one. |
| Exact-cost exercise | `naiveRun_double_cost` proves `2*T = (n+1)*(n+2)`; `naiveRun_cost` derives exact natural division. This proves the triangular formula without an unproved rounding or parity assumption, including `n = 0`. |
| Quadratic bound | `naiveRun_cost_le` gives precisely the source's `(n+1)^2` bound for all finite inputs. |
| Accumulator equations, correctness and cost | The actual existing `SymmetricCosts.reverseRun`, `reverseRun_value` and `reverseRun_work` were inspected. They exactly supply the source recurrence, `reverse xs ++ acc`, and `length xs + 1`, with an arbitrary accumulator. `accumulator_exact` combines them. |
| Empty-accumulator refinement and comparison | `realizations_agree` preserves list order and multiplicity. The non-strict cost comparison includes empty input; strict comparison correctly requires nonempty input. |
| Semantic/resource integration | Both erasure squares use existing interfaces. The continuation square has matching represented boundaries and uses bind to retain prior observations. Universal double-reversal clients and the cost-14 example exercise composition. |
| §§1.5.2–1.5.3 discussion | The source map preserves the conditional compiler/runtime/target boundary, the inlining zero-cost exception and the preference for explicit bounds. It makes no physical runtime or end-to-end compiler theorem claim. |

The Fibonacci and alias-pattern passages are syntactic illustrations; in
particular, Chapter 1 does not give Fibonacci base cases. Accounting for them
as syntax rather than adding an invented algorithm specification is appropriate.
The apparent intermediate append-cost inconsistency on page 7 is explicitly
identified, and the unambiguous final recurrence is used.

## Statement and assumption checks

- `let_rule` uses the actual returned value as the body's input. Conditional
  and sum-case rules count only the selected branch after the discriminator.
  Their additive assumptions do not introduce unnecessary commutativity.
- Reversal results quantify over arbitrary finite lists and universe-polymorphic
  payloads. They preserve ordered values and repeated occurrences.
- The fast cost is independent of accumulator length because the source model
  moves source elements onto the accumulator; it does not traverse the existing
  accumulator. This matches the inspected reused implementation.
- Natural-to-real subtraction retains `n ≤ m`; a separate example exhibits the
  truncated-subtraction discrepancy. Update-away retains inequality of keys.
  Multiset sums/counts retain repeated elements.
- `Resources.erasureSquare` changes only its universe signature, permitting
  lower-universe observations. The semantic contract and implementation are
  unchanged, and the old equal-universe instantiation remains representable.
  All-source compatibility remains a validation gate.
- The examples invoke the intended public general results. The independent
  length-three count is 10 versus 4; empty, singleton, distinct-label and
  nonempty-accumulator cases expose consequential boundaries.

No additional unresolved Chapter 1 source obligation or unjustified reduction
of the chapter's mathematical scope was found.

## Validation blocker SPEC-V001

**Status: unresolved, validation-only.** The required complete immutable-candidate
build and exhaustive audit have not yet completed in the evidence supplied to
this reviewer. The focused builds passed according to the handoff; the full
fresh check is still compiling project modules. Ordinary per-module axiom-print
output must not be mistaken for the final exhaustive audit.

To resolve: supply the successful final command result and preserved
`.lake/verification.json` matching the exact candidate, dependencies and compiler.
The coordinator/caller must also perform the prescribed final candidate identity
verification before acceptance. If the candidate changes, review the entire
updated candidate against the same base while retaining this assessment and
any later findings.

No duplicate full build or mutation of the candidate was performed by this
reviewer. This report can reuse its unchanged-source analysis when matching
complete validation arrives; it cannot currently be recorded as Passed.

## Reopening addendum: omitted cost-model comparison claims

Reopened on 2026-11-02 at the same base and candidate, after the root implementer
and source researcher identified statements missed by this initial review.
This reviewer independently reread the actual pinned Chapter 1 text, pp. 7–9,
and rechecked the candidate's call-count definitions, reversal results and scope
documentation. All three omissions below are confirmed. The source expresses
them in prose, but they are mathematical claims about cost models; whole-chapter
coverage does not permit treating them solely as contextual discussion.

The existing explicit reversal, append, induction and standard-library findings
above remain valid. The correction concerns additional source completeness.
The truly external compiler/runtime/hardware running-time claim remains
conditional; none of these findings requires a verified hardware stack.

### SPEC-001 — Missing fixed-program fine/coarse cost comparison

**Severity: major; status: unresolved.**

Source: §1.5, printed p. 7, and §1.5.2, p. 9. The source claims that counting
primitive operations, constructor calls and variable accesses as well as
nonprimitive calls changes the cost by only a constant factor for a fixed
program under the stated local-work assumptions.

Candidate evidence: `Applications/Resources/CallCount.lean` provides `tick` and
compositional equations only. `ListReversal.lean` compares two algorithms within
one call model, not two tariffs for the same execution. Existing
`Resources.reweight_bound` requires a bound already supplied by a caller; it
does not establish this fixed-program comparison. The scope map's resource
discussion has no corresponding comparison witness.

Required remedy: define the two observations on the same supported executions
and prove a **uniform** comparison such as `coarse ≤ fine ≤ K * coarse`.
`K` must depend on the fixed finite program or its finite local tariffs, not be
chosen anew from the completed input trace. Retain explicit coverage of local
work by charged entries, and derive the global inequality from bounded local
work and composition. One sufficient model labels each charged entry by a
member of a fixed finite family of equation bodies and counts its primitive/
variable overhead in addition to the entry; finite maxima then supply `K`.
If state-dependent local work is allowed, its uniform bound must be an explicit
local contract rather than the desired global cost conclusion.

Establish the standard constant-factor/Big-O consequence using existing
resource/asymptotic interfaces where applicable. Retain a meaningful varying
execution example and an example or explicit limitation showing why uncharged
unbounded work defeats the conclusion. A hypothesis that merely states the
desired whole-run inequality would not resolve this finding.

### SPEC-002 — Missing justified removal of a nonrecursive entry charge

**Severity: major; status: unresolved.**

Source: §1.5, printed p. 8, claims that dropping the nonrecursive `+1` leaves
the asymptotic cost unchanged, with a zero-cost exception.

Candidate evidence: the source-map row for nonrecursive inlining specifies use
of `bind`/`pure` without `tick`, and its boundary paragraph mentions the zero
case. Neither `CallCount.lean` nor the retained examples proves a comparison
between the original and uncharged models. `tick_cost` gives the arithmetic
definition of the charge, not its invariance conditions.

Required remedy: for natural counts prove both `T ≤ T + 1` and
`T + 1 ≤ 2 * T` under `0 < T`, then retain a family-level constant-factor or
standard Big-O consequence with the appropriate **eventual positivity**
hypothesis. The guard must not be weakened to merely “T is not identically
zero”: a cost family with infinitely many zero values can violate the forward
Big-O comparison. Preserve a checked zero case demonstrating that a positive
constant cannot be bounded by any constant multiple of zero. Connect these
facts to the measured `tick` convention and to a satisfiable positive-cost
client. The conclusion must state the model/domain on which entry omission
is justified.

### SPEC-003 — Missing qualified lazy-demand upper bound

**Severity: major; status: unresolved.**

Source: §1.5, printed p. 7, says the call-by-value count also upper-bounds lazy
evaluation, potentially loosely.

Candidate evidence: `if_rule` and `case_rule` select a branch within one
measurement. There is no second demand/shared evaluation model, simulation,
or theorem comparing its call count to an eager evaluation. Dropping an
inactive branch is not by itself a proof of the source's lazy-evaluation claim.

Required remedy: supply a bounded, explicitly qualified shared-demand model
or simulation that relates demanded computations to a finite terminating eager
evaluation. Relevant hypotheses must preserve requested observations, align
the charged call events and prevent charging a shared demand repeatedly.
Derive the count inequality from this structural relationship. A defined
demand/pruning relation with a proved event injection, or an equivalent
certified shared schedule, is sufficient for a stated fragment; an assumption
of the final numerical inequality is not. An otherwise unexplained arbitrary
subset/subtrace assumption must not be presented as an evaluation theorem.

Retain cases with unused expensive work (strict saving), repeated demand of
the same shared computation (at most one charge), and a real demanded result.
State the boundary from nonsharing call-by-name, whose repeated evaluation can
increase work. Cache lookup, heap management and runtime overhead remain
outside the source's nonprimitive-call count unless separately modeled.
This is not a demand for a general compiler/runtime semantics proof.

## Revised acceptance requirements

The source map must add checked witnesses for these comparisons and remove
the categorical statement that the remaining discussion contains no additional
algorithm theorem. A scoped addendum may refine the bounded models and checked
clients, but it must preserve the original whole-chapter requirement and must
not close these findings through weaker proof-shaped assumptions.

All three findings need review against the replacement immutable candidate.
`SPEC-V001` remains separate and must be matched to that candidate's required
validation. Passing validation for `1aabd512...` cannot approve a later repair,
nor can it turn this source-incomplete candidate into an accepted chapter.
