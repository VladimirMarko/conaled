# Rounded recurrence: complete-bound source candidate

Prepared 4 November 2026. **The two new modules are source-only and await root's
focused compilation. No actual-type, full-audit or acceptance credit is claimed.**
This continues the original C03-039–044 assignment and the enclosing full-book
review loop. All 83 Chapter 3 obligations remain in scope.

## Immutable candidate and preservation

- Candidate: `4e022bf16e793fd5a1f830b14ba30fb4a2dd0525`.
- Tree: `7d9c38079e6ab5f9045e6c0282f56af97caab227`.
- Parent: `a4cd1b6b53fdab38eab40433c3fd60293fdc054f`.
- Original full rounded-scope base remains accepted XR
  `c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5`.
- Branch/worktree: `work/fdsa-ch03-rounded-recurrence` /
  `conaled-ch02-natural-runs`, clean after the commit.
- Local commit: `feat(resources): complete sharp rounded recurrence bounds (#174)`.
  Command-local identity ChatGPT <chatgpt@openai.com>; actual command/readback
  tool `e2f385`, exit 0. The staged whitespace check also exited 0.
- Exactly two added paths: `Applications/Resources/RoundedRecurrenceBounds.lean`
  (6,949 bytes / 135 LF lines / SHA-256
  `1a9a67658233c4efb0c7ee03b28e334376db28fa6d1c816fbd9e6bebc427751f`)
  and `Examples/RoundedRecurrenceBounds.lean` (7,279 bytes / 162 LF lines /
  SHA-256 `549561d415dc3a97080c5a3df431a2beb583df32cde9c89798a411b4068e1683`).
- Both original rounded files and all 16 original authored statements are
  byte-identical. All 13 prior own provenance files remain unchanged, as do
  every other parent source path, accepted branch and original XR ref.
  No other author's branch or worktree was mutated.

The original slice1 focused pass was reported by root and its saved result,
owned terminal and complete-log identity were checked read-only by this author:
owned 52277, terminal `3e669a`, closure `67190b`. It covers the original two
modules at a4cd1b6, not the new modules, actual printed types or full Chapter 3.

## Full mathematical construction now present in source

`explicit_cutoff_bounds` proves that the exact source choice
`N = max n0 (Nat.ceil((max 0 b + max 0 d + 2)/(1-a-c)) + 1)`
dominates n0 and strictly exceeds the combined quotient. The elementary
ceiling statement itself needs no sign assumptions; the later contraction
hypotheses supply the required positive denominator.

`affine_bound_of_prefix` completes the sharp strong induction. It retains the
original recurrence above n0, n0 <= N, the exact strict cutoff, a genuine
finite-prefix bound by C4, and both non-strict source slope inequalities. It
derives slope nonnegativity from C1 >= 0 and contraction, uses the original
exact signed-offset child descent, and applies the original sharp step to
the two smaller-child induction hypotheses. All natural inputs, including
zero, use the same constants. There is no assumption that f, either offset,
the constant toll or the intercept is nonnegative.

`bound_with_source_constants` exposes the exact choices in its statement:
the preceding N; C4 equal to the actual `Finset.sup'` over the nonempty range
0..N; and C3 equal to the maximum of the two original quotients. In particular,
C4 is not replaced by `max 0 C4`, and the second denominator remains
`(1-a-c)*N-max 0 b-max 0 d-2`. This theorem discharges the prefix obligation
using standard finite-supremum membership, rather than postulating a desired
global affine bound.

`exists_affine_bound` hides those fixed source witnesses to give the complete
real Theorem 3.9. `exists_affine_bound_nat` casts the actual natural recurrence,
uses that real theorem, and rounds both witnesses upward with `Nat.ceil` and
`Nat.le_ceil`. It introduces no second induction, positivity restriction on
the real witnesses or restriction to sufficiently large inputs.

The scalar function is already total in these theorems. They do not establish
termination of a separate selector, attach costs to an extensional function,
or give a norm-based asymptotic bound for signed f. The original strict-sign
counterexample is retained unchanged; the sufficient slope remains non-strict.

## Connected propositions and independent expectations

The zero source-witness client uses the public exact-constant theorem; its
finite prefix maximum and two-quotient maximum both reduce to zero. The
negative-intercept client uses the complete sharp induction with f=-3,
C4=-3, C2=3 and negative offsets. A separate real-existence client uses
the actual constant function 3 with C2=-3.

The new scalar `roundedQuarter` is independently defined with base Q(n)=n+1
for n<=5 and otherwise
`Q(n)=Q(ceil(n/4))+Q(ceil(n/4))+n+1`. Its well-founded construction obtains
actual child decrease from the original public ceiling theorem before any
growth theorem is used. It is a noncomputable real-ceiling specification,
not an execution-cost claim. Its retained value proofs are Q(0)=1, Q(5)=6,
Q(6)=13 and Q(21)=48. The first recursive value distinguishes ceiling from
floor, and Q(21) uses the recursive child Q(6).

For this actual recurrence, N=5, prefix maximum 6 and slope 24 satisfy the
exact source constraints. The explicit bound Q(n)<=24n+6 is proved through
`affine_bound_of_prefix`. Separate real and natural existence clients consume
Q's same actual recurrence. Thus the complete witness and natural rounding
paths are exercised by an actual nonconstant recursively defined function.

The noncontracting boundary proves that, for a=c=1/2 and linear toll 1, no
fixed affine one-step estimate closes beyond any finite cutoff. It uses
the exact natural-ceiling children at even inputs. This is expressly an
obstruction to this induction step, not a converse claiming that every
noncontracting scalar recurrence lacks an affine bound.

## Source statement review and declaration inventory

The new pair has **19 authored public names: 18 theorems and one definition**.
Together with the unchanged first pair, the complete rounded source now has
**35 public names: 34 theorems and one definition**. There are no authored
private declarations, anonymous examples or instances. Generated declarations
from the recursive definition remain part of the later exhaustive audit;
these source counts are not kernel-audit counts or completion counts.

`statement-review.json` records quantifiers, domains, signed boundaries,
prefix/termination obligations, exact source constants and every connected
case. `statements35-inventory.json` binds all four source files and every
authored header. The two new theorem types containing local `let :=` bindings
are retained in full: the inventory identifies the declaration body delimiter,
not the first type-level `:=`. Every retained old header exactly matches the
original 16-name inventory.

The complete 297 new source lines were read back at `b89fa0` and `d1fdd4`.
This is author statement/proof assessment, not either independent review axis.

## Execution and integration handoff

Focused targets:

- `Applications.Resources.RoundedRecurrenceBounds`
- `Examples.RoundedRecurrenceBounds`

`Statements35-candidate1.lean` contains all 35 explicit-`@` checks, preserving
the original 16 first and adding the 19 new names. It uses the supported
full pretty-printer profile and no nonexistent `pp.maxDepth`. It remains
unexecuted; actual output completeness and input qualification are root/review
tasks. The original 16-name program is unchanged.

The natural API intended for the later F bridge is
`exists_affine_bound_nat F (1/5) 0 (7/10) 3 19 54 20`, after proving the
actual recurrence of F with those exact real-ceiling arguments. C03-045 and
C03-046 still require the actual F and measured-selector correspondences;
neither is supplied or accepted by this scalar package. Public-entrypoint
and final source-map integration remain with the complete Chapter 3 receiver.

No compiler, Lean/Lake probe, cache/hydration, runtime/profile/pin change,
GitHub mutation or push was executed by the author. Only Nix is waived.
The mandatory full integrated candidate check/audit, complete actual-type
review, both independent axes, immediate verification and exact acceptance
remain under the original workflow. All source is held for root feedback.

## Reading and preservation boundary

The full 510-line frozen inventory, all 559 lines of the proof plan, actual
book §3.5 through Theorem 3.10 at LF lines 1837–2035, relevant instructions,
the prior handoff/requirements/header inventory/bindings/receipt and pinned
ceiling/finite-supremum APIs were read. Old large Git-ref/action records were
structurally inspected and every prior saved payload hash was rechecked.
No fresh full-book or whole-Mathlib read is claimed. The design note and
baseline were saved before source edits; the original failures, reviews and
prior preparation remain intact.
