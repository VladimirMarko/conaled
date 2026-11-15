# Drift elaboration correction 1

Candidate `f535b1ef557795c4e09c97ce0daf599961c9b268`, tree `e542b3e09015cebeb3376fbc8903fe738fec72e4`, parent `eec2172f7296b6bfcd13533aadb68bd9d11c4a32`.
Branch `work/fdsa-ch03-random-selection`; clean worktree.
Commit `fix(selection): use pinned drift monotonicity APIs (#174)`.
This is a bounded proposed correction for **C03-RANDOM-DRIFT-ELAB-001**, not a
successful compiler check or finding closure. All eight source files and own
provenance are held for the root's actual focused result or explicit release.

## Actual failure retained

The complete first drift log, closure and terminal were read in `dc5845`.
Root owned76550 closed with actual exit1, terminal `cc94c2`, root reconciliation
`f0abdd`. The outer log is14,088 bytes with SHA-256
`e05fc02253486963d308354dc4a9d1a8a38da85c4467d13b9ccf964da5423e6d`;
the native log is13,804 bytes with SHA-256
`4302937b02b7dfea31b7042ad5d93074d524abef2290225c8a6e010565cfb0e7`.
Their exact containment, actual exit and failed candidate were checked before
source mutation. All14 failed-run records and109 earlier author records remain
unchanged. No historical execution session was polled.

## Exact correction and statement review

Only `Applications/Resources/RandomSelectionDrift.lean` changes: six inserted
and five deleted lines. Pinned Mathlib primary source was read in `5e3dc9`.
Its `mul_le_mul_right h a` proves `a*b <= a*c`; the additive analogue is
`add_le_add_right`. The opposite additive name appends a common right summand.
The correction therefore changes four multiplicative proof references and
three corresponding additive references in the drift, scan and source proofs.
No algebraic inequality, recursive child, constant, case or executable operation
changes. The actual recursive call and `stepRun_child` termination proof remain
verbatim; prior cascading no-goal/termination diagnostics remain in the evidence
and are not declared resolved before the next actual compiler result.

One private helper changes its implicit context: local
`omit [LinearOrder α] in` removes the unused order instance from
`filter_length_eq_card_indices`. Its generic list/Bool-filter proposition and
proof body are unchanged. This is **not** exact actual private-type preservation.
The other14 authored private contexts remain unchanged. All139 public declaration
header texts and contexts remain unchanged; their actual successor elaborated
types still require root output. No linter is suppressed.

All seven other sources are byte-identical, including all six earlier passing
sources and the entire drift example file. The complete source/case read is
`a6b1d8`. Preserved expectations cover sizes0..5, stable/uniform duplicate ranks,
all-rank singleton continuation0, actual duplicate sizes1,1,0 with mean2/3,
upper9/4, chosen child1 versus larger side3, arbitrary and valid expected bounds,
and empty means0 and2. The current full139 public/15 private inventory, all
headers and the disclosure above are in `precommit-assessment.json`.
The actual stepRun/run/scanLaw/sourceLaw observations, all worker ranks, duplicate
handling and public one-based boundary are intact. No desired complexity law or
independence hypothesis is introduced. Tail, endpoint and all-equal families
are not added in this correction.

## Inputs for root validation

```text
lake build Applications.Resources.RandomSelectionDrift Examples.RandomSelectionDrift
```

`Statements139-correction1.lean` is the complete explicit-@ input, rebound to
this candidate and all eight exact source blobs. It is byte-identical to the
previous139 program:7,759 bytes, SHA-256
`11642119a2fafb69c23bc1e16d41fe82a34cc8d0319d7256eb6717bcaba35084`.
No author compiler, audit, type-program, runtime/cache/profile or dependency
action occurred. No actual successor type output or build pass is claimed.
The fixed whole-task review base remains
`2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Starting state was captured before editing in `6bc66e`. Exact source replacement,
all139 header checks, seven unchanged-file checks, all15 private inventory,
prior-evidence hashes and input binding passed in `414870`. The staged diff was
byte-identical to the recorded source diff, its whitespace check passed, and
local commit exited0 in `ddf54f`. This is source/provenance integrity evidence,
not Lean validation. Full candidate check/audit, independent Standards and Spec
reviews and immediate verification remain root-owned gates.
