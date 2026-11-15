# Local1040 — complete Monitor's narrowed order imports

This is a correction within the existing Preface/Perm implementation and review
loop. No next chapter may start until that loop's acceptance checkpoint is
uploaded. No new enclosing review or formal-gate waiver is introduced.

## Starting state and actual failure

Starting candidate: cf0a687265c1929ffd3ff6f15fa18febe0fb61b5.
Fixed whole-task base: 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd.
Main conaled and isolated vfa-summation-validation are clean at that candidate.
The supplied unchanged kit's direct tty run completed actual execution-API and
kit exit1, with no timeout or recorder error, after936 successful modules.
SquareKit.Temporal.Monitor failed at937; no exhaustive audit or fresh verification
record exists. Full records: validation/1002-candidate-cf0a687-summation-fresh1;
summary: validation/1040-fresh-failure.json.

Earlier task work narrowed this file's Mathlib.Tactic import to Nat.Basic and
Omega. Its remaining body is byte-identical to the fixed baseline. The concrete
errors are missing LE.le.trans dot notation at58/59, a failed min-bound simp step
at123, and unknown lt_self_iff_false at176. This is not an unchanged-baseline
attribution. Earlier corrections passed complete modules603,665,931 and933 in
the failed run; those successes do not turn that run into integrated success.

## Required correction and bounded checks

Prefer the smallest explicit semantic import that supplies the existing proof
dependencies. Pinned Mathlib.Order.Basic defines the order alias and self-less-
than lemma; Mathlib.Order.Lattice additionally supplies LinearOrder.toLattice
and the lattice simp rules used by the min-bound step. Mathlib.Order.Lattice is
the current single-import candidate, subject to actual complete-source checking.
Retain all statements, hypotheses, constructors, executable recurrences, cases
and proof bodies if imports suffice. Do not restore the Mathlib.Tactic umbrella
or rewrite mathematics merely to suppress a dependency error.

Record exact source/commit identities and clean checkout state. Check the whole
corrected Monitor file and the remaining theorem-bearing consumers under the
same pinned kit with separate private diagnostic outputs. Determine their local
prerequisite closure using the unchanged checker's source graph. Include the
Verification module's diagnostic commands; exclude only the import-only public
aggregator when its closure would repeat the entire project. A static scan is
not evidence of compilability, and focused checks replace no integrated gate.
No diagnostic or old/fresh outputs may be copied into the managed project cache.

Re-derive candidate-specific direct external selectors and source/cache closure
evidence. If all newly named dependencies are already installed, retain that
fact and avoid unnecessary acquisition. Keep official compiler bytes, source
pins, checker, guard and hash-helper unchanged. The old4adc worktree remains
quarantined with descendant quiescence unknown; do not retarget, clean or signal
it. Only its stable shared dependency inputs are reused.

## Review and completion

Both retained independent axes review the complete fixed-base task scope for
the correction candidate, reusing unchanged source analysis and preserving all
findings. Standards' returned closure of ST-003 rests on the actual complete
IndefiniteService compilation at603, not on whole-run success.

A new complete fresh build and exhaustive audit are required after correction.
Then complete unchanged non-repairing artifact preservation/classification,
guarded build/postguard/audit with a distinct verification record, managed
ProofAudit prerequisite, all four regressions, both final evidence reviews,
immediate candidate verification, and the uploaded acceptance checkpoint.
All chapters remain unaccepted while these gates are pending.
