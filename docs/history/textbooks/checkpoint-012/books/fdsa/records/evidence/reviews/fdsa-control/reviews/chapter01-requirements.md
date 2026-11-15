# FDSA-001 — Chapter 1: Basics

State: active. Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, printed pages 1–10.
Depends on: FDSA-ENV, FDSA-SOURCE.

## Acceptance checklist

- [ ] Map the source's total functional language, types, notation, pattern
  matching, coercions, function update and multisets to existing Lean/Mathlib
  interfaces. Check meaningful examples, including truncated natural subtraction
  versus integer/real subtraction and multiplicity-sensitive operations.
- [ ] Connect append equations and associativity to standard Lean List results.
- [ ] Establish the stated gcd computation-induction schema with its nonzero
  branch premise and termination argument; retain a meaningful specialization.
- [ ] Represent the source's call-count rules for values/primitives, calls,
  conditionals, case and let using existing compositional measured operations.
  State the bounded scope and the optional omission of a nonrecursive call tick.
- [ ] Match append call-count recurrence; prove exact cost length + 1.
- [ ] Instrument naive reverse according to the source recurrence, prove erasure
  to List.reverse, prove the quadratic upper bound, and solve the exact-count
  exercise (triangular count).
- [ ] Reuse or implement accumulator reverse, prove arbitrary-accumulator
  correctness, exact cost length + 1, and empty-accumulator refinement.
- [ ] Connect both realizations to conaled's resource and semantic interfaces;
  retain a client that compares their distinct counts for the same output.
- [ ] Identify conditional runtime assumptions and asymptotic discussion as
  explanatory scope; do not assert machine-runtime theorems absent a target model.
- [ ] Complete per-claim statement review and meaningful checked examples.
- [ ] Integrate modules into public import coverage and exhaustive proof audit.
- [ ] Capture immutable candidate and pass applicable project verification.
- [ ] Independent Standards review: no unresolved findings.
- [ ] Independent Spec review: no unresolved findings.
- [ ] Verify accepted candidate identity, update local tracker, create/upload
  checkpoint, then advance to Chapter 2.

## Reuse assessment (provisional)

`Resources.Measured`, `Resources.bind`, `Resources.pure`,
`Resources.erasureSquare` are the existing observation/composition vocabulary.
`Resources.SymmetricCosts.reverseRun` appears to implement the exact accumulator
reverse and call-count recurrence. The tree-flattening append helper counts
copied cells rather than calls, so its raw cost cannot substitute for the book's
length + 1 count.

## Validation and review

Not yet run. This ticket is not complete.
