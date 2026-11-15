# FDSA-X002 — Shared insertion-sort call-count results

State: implemented with focused builds; complete verification/review pending;
integration blocked on FDSA-001 acceptance.
Triage: ready-for-agent. Parent: FDSA-000.

This is the user's authorized cross-cutting exception: the same measured
insertion-sort model and bounds are needed by Chapter 2 sorting and Chapter 3's
small-input selection base case. It does not activate or close Chapter 2.

Fixed review base: `1aabd512284fe86254278ac631eda061d311050b`.
Development branch: `work/fdsa-insertion-costs` in a separate worktree.
Candidate: `697bcf242ce65d74815b5639bddb1c6e754dd10f`.

## Exact scope

Source: FDSA §2.2, Exercise 2.1, and the later reuse by Chapter 3. Relevant items
C02-004–016, C02-099–100 in `../research/chapter02-obligations.md`.

- Instrument `List.orderedInsert` and the existing `insertionOn` recurrence;
  prove exact erasure, including the comparison's tie direction.
- Keep operations and cost bounds usable for arbitrary decidable relations
  where they do not need order laws. Add order hypotheses only for correctness,
  best-case or worst-case source specializations.
- Prove one-element insertion call count between 1 and length+1; exact count
  one when the inserted element precedes the head and exact length+1 when it
  precedes no input element.
- Prove insertion-sort lower bound 2n+1, triangular upper bound
  (n+1)(n+2)/2, and the chapter's weaker quadratic bound.
- Prove sorted-input count 2n+1 and reverse(range n) count
  (n+1)(n+2)/2, retaining empty and singleton cases and duplicates where allowed.
- Connect ordinary sortedness/permutation to existing contracts without
  introducing a new sorting specification or replacing existing algorithms.
- Retain meaningful checked examples and statement review, integrate public
  import coverage, and obtain required candidate verification and both
  independent review axes before integration/acceptance.

## Progress boundaries

Chapter 1 remains the active sequential chapter. This branch may develop shared
cost lemmas while its full candidate verification runs, but may not be merged
as accepted work before that prerequisite passes. Every checkpoint must include
its reachable commits and describe unaccepted work truthfully.

## Evidence

- Core focused build: `reviews/insertion-core-refined.log`, exit 0.
- Connected examples: `reviews/insertion-examples-refined.log`, exit 0;
  includes arbitrary payloads, tied-head short circuit despite a later failure,
  empty/singleton counts, attained extrema, repeated-value occurrence rank and
  the sorting-only budget of 21 calls for length at most five.
- An initial concrete reverse-range specialization needed an explicit
  definitional shape conversion; its corrected public-theorem application is
  checked. The general core statements and independent expected count of 10
  were unchanged.
- Independent architectural/mathematical preflight is saved in
  `research/insertion-cost-preflight.md`. Its three improvements were applied.
  This preflight is not the required final Standards/Spec review.
- Candidate source has no admission or new axiom; complete source-policy and
  exhaustive proof-audit gates are still required before acceptance.
