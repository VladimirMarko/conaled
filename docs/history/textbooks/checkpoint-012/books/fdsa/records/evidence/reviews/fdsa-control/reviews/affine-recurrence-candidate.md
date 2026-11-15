# Shared affine recurrence candidate handoff

Recorded 2026-11-02. Implementation draft; no unit or chapter acceptance.

- Unit starting base: `c28ba71863d2a35ee1c3a089caa90464e4cca692`.
- Candidate: `d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2`.
- Branch/worktree: `work/fdsa-affine-recurrence` / `conaled-affine-recurrence`.
- Commit: `feat(resources): bound contracting scalar recurrences (#174)`.
- Frozen exact requirements: `affine-recurrence-requirements.md`, SHA-256
  `5873700a349c359d15873829f1399a20225fa80eaa980e7ad9f1e4c8f774dd02`.

The starting shared base and repaired Chapter 1 candidate remain unaccepted.
This branch extends the shared foundations without containing the separate
Chapter 1 cost-comparison repair. Reconcile it with the eventually accepted
Chapter 1 and shared integration before presenting a full immutable candidate
for the retained independent review loop. Preserve all earlier findings and
validation limits; changing the integration base is not a resolution of them.

## Contents and author statement review

The new `Resources.AffineRecurrence.exists_affine_bound_of_two_branch` proves
one nonnegative slope/intercept pair for all natural inputs from fixed
recurrence data. Its scalar assumptions are `CommRing`, `LinearOrder`,
`IsStrictOrderedRing` and `Archimedean`. It assumes an eventual strictly
contracting sum of the two natural child sizes and an affine upper recurrence.
It imposes no monotonicity or sign premise on the scalar function and no sign
premise on its affine toll coefficients.

Root inspected the complete proof. The first Archimedean witness chooses an
enlarged cutoff with `2*K <= (1-rho)*N`, containing the original cutoff and 1.
The finite supremum includes every input through N, including zero. The second
witness chooses a nonnegative slope using the positive toll parts and a
nonnegative intercept. Above the cutoff, the doubled size inequality proves
each child strictly smaller before natural induction is invoked. Explicit
multiplication monotonicity supplies the absorption inequality; the final
polynomial combination has the required direction and constants. No final
growth bound is assumed as a premise.

The quarter-size scalar client has a separate terminating definition at its
own cutoff, actual branch equations and independent expected values
`1,1,5,7,19,31` at `0,1,2,4,8,16`. Its rational specialization discharges the
rounded child-size premise through `Nat.div_mul_le_self` and the recurrence
premise through its actual equation. The integer client `f(n)=-n-1` uses zero
children and toll `1-n`, with a negative base and valid equality recurrence.
It exercises the absence of a field or nonnegative-function assumption.

Separate examples retain a negative square's one-sided bound and an
absolute-value observation. They claim no signed Big-O theorem. The parameter
family `f(p,n)=p` applies the generic theorem separately to each p, then refutes
constants uniform over all p at n=0. Both natural and integer coefficient
boundaries are retained. These are meaningful satisfiable uses, not a vacuous
application under contradictory contraction premises.

The source map and dedicated notes preserve all later source-specific work:
exact ceilings and negative offsets, sharper C03-041/042 constants with their
possibly negative intercept, actual selector cost correspondence, grouping
and the noncontracting halving counterexample. No chapter is activated by
this generic theorem, and no proposed algorithm gains termination merely
from the proof's enlarged cutoff.

## File identities and validation

| New file | SHA-256 |
| --- | --- |
| `Applications/Resources/AffineRecurrence.lean` | `0f867ba6fa96cbeaaaeeba6c4a24cc71b38fdbf798b684d484234eabb283d17d` |
| `Examples/AffineRecurrence.lean` | `eb9239f5810887ba988420c3fe8538eab21285c1e6173eb5467133baa63868d5` |
| `docs/research/fdsa-affine-recurrence.md` | `a07b086bc846c0898b2713a7b055b9cb451d0471c655eeaab9cc1077f32b87bf` |

The contributor checked the actual pinned arithmetic, cast, finite-supremum
and Archimedean APIs. Root added `Examples.AffineRecurrence` to the public
application root and a separate reconstruction-map section. The five-file
commit is clean, and `git diff --cached --check` passed before committing.

No Lean compiler, focused build, full candidate check or axiom audit ran for
this unit. Generic arithmetic tactic applications, the well-founded definition
and equation rewrites still require elaboration. Source inspection and file
checks are not independent Standards/Spec approval. Keep compilation serial
with the existing frozen full gate; later validation must cover the final
integrated immutable candidate and both retained review axes, followed by
immediate candidate verification before acceptance.
