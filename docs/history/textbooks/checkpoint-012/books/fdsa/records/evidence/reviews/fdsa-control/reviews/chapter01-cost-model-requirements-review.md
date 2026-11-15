# Chapter 1 cost-model addendum — independent Spec assessment

Assessed on 2026-11-02 within the retained Chapter 1 review loop.

Requirements document:
`chapter01-cost-model-requirements.md`.

Verified SHA-256:
`1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1`.

Original review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Source-incomplete candidate: `1aabd512284fe86254278ac631eda061d311050b`.

## Outcome

The frozen addendum specifies an adequate bounded repair for **SPEC-001,
SPEC-002 and SPEC-003**, provided the implementation supplies the stated proofs,
connections and qualifications. No additional scope expansion is required.

This is a requirements-sufficiency assessment, **not implementation approval**.
All three source findings remain unresolved. SPEC-V001 remains separate and
must be evaluated against the eventual repaired candidate. No build, source
mutation or candidate re-review was performed for this assessment.

## SPEC-001: fixed-program tariff comparison

The required observation uses the same finite trace of charged entries for both
costs, adding nonnegative local work to produce the refined count. Requiring one
uniform local bound K, and additionally deriving K from a finite catalogue of
fixed-program body cases, addresses the quantifier-order risk. The intended
conclusion is uniform over arbitrary input traces; it is not a per-input
constant chosen after seeing the run.

The requirement to assign local work to an enclosing charged entry is
substantive. It prevents an apparently general theorem from silently ignoring
uncharged work or applying after every entry tick has been erased. The source
still needs explicit bounds when local arithmetic, callbacks or primitives can
do unbounded work. No finite payload type is required by the proposed model.

The append connection is well chosen: its independently specified branch trace
has n cons events and one terminal event, so its coarse count must match the
existing n+1 result. The illustrative local overheads produce 5*n+2, which
must be connected through the generic comparison theorem. The explicit label
of this tariff as illustrative prevents a false compiler-instruction claim.

The requested two-sided real-cast asymptotic comparison preserves the source's
constant-factor meaning and reuses the established mathematical interface.
Empty traces and zero extra tariffs provide relevant boundary cases.

## SPEC-002: nonrecursive entry omission

The pointwise inequalities and eventual-positivity hypothesis precisely repair
the omitted condition. Natural positivity gives the fixed factor two;
the reverse upper bound needs no positivity premise. The measured tick/value
connection ensures this is a comparison of the actual modeled boundary rather
than detached arithmetic.

The zero counterexample and alternating family are particularly useful. The
second demonstrates that excluding only the identically-zero function is
insufficient: an unbounded family can still have zero values cofinally, making
its unit-added family fail the stated Big-O comparison. The arbitrary-filter
formulation is appropriate; the counterexample's at-infinity filter supplies
the nontrivial setting for failure.

The addendum correctly prevents the single-tick theorem from being advertised
as a proof about transitively inlining arbitrary families of definitions.

## SPEC-003: qualified shared-demand upper bound

The planned option-cache request operation is a real bounded execution model.
It computes a pure measured callback on a miss and stores its value; a hit
returns that value without charging the computation again. Consequently the
at-most-once property can be derived from transitions and invariant preservation.
A remaining-work potential then gives a principled total-cost bound. The
required inequality is not assumed as a premise.

Separating validity, value agreement and cost accounting prevents a degenerate
model from satisfying a small cost merely by dropping requested results. Stable
computation identities and nonnegative work make the potential argument
meaningful. Empty catalogues, empty request sequences and repeated demands
cover relevant boundaries. Identity equality/finiteness assumptions stay local;
none belongs on payload values merely to implement a cache.

The external-program correspondence is an essential limit, not optional prose.
The finite catalogue's cost is an eager-catalogue specification. Applying the
result to an external program requires establishing that requests identify its
catalogue computations, values are stable, and this catalogue observation
matches the eager source count. The cache theorem alone must not be reported
as a simulation for every program of an unspecified lazy language.

The source's nonprimitive-call count omits cache lookup/update administration.
The addendum retains that distinction and avoids inferring physical running
time from a reduced callback count. It also correctly distinguishes shared
call-by-need from unshared call-by-name.

## Implementation assessment constraints

The addendum already contains the necessary obligations. The later candidate
review should apply these clauses strictly:

1. A finite local-tariff bound must be uniform over executions, with local
   coverage explicit. A whole-run bound restated as a hypothesis is insufficient.
2. The eager denominator of the shared-demand theorem must remain explicit.
   A catalogue sum should not be renamed the count of arbitrary source
   evaluation without the required correspondence proof or assumption.
3. The duplicated-let example must connect its n+1 versus 2^(n+1)-1 recurrence
   to a concrete measured computation or a clearly specified checked recurrence
   model with the same demanded observations. Merely attaching eager/shared and
   unshared labels to unrelated natural-number sequences would not satisfy the
   stated connection requirement.
4. The source map must describe the three comparison results and their exact
   assumptions, while preserving the source's separate exclusion of an
   end-to-end compiler/runtime/hardware proof.

These are acceptance interpretations of existing clauses, not new requirements
or a request to enlarge the model into a general programming-language semantics.

The opening statement that the addendum “resolves” the omissions is understood
as specifying their repair requirements. Its final completion section correctly
states that neither the document nor a source preflight accepts a chapter; no
finding is closed by this assessment.
