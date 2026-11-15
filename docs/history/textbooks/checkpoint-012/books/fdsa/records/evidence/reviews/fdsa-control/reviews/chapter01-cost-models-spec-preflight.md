# Chapter 1 cost-model repair: independent Spec source preflight

Recorded 2026-11-02 by the retained independent Spec reviewer
`/root/chapter01_review/spec`.

**Outcome: source-preflight no finding.** This is a narrow statement/source
preflight, not a final Spec approval. SPEC-001, SPEC-002, SPEC-003 and the
separate validation blocker SPEC-V001 remain unresolved. No supplemental
finding is assigned. The earlier review and its correction remain unchanged.

## Identity and scope

- Original review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Previous candidate: `1aabd512284fe86254278ac631eda061d311050b`.
- Inspected repair commit: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Checkout: `conaled-ch01-cost-models`; HEAD matched that commit and the working
  tree was clean at the read checks.
- Frozen addendum: `chapter01-cost-model-requirements.md`, independently
  rechecked SHA-256
  `1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1`.

The original frozen requirements remain in force. This pass reread the actual
pinned Chapter 1 source on printed pp. 7–9, the addendum, the retained findings,
the author statement review and candidate handoff. It inspected the four new
Lean modules, the call-model explanation, the reconstruction-map correction
and the public-import additions. It assessed only mathematical adequacy of
the three repairs; it did not repeat the earlier whole-chapter review or
evaluate pending build logs.

## Statement/source assessment

### SPEC-001: uniform tariff comparison

`CallCount.refinedCost` counts the original entry and a natural extra charge
for every occurrence of the same list. Its lower bound does not require
positivity. `refinedCost_le` derives the upper bound from the local premise;
`catalogue_refined_bounds` fixes the constant using one finite catalogue's
supremum, independently of the trace. The family theorem places K outside the
eventual input quantifier. Both standard real-cast asymptotic directions are
present, including empty traces and zero extra tariffs.

`appendEvents` has the required cons and terminal equations.
`appendEvents_cost` connects its length to the existing measured append
observation; `append_refined_exact`, `append_refined_bounds` and
`append_refined_isBigO` connect the illustrative `5*n+2` tariff to the general
public results. The duplicate-input and empty-payload cases are retained.
The documentation explicitly requires local-work/charged-entry coverage,
accounts for the root boundary and excludes unbounded uncharged primitive or
callback work. It does not substitute the desired total inequality for a
structural premise or require finite payloads.

### SPEC-002: omitted entry and zero exceptions

The pointwise laws retain natural counts and the explicit `1 <= T` premise
for `T+1 <= 2*T`; the reverse inequality is unconditional. The premise is
satisfiable and is not weakened to being nonzero somewhere.
`tick_cost_comparison`, the generic measured-program client and the retained
`tick_value` connection identify the actual operation and unchanged values.
The asymptotic forward law requires eventual positivity in an arbitrary
filter, while its reverse direction has no such requirement.

The zero example and `intermittent_entry_not_isBigO` cover the consequential
exceptions. The latter family is nonzero at 1 and still has a zero input after
every proposed natural cutoff. The documented conclusion concerns one entry
at the stated boundary; it does not claim a transitive inlining theorem.

### SPEC-003: shared demand and bounded eager comparison

`SharedDemand.request` is an actual option-cache transition: a miss computes,
stores and charges the fixed pure callback; a hit returns the stored value
with zero additional callback charge. Empty-cache validity, preservation and
the arbitrary-prefix demanded-value theorem link these observations to the
same callback values. Stored identities are preserved through intervening
requests, so repeated demand is structurally accounted for.

The cost conclusion is derived from exact local remaining-work conservation
and the existing executor's potential theorem. Nonnegative natural weights
yield `run_cost_le_eager`; no desired total-cost inequality is assumed. Cache
validity is kept separate from this accounting law. Finiteness applies only
to the eager catalogue, identity equality only where cache operations need
it, and payload equality/order/inhabitance are absent. Empty requests and an
empty catalogue with empty payload type are represented.

Connected cases exercise repeated cheap demand, skipped expensive work,
preserved demanded values and equal values at distinct identities. The
duplication example uses actual shared requests and unshared measured binds.
`sharedLayer_eager` identifies the shared layer with one eager bind, while the
recursive families retain equal values and derive the different call counts.
These are not merely unrelated numeric sequences named after evaluation
strategies.

The eager sum remains an explicit catalogue specification. Applying it to an
external program requires a correspondence between requested identities,
stable observations and that program's eager cost. The source comments and
documentation state this boundary and exclude cache administration from the
callback-work charge. They do not assert a universal source-language
simulation or physical runtime comparison.

## Pending review boundary

The reconstruction map now explicitly corrects the earlier classification of
these mathematical source claims as explanatory scope. It continues to mark
the additions as unvalidated and preserves the legitimate compiler/runtime/
hardware limitation.

No build, compiler/gate/cache change, source mutation or Git mutation was
performed in this preflight. Source inspection cannot establish elaborated
signatures, checked proof terms, whole-project compatibility or exhaustive
axiom compliance. The repaired immutable candidate still needs matching
required validation and the retained independent final Standards and Spec
reviews, followed by final candidate identity verification. Validation of the
previous candidate cannot satisfy those gates for this repair.
