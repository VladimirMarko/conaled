# Chapter 1 cost-model repair: author statement review

Recorded 2026-11-02. This is an implementation-side statement review, not an
independent Standards or Spec approval. The source draft is uncompiled at this
record's creation. Candidate identity and later validation belong in the
separate candidate record and retained review loop.

Requirements: `chapter01-cost-model-requirements.md`, SHA-256
`1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1`.
The original Chapter 1 requirements and original review base remain in force.

## Intended observations and independent calculations

Each fine-tariff event contains the original entry unit and its nonnegative
local extra charge. For an append input of length n, there are n cons events
and one terminal event. The specified local extras 4 and 1 therefore give
`5*n+2`; the original count is `n+1`. At length three these are 17 and 4.
The empty input gives 2 and 1, including at the empty payload type. A zero
extra tariff recovers list length, including for an empty event trace.

For a positive natural body count T, `T+1 <= 2*T` follows from `1 <= T`.
For zero body cost no multiplicative bound can absorb the positive entry.
The input family that is zero at even n and n at odd n is nonzero at 1 but
still has arbitrarily large zero inputs. It cannot satisfy the forward Big-O
comparison. These expectations precede the proofs and are not weakened to
make an implementation pass.

Shared demand is observed through the actual option-cache transition. Five
requests for the same cost-3 callback charge 3. A separate cost-1000 callback
that is not demanded remains uncached and contributes 1000 to remaining work.
Two distinct identities with equal payloads still charge 3+5 on their first
requests; equality of payloads is not a sharing relation. Repeating a stored
identity after arbitrary intervening requests still incurs zero callback
work. Shared and unshared recursive duplication both return `2^n`, while their
counts satisfy respectively `S(0)=1, S(n+1)=S(n)+1` and
`U(0)=1, U(n+1)=2*U(n)+1`. Thus depth four has value 16 and counts 5 and 31.

## Statement assessment

| Claim family | Premises and intended conclusion | Assessment |
| --- | --- | --- |
| Fine versus coarse trace | One natural local tariff; each occurrence charged separately; bounded by a fixed K | Lower bound unconditional; upper bound derived by induction from local bounds, not assumed on total work |
| Fixed program catalogue | All actual event identifiers belong to one finite catalogue | Its finite supremum fixes K independently of the input trace; no finite payload type or payload equality is required |
| Asymptotic tariff comparison | Input family and filter arbitrary; one K precedes the eventual local-bound premise | Both directions use standard real-cast Big-O; zero traces remain valid |
| Append connection | Actual measured append count equals the branch trace length | Exact tariff and factor-five client consume the general results; arbitrary and empty payloads retained |
| Omitted entry | A natural body observation and an actual `CallCount.tick` | Pointwise upper bound requires positivity; family upper bound requires eventual positivity; reverse direction unconditional |
| Zero counterexamples | Zero cost, then a non-identically-zero intermittent family | Both refute the unsupported multiplicative conclusion; the family proof uses an even input after any proposed cutoff |
| Cache request | Fixed pure callback, stable identity, ordinary option cache | A miss stores and charges the callback; a hit preserves the cached payload and adds no callback work |
| Validity and demanded value | Empty cache valid; transitions preserve validity | Every next request after an arbitrary prefix returns its pure/eager value; validity is separate from the work law |
| At-most-once charging | A stored identity is preserved through arbitrary intervening requests | Repetition uses the same entry; distinct identities remain distinct even when payloads coincide |
| Eager catalogue bound | Finite identity catalogue, nonnegative natural work | Exact local remaining-work conservation telescopes through existing `run_potential_exact`; final bound is derived, not a hypothesis |
| Duplication contrast | Actual cache requests, a single eager bind, and two unshared binds | Same demanded values and different derived recurrences; no inference about host-language cost semantics |

Identity equality is local to cache update operations. Finiteness occurs only
in the catalogue accounting section. Payload equality, order and inhabitance
are absent. The empty-catalogue case also has empty payload type. The callback
is a `Unit` thunk so its invocation boundary is explicit, although the
measured work remains the defined mathematical observation rather than a
measurement of Lean's evaluator.

The constant-per-equation argument requires that local body work is assigned
to an enclosing charged entry. An actual user-function execution includes a
root entry before optional inlining. Work with no charged entry needs an
additional boundary or coverage argument. Unbounded primitive work is not
covered merely by calling its operation primitive.

The eager sum is a model specification. Applying it to an external source
program requires a correspondence between identities and eager computations,
stable requested values, and equality of the catalogue observation with that
program's eager count. Cache administration is outside the callback-work
observation. Neither this correspondence nor a whole-language or physical
execution stack is silently postulated.

## Pending evidence

No compiler was started while the old frozen full gate remained active.
Elaboration, exact inferred signatures, connected examples, source-policy and
public-coverage checks, full candidate build, exhaustive axiom audit and both
independent final review axes remain required. The old candidate's validation
cannot validate these new modules or close SPEC-001/002/003.

Potential elaboration risks identified during static inspection include
finite-sum decomposition, simplification through nested projections and
function updates, real-cast norm simplification, and structural recursion
through delayed child computations. These are validation tasks, not known
mathematical counterexamples or permission to weaken the statements.
