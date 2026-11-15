# Set/Map refinement preparation: root readback

Recorded 2026-11-02. This is bounded source preparation only. No requirements
are frozen, no new shared unit is implemented, and Chapter 1 remains active.

Both report authors stopped writing. Root read both complete final reports
and checked their ordinary file identities:

| Report | Bytes / lines | SHA-256 |
|---|---:|---|
| `research/adt-refinement-api-preflight.md` | 28,486 / 445 | `4d63f2616dee5af5e358cc59696745f215698973517dad9d4d77c1310b09e391` |
| `research/adt-refinement-source-preflight.md` | 22,132 / 342 | `5db706e4afc85913cfd92c8aeace3de2e8aea174fe813b828aa9a30a3d1d8994` |

The reports agree on seven Set laws and six Map laws, with decoder and validity
separate from operations. Generic keys, values and states retain independent
universes; the contracts need no order, default value or global equality
decision. Bool membership reflects into Prop, while Map lookup is already the
decoder. Pointwise changed-key and unaffected-key clauses express the full
function update law without adding a global decidable-equality assumption.

Existing relational squares and composition already supply the required
preservation mechanism. A small valid-graph bridge may be useful; a new generic
ADT language or parallel refinement framework is not justified by these sources.
Composition must preserve the actual middle witness, middle operation agreement
and intermediate validity. The valid-graph composite has predicate
`I t ∧ J (decode t)` unless redundancy is separately proved. Ordinary argument
roles do not change merely because their underlying type equals the state type.

Exercise 6.2 requires both modify translations. Deriving modify from the original
update/delete operations and translating back recovers those raw operations by
reduction. The reverse direction generally recovers only lookup observations
and validity on valid states. The lawful hidden-counter example gives counters
one and two for the same observed result and refutes the stronger state equality.
No callback restriction `f none = none` or execution-cost claim belongs here.

The proposed connected cases retain nonempty two-key clients, a nontrivial even
counter invariant, two-stage composition with a separate true-tag predicate,
actual sequential validity transport, same-key and distinct-key updates,
absence and `none` versus `some false`, and Empty key/value boundaries. AList is
an available finite Map realization; its insertion order is not the source's
ordered-list algorithm. No concrete list/tree/map/heap/interval algorithm, cost,
balancing proof, direct Chapter 5 exercise or chapter acceptance is discharged
by these proposed contracts or examples.

No new compiler/checker, project hash helper, cache action, GitHub write or
chapter activation was performed for these reports. Session 83124 remains the
sole full Chapter 1 guarded run at candidate
`07e480f6ec9958d4975bb90151005b84f2907614`. The original initial Chapter 2
integration prefix `c80eec92f5458eccfd1c34c8314d666c2a1e3847`, all frozen
requirements, original review bases and unresolved findings remain unchanged.

## Completed case preparation and scope freeze

The case author subsequently completed and stopped
`research/adt-refinement-case-preflight.md`: 29,841 bytes / 466 lines,
SHA-256 `98bf8c5e68cb8eecbedbedfde8caf8ed1587c5219a0df8c2d794085ef9738e52`.
Root read all of it and confirmed that byte identity. It supplies the exact
nonempty client calculations, actual two-stage square route, two distinct Bool
omitted-premise failures, Nat role/product cases, both modify directions,
Empty/Option cases and a real AList adapter. A Nat AList initialized with a
third binding makes the all-three-steps unaffected-key clause nonvacuous.

The case note distinguishes invalid metadata from an actual semantic failure,
and keeps the lawful modify counter-one/counter-two witness at validity True.
The source author separately assessed the complete earlier scope draft and
found no concrete mathematical/source sufficiency issue within its explicitly
bounded scope. That assessment did not include a second read of the final
case report; root read the final case details and incorporated them in the
freeze. See `adt-refinement-requirements-assessment.md` for the limits.

Requirements are now frozen in `adt-refinement-requirements.md` for FDSA-XA01.
Source authoring still waits for the clean start record and successful pre-code
checkpoint. None of this changes Chapter 1, source acceptance, the first Chapter
2 prefix, or the sole full validation session.
