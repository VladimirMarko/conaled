# Paired journal transport task

This is the common mathematical task for both arms of the #534 pilot. The trial
has not started. `TrialTask.lean` fixes the data, native map and acceptance types.
The coordinator must freeze and review this bundle before releasing it.

A state consists of two finite lists of natural-number entries. The source
package starts with two empty journals and appends entry 1 to both journals at
each step. In the main construction, the dependent invariant says that their
lengths agree. Change the presentation by reversing each journal. The target
starts empty and prepends entry 1 to each journal. Its invariant is again
equality of lengths. The target is specified directly, independently of a
conjugation definition.

Transport the complete proof-bearing package along the exact native universe
path of `nativeMap` and the supplied `E : HomotopyEquivalence nativeMap`.
Construct a complete native package path and the actual selected filled section,
recover that section, and recover the native path through the fixed-equivalence
structure-identity correspondence. Decode the entire package and prove it equals
the independently specified target, including its dependent fields.

For the variation, keep the initial state, transition and presentation but change
the dependent invariant to equality of journal totals. Transport this complete
package too. This is a genuinely different predicate: journals `[2,3]` and `[5]`
have equal totals and unequal lengths, while `[2]` and `[3]` have equal lengths
and unequal totals. Both invariants are preserved by adding the same entry.

Reject the proposed `badTarget`: it has the correct initial point and transition
but replaces the invariant with `True`. Prove that there is no complete native
package path to it over the specified equivalence. A failed elaboration or
failure to find a proof is not a rejection proof.

Write `AuthorSubmission.lean` with declarations in namespace
`JournalTrial.Author`. Every declaration below takes the original supplied
`E : HomotopyEquivalence nativeMap` as its first argument. Prefix the main
construction's declarations with `main` and the variation's with `variation`.
Use `(p,q) = (sourceLength,targetLength)` for the main construction and
`(p,q) = (sourceSum,targetSum)` for the variation:

| Declaration suffix | Required type or equation |
|---|---|
| `Path` | `NativePath E p q` |
| `Section` | `Term (package (admittedLine nativeMap E)).family` |
| `Section_exact` | Submitted section equals `transported nativeMap E p` |
| `Section_recovery` | Submitted section equals `pullPackage (admittedLine nativeMap E) (admittedPresentation nativeMap E) (p.conjugate (admittedCarrier nativeMap E))` |
| `Decoded` | `StatePackage Journals` |
| `Decoded_exact` | Submitted decoded package equals `targetPackage nativeMap E p` |
| `Decoded_target` | Submitted decoded package equals the independently specified `q` |
| `Path_recovery` | `(uaStructureIdentity nativeMap E p q).symm ((uaStructureIdentity nativeMap E p q) (submitted path)) = submitted path` |

Also expose `reject E : IsEmpty (NativePath E sourceLength badTarget)`.
The namespace openings and implementation style are the author's choice.
`ExpectedInterface.lean` gives the exact checker against these names, for use
by both arms. The same private oracle will import each submission and check the
additional public observations below.

The declarations must work for the original arbitrary supplied `E`. Do not
replace it with `HomotopyEquivalence.ofIso`, or change the prescribed map, code
or native line. A caller may instantiate them with any admitted contraction
of that map; preserving the witness is part of the contract.

Authors may introduce and retain generic helpers. Independently proving a few
numeric observations without these native objects will not satisfy the
interface. The named declaration boundary avoids adding a new record around
native paths; it does not reduce the native contracts.

Independent acceptance checks full decoded records; initial state, transition
and invariant at every list pair; the two separating pairs above; the transition
at `([2,3],[5])`, which must produce `([1,2,3],[1,5])`; both native path endpoints;
both native section decodings and recoveries; exact native path recovery; and
the rejected dependent-field erasure. These observations are public acceptance
requirements. The checking implementation and feasibility solutions are private
until the trial ends.

Both arms may use every generic API accepted at the frozen baseline, including
#528, #530, #533 and #554, the public calibrations, ordinary Mathlib facts and
self-written helpers. The direct arm must not import or read the proposed
`Examples.CubicalAuthorTransport` facade or its facade-only calibration. The
facade arm may additionally use it. The coordinator supplies the same baseline
calibration bundle to both arms. Each author receives only the frozen repository
scope, this task, `TrialTask.lean`, `ExpectedInterface.lean`, their own submission workspace and the common
validation instructions. The private preparer directory, oracle, feasibility
solutions, other submission and orchestration notes are excluded.

Retain every attempted submission and compiler log. Report helpers, blockers,
repairs, assistance and unavailable telemetry. There is no task-specific token
ceiling or wall-time performance ranking. Questions go to the coordinator;
shared clarifications are recorded and sent to both arms. A correctness defect
in the frozen task, oracle or interface stops the affected cohort and requires
separate repair and review before a newly identified cohort begins.
