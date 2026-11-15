# Force-after-delay observations — local ticket 10014

## Ownership and current status

This is implementation within the existing suspension-foundation loop.
Root assigned the remaining focused-client chain after its active Relocation
r6 check: proof corrections in `Examples/SuspensionRelocation.lean` if needed,
then `Applications/Suspensions/ForceObservation.lean` and
`Examples/SuspensionForceObservation.lean`. Root retains the Relocation core,
its report, tracker, entrypoints, commits and acceptance decisions. No separate
review or implementation loop is opened.

The assigned chain is now green in focused checking. Relocation core passed
in root's r6 check, and its corrected concrete client passed in ForceObservation
r1. ForceObservation r2 passed the core and all its concrete clients with
751 jobs, exit 0, and unchanged queue/start/end input hashes. No source edits
were made after that successful check.
Earlier interrupted Relocation sessions supply neither success nor failure
evidence; root records them separately.

## Source and requirement boundary

The source distinction is recorded in
`session/research/suspension-foundation-inventory.md`, section 4.3: the book's
force-after-delay law observes ordinary results, exceptions and visible
effects, while allocation of a private suspension and additional forcing work
remain present in the operational model. Requirements 7 and 8 of
`session/requirements/suspension-foundation.md` require the concrete execution
connection and an explicit account of address renaming/private garbage.
Requirement 3 keeps stuck and unknown observations distinct.

The current comparison contracts concern finite normal and raised executions.
They do not assert a force/direct equivalence for stuck answers, finite unknown
budgets, divergence, or ordered event traces. Their extra transition counts
are explicit. The general Observation module separately retains unknown and
stuck states and records actual ordered events. Source typing and inherited
identifier classification remain separate from these raw runtime laws.

## Statement-level review before compilation

`FixedCells (shift memory.next) memory` requires all occupied cells to remain
unchanged when runtime addresses inside values and captured environments are
renamed. The separate `captured` premise requires the explicit initial
environment to be fixed. These conditions allow aliases and cycles through
old heap addresses. They exclude dangling addresses at or above the frontier
when the identical initial cells and environment are reused on the delayed
side. They are not assumptions about the eventual body result.

`Relocation.Equivariant` is an independent law for primitive operations.
It prevents a primitive from exposing the omitted private address in a way
inconsistent with the injection. The current clients use a primitive handler
that always returns the same primitive fault and perform their reference
effects through the actual core operations.

`delay_states_related` constructs the initial relation from bounded memory
and fixed cells. The injection fixes every address below the initial frontier,
shifts all later addresses by one, and leaves exactly that frontier address
outside its image. `delay_configs_related` additionally uses fixed captures.

`value_observed` and `raised_observed` transport an actual direct body run
through Relocation and then consume Derived's exact force-delay contracts.
They do not assume allocation leaves the body result literally unchanged.
The returned value or exception packet is renamed consistently with all
represented heap cells. Successful forcing writes the cache in the omitted
private cell; `MemoryRel.private_replace` preserves every represented lookup.
Exceptional forcing retains the body's reached memory, including earlier
effects, rather than introducing a rollback or a global unchanged-thunk claim.

`value_reflected` and `raised_reflected` unpack Derived's checked iff contracts,
transport the allocated-state body run backward, and retain the complete
reached direct answer and exact step relation. The orientation of the result
equalities and the normal-case final-memory rewrite matches those APIs.

The memory relation retains exception names and the shifted allocation
frontier as well as every represented lookup, including absence. A scalar
result equality alone would not supply these effects. The current statements
do not claim literal equality of full memories or exact resource traces.

## Independently expected connected cases

| Case | Direct steps | Force-after-delay steps | Expected observations |
|---|---:|---:|---|
| Write old reference, allocate and return a new reference | 13 | 25 | Old address 0 changes from 5 to 7; new reference 1 relocates to 2 and contains 9; final forced frontier is 3. |
| Write old reference, then raise | 13 | 23 | Address 0 contains 7; packet is exception 2; exception-name set remains `{0,1,2}`; final forced frontier is 2. |
| Dangling capture outside the fixed-environment domain | 3 | 10 | Direct read faults with `missingAddress 0`; forcing first allocates thunk 0 and then faults with `expectedReferenceValue`. |

For each direct effectful body, nine transitions perform the binding's
reference assignment and enter its continuation. The normal continuation
takes four further transitions to allocate and deliver the new reference.
The raising continuation likewise takes four transitions to deliver the
packet. Derived contributes twelve extra transitions on normal completion
and ten on raised completion. These are counts of the explicit machine steps,
not host-time measurements.

The normal and raised reverse clients use determinism against these direct
runs to recover the exact returned value/packet and total count. The dangling
case is a deliberate raw-state counterexample: bounded empty memory alone
does not justify reusing a captured address that the new allocation occupies.

The current dangling case discriminates the explicit-environment premise.
The separate FixedCells premise covers nested addresses in stored cells;
the scalar initial reference makes it straightforward in these clients. A
stored-dangling-address case could illustrate that premise independently,
but no such extra case is required to repair the current statements.

## Anticipated proof elaboration risks

The read-only pass found no semantic counterexample under the stated
hypotheses. Before compilation, two local proof-polish risks were identified:
the final `rfl` after the newer-address rewrites in `delay_states_related`
may be redundant, and concrete lookup/frontier simplifications may need
explicit normalization of `initial`, `exceptionMemory`, `integer`, or `shift`.
These are hypotheses about compiler feedback, not recorded failures.

All expected results and public statements are to be retained unless an
actual semantic issue is first reported to root. Focused checks will use the
pinned offline Nix environment, the shared focused-build lock, and recorded
input hashes. Default proof limits and lint settings remain unchanged.

This report is preparatory and implementation evidence only. Full exact-
candidate validation, exhaustive proof audit, and final Standards/Spec review
remain requirements of the enclosing foundation loop.

## Relocation r6 feedback and first client correction

The terminal automatic record gives exit 1 with unchanged inputs, ending at
20:10:48 UTC. Relocation itself built in 36 reported seconds. Its example
failed after 9.9 seconds. Root owns that check's session and evidence record.

The unrelated-address branch of `related_initial` still contained projections
from `start`, so its heap simplification arguments did not apply. The proof
now explicitly states the memory lookup goal before its address cases. The
`control` simplification name conflicted with the root-level MonadControl
operation; it is now `Relocation.control`. The two relocated integer-cell
observations explicitly expose the `integer` value definition. No definition,
theorem statement, expected observation or step count was changed in the
Relocation client.

The same `Relocation.control` qualification is applied in ForceObservation's
initial-configuration proof. Its remaining proofs and both clients will be
checked together through `Examples.SuspensionForceObservation`, which imports
the corrected Relocation client. The Relocation core remains root-owned and
unchanged by this worker.

## ForceObservation r1 feedback

The first combined check is terminal with exit 1 and unchanged recorded input
hashes. `Examples.SuspensionRelocation` passed in 15 reported seconds and
`Applications.Suspensions.ForceObservation` passed in 17 seconds. The force
client failed after 7.1 seconds. Evidence is saved in
`session/validation/suspension-force-observation-r1.log` and `.json`.

All core observation, reflection and initial-relation proofs compiled. The
anticipated redundant-rfl concern did not occur, so that proof is unchanged.
The concrete client feedback consists of expressions retaining `initial.next`
or `exceptionMemory.next` instead of the known frontier one, and renamed
integer values retaining their `integer` wrapper. Two exact private frontier
facts and explicit integer-wrapper simplification now address those sites.
No public statement, expected observation, step count or semantic definition
was changed. The core module's documentation now explicitly states the finite
normal/raised scope; this clarification is included in the next check's input
hashes. The corrected client remains unverified until that check finishes.

## ForceObservation r2 — focused success

The second combined check passed with 751 jobs and exit 0. Queue/start input
hashes matched, and the same input hashes were unchanged at completion. The
compiler reports 39 seconds for ForceObservation core and 47 seconds for its
client; the corrected Relocation client was unchanged from its successful r1
compilation. Exact evidence is saved in
`session/validation/suspension-force-observation-r2.log` and `.json`.

Checked public core declarations include `FixedCells`, `fixed_empty`,
`delay_states_related`, `delay_configs_related`, `value_observed`,
`raised_observed`, `value_reflected`, `raised_reflected`, and
`closed_value_observed`. The actual body execution is transported in both
directions through Relocation and connected to Derived's checked force-delay
contracts. The private successful cache write remains outside the represented
address image, while represented memory effects and exception names remain
related.

All previously stated client expectations passed. Normal forcing finishes in
25 transitions with returned reference 2, old reference 0 containing 7 and new
reference 2 containing 9. The reflected client recovers these facts for any
normal run of that program. Exceptional forcing finishes in 23 transitions,
retains the write of 7, raises exception 2, preserves its exception-name set,
and has frontier 2; its reflected client recovers the packet and count for any
raised run. The dangling-capture clients retain the distinct 3-step missing-
address fault and 10-step reference-kind fault, validating the stated domain
restriction without changing either expected result.

Only the authorized proof normalizations, a qualified control-renaming name,
two exact private frontier facts, and the finite-completion documentation were
changed. Public statements, semantic definitions, expected counts and
observations, proof limits and lint settings are unchanged. Relocation core
was not edited by this worker. No index, commit, entrypoint, tracker, dependency
or full-gate changes were made. The sources and this report are stable for
root's coordinated snapshot and the enclosing exact-candidate validation and
independent review process. Focused success does not constitute foundation or
chapter acceptance.
