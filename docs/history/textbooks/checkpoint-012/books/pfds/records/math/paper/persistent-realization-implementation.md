# Local10021 measured debit interpreter: implementation handoff

Development began2026-11-03 at the clean3dd baseline in `persistent-accounting`.
The current source is a draft, not yet compiled or accepted. Root owns the
new Realization/Observation modules, their clients, public integration and docs.
The other authors own History and Debits, respectively.

The independently expected case has two operation occurrences, each with one
unit of unshared work and realized support{7}. The first incurs two units, the
second one, for total3 and final support{7}. Starting with{7} already realized
leaves exactly two unshared units. Splitting this run into consecutive single
operations must retain the first operation's support. Renaming7 to17 through
the injection n↦n+10 preserves the cost. Repeating the same operation label
still repeats its unshared charge; replacing a list by its finite set without
an occurrence/enumeration condition would lose that charge.

`Realization.lean` uses unchanged `Resources.run`. `realizeStep` charges
unshared work plus the set difference of realized debit support from seen.
The intended local and global identities retain initial support on the left
and final support on the right, without natural-number subtraction. State
observation, initial-support monotonicity and injective renaming refer to
that same measured run. No global additive Finset instance or false additive
unique-support reweighting is introduced.

These are statements about the explicit debit interpreter. The actual
suspension-machine work bridge remains10017; in particular, the existing
handled-exception source case has two body attempts and zero writes. The
pending graph/accounting glue will derive a bound from Paid and finite-scope
closure, with an explicit duplicate-free finite-node enumeration. The
expected examples are not adjusted to accommodate proof failures.

Validation: not yet run. The existing full901 and focuseda3 consumer check
own the formal build slots. New source remains outside their input closures.

## First focused attempt

persistent-realization-r1 ended1 with unchanged inputs. The general step/run
balance, state, empty-support cost and initial-state bound elaborated; the
renaming step retained one unsolved finite-set difference/cardinality goal.
The map_sdiff lemma was oriented toward expansion while the goal required its
reverse, followed by card_map. This is a proof normalization defect, not a
changed expected claim. Raw JSON/logs are preserved. No proof limits or
expectations changed. A correction and explicit standard local option settings
will be checked in a new focused round.

## Full draft connections

Observation.lean now connects the same realization run to the Paid/closed-scope
bound through a duplicate-free exact enumeration. It reuses List.sum_toFinset,
rather than deriving a competing list-sum API. The independent Realization
layer has no graph premise; graph scope enters only in the Observation layer.
The connected public Fork from Examples.PersistentDebits has three nodes, one
unshared unit each, one prior discharge and two realizations of debit7. Its
expected actual interpreter total and source budget are both4. Repeating the
left occurrence in the list produces5 while leaving the finite-node budget4,
so the enumeration premise must remain. These glue/client statements are not
yet compiled.

PersistentSourceBoundary uses public10020 source theorems with explicit source
inputs: empty start for repeated force, and fixed exception17 at captured name3
for the handled retry. The positive case equates only one body-entry count
with the interpreter's one shared unit. The retry case retains two body entries
and zero writes, exceeding the same coarse one-address charge. Neither case
claims that the abstract interpreter counts all machine transitions or body
work. The r2 focused run includes both source cases and the corrected core.

All nine new Lean files are now imported by SquareApplications. The new public
documentation explicitly identifies the development/acceptance boundary. This
integration does not change either running candidate's checkout or active
focused source inputs. Root will commit a recovery WIP snapshot before any
complete-candidate acceptance claim.

## Second focused attempt

persistent-realization-r2 ended1 with its inputs unchanged. The corrected
Realization core compiled38s and PersistentSourceBoundary compiled26s. The
worked Realization client failed on implicit run_append arguments and an
omega proof for embedding injectivity; its generated secondary sorry errors
are failed elaboration diagnostics, not authored admissions. The correction
instantiates the unchanged public executor-composition theorem explicitly
and uses natural-number cancellation with its direct provider import.
Observation's uncompiled composition client received the same explicit
application. No statements, expected values, proof budgets or lint policies
changed. Corrected Realization r3 and Observation compilation remain pending.
Raw JSON/logs are retained under validation/persistent-realization-r2.*.

## Bounded Observation author assistance and added connections

The History author performed read-only author assistance within the existing
10021 loop against requirements v1. This was not an independent acceptance
review. The assessment confirmed the closed-scope bridge's same-run identity,
Nodup plus exact-enumeration premises, minimal Paid/closure assumptions,
unrestricted cyclic graphs, initial seen support and explicit source-cost
boundary. It found a concrete missing connection: measured open-scope accounting
did not yet use the existing PaidWithBoundary support theorem.

Before first Observation compilation, root added a shared exact enumeration
cost identity, a measured bound with external boundary.card, and its separate
initial-seen version. The open Cycle client now uses that bound and its source
discharge witness. Independent expectations remain cost1, internal payment0,
boundary credit1 and nonclosure. Initial seen equal to that singleton reduces
the new-work charge to0; boundary payment alone leaves it1. This distinguishes
paid credit from realized support. The duplicate-fork client now also proves
its toFinset remains exactly Fork.scope while cost rises to5 and Nodup fails.
These additions are uncompiled until the first Observation check. The exact
cost identity has no graph premise; only the payment-based bounds need Quiver.

## Third Realization attempt

persistent-realization-r3 ended1 with unchanged inputs. The explicit executor
composition and natural-number cancellation elaborated. The remaining client
failure is coercion normalization in the concrete renamed singleton: simp
left the embedding application to7 instead of17. Root retained the same
transport theorem and conclusion, proved the singleton map separately with
Finset.map_singleton and definitional equality, and used that exact image
equality in the public transport application. Realization core and actual
source-boundary client remain unchanged. Raw r3 JSON/logs are preserved; r4
is pending. No statements, expected observations, proof limits or lint policies
were weakened.

## First complete module/client check and explicit specialization repair

At committed c6f96cf, persistent-accounting-r1 checked all four cores and five
clients with67 recorded inputs unchanged. The check ended1: all modules except
Examples.PersistentObservation compiled or replayed successfully. Debits client
compiled99s and Realization client153s, preserving their entire original scope.
Observation client failed471s on two private function aliases not unfolded
by its simpa applications and on dotted constructors in two list-only goals.
There was no new general-theorem or arithmetic-counterexample failure.

Root retained every statement, exact cost and law premise. The two simpa lists
now explicitly unfold realized/cycleRealized; the duplicate-list expressions
name Fork.Node.left explicitly. The publication-facing document now describes
the stable API and scope instead of embedding transient compile status.
These changes are committed as eedaeca6fc2fcc3f73cb92630dc8d8acf2bd50f8.
The same complete target set is undergoing persistent-accounting-r2; no result
is assumed before its terminal record. All r1 diagnostics are preserved.

The core Observation check had independently passed116s with unchanged inputs.
Its exact enumeration identity has no graph premise; history enters only the
closed/payment or explicit-boundary bounds. The corrected client continues
to connect those public statements to the same fork and cycle source laws.
No proof budget, linter policy or expected result changed.

## Complete focused success and documentation-only candidate correction

The combined persistent-accounting-r2 ended1 at eedaeca6fc2fcc3f73cb92630dc8d8acf2bd50f8,
with all67 recorded inputs unchanged. Explicit constructor names elaborated,
but simpa lists still did not unfold two private functions occurring as bare
higher-order arguments. Root added explicit `unfold realized` and
`unfold cycleRealized` before those two public-bound applications. The same
statements, law hypotheses, exact costs, finite scopes and independent expected
observations remained unchanged. Commit eb61c35f911ad0fac36758c878559eaf5f795cfa
contains this correction. The raw r2 JSON/log retain the actual failure.

The complete combined persistent-accounting-r3 then finished exit0 at eb61,
with875 Lake jobs and all67 queued/start/final formal and configuration inputs
identical. All four core modules and all five connected clients passed. The
Observation client compiled176s; the other completed modules were reused by
stock Lake. Its terminal record/log are validation/persistent-accounting-r3.*.
This includes the corrected Debits and Realization clients, whose earlier
successful combined-r1 compilations were99s and153s respectively.

Author statement review then found a documentation precision issue: the words
“prior payment” could suggest chronology not supplied by unrestricted graph
histories. The boundary law retains a real supporting discharge in logical
history, possibly outside the scope. The public document now states that
meaning and leaves temporal order to concrete evaluator correspondence10017.
This documentation-only correction is commit577be121e074ddb5de6727a7481c115cb61b3b27.
No formal or configuration input changed; all67 hashes match the clean isolated
candidate. Its complete base-to-tip scope is11files and5commits, with no
exclusions and fixed bounded/original base3dd930c3e3989f3e5530463f3ac937a629551335.

The immutable candidate is validation-persistent-accounting on
pfds/persistent-accounting-review-r3. Earlier r1/r2 refs and manifests remain.
The completed ordinary-output warm copied125 groups/875 files/89351399 bytes
to its earlier eb61 materialization, with stock output hashing and no approval
record. The doc-only switch preserves identical formal/configuration inputs;
this does not replace the candidate's own full guard/build/audit. Unrun future
helpers now name577be12 and still require successful exact3dd as predecessor.

Both independent review axes have yet to run. Full acceptance, exhaustive
audit, matching verification and immediate final verification remain pending.
The whole Chapter2 frontier and all parent10017 work remain unchanged.
