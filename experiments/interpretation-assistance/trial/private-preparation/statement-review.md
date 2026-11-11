# Private H1/H2 reference statement review

Confidential preparation evidence for the coordinating session and independent
reference reviewer. Do not include this directory, its proof source, or any
successful diagnostic transcripts in tool-developer or author handoffs.

Baseline: `2b3b344b69c4e56324c8de2eb566ee0f8aef129b`.
Source: `checkout/Examples/PrivateReference462.lean`.
No tracked baseline file was modified. This is a private detached worktree with
its own project outputs; only pinned dependency packages are shared.

## H1

The setup uses Bool source codes and values with `sourceEval c a = c`, a constant
false step, and a selected false code. The target uses Option Bool codes with
`targetEval c a = c.getD true`, a constant false step, code map `some`, and identity
value map. Both local map laws are checked, and the source representation proof
is actually part of the supplied selected object.

`rows_differ` proves distinct code rows for every target input. `rows_constant`
states precisely the remaining limitation: each row is input-constant. This is
not an arbitrary input-dependent evaluator, and it is not a globally constant
target evaluator. Neither code rows nor the expected false witness were changed.

`not_onto` disproves surjectivity of the actual code map by the omitted `none`
input. `extension` inhabits the exact native `Map.Extension` proposition for
the selected source row. Its proof establishes a stronger pointwise equality,
which is a legitimate sufficient certificate; it does not claim other selected
rows extend. `full` is built by `Map.selectedExtension` using that certificate.
`selected_code`, `selected_value`, `full_representation`, and `omitted_input`
retain the specified code, false value, all target inputs, and the omitted input
explicitly. The witness comparison consumes `Map.extension_witness`.

`restricted` uses the native `Map.selectedImage` route. Its representation has
an image-subtype domain, not all Option Bool. `restricted_code` and
`restricted_value` compare selected observations, while
`restricted_excludes_none` proves a target input cannot occur in the restricted
domain. No equality of those domains or full-target conclusion from image
restriction is claimed.

`wrong_source_code` proves the negation of the exact proposed representation
of source code true. `no_selected_true` rules out any selected source object
with that code under the fixed evaluator and step. Separately, `WrongH1.lean`
tries the false representation obligation and Lean rejects it at that equality.
Compiler rejection is recorded separately from the checked refutation; the
failed proof alone is not used as mathematical evidence.

## H2

The two additive maps have exactly the requested types and formulas: Nat to
Nat × Nat, followed by Nat × Nat to Nat. Their zero and additive laws are
checked. The intermediate product is the observation type of `productExecution`,
not a pair introduced only while simplifying the final scalar expression.

The compiled seed and transitions come from the existing `total`, `seed`, and
`addBody`, with `counted.scalar`. `seed_observed` is (0,1).
`transition_observed` is (acc+x,2), retaining both one cell visit and one addition
primitive charge. `native_execution` and `native_execution_sum` consume the
existing source execution relation for every integer list, with exactly its
length in visited cells and final sum. `native_counted`, `native_ordinary`, and
`erasure_before_reweight` recover existing public native contracts before any
resource change.

`transport_execution` quantifies over an arbitrary additive observation monoid
and a Nat additive homomorphism. It unfolds the actual compiled total program to
seed binding and the executed transition run, then uses generic
`Resources.reweight_bind` and `Resources.reweight_run`. It does not rely on
#461's Nat-only square-program helper or invent a common recursion interface.

`product_transport` applies that universal execution result to the product map.
`second_transport` pushes the second additive map through the product seed and
product transition run, again using the generic public laws. `composed_execution`
connects the composed additive map on the original compiled program to the
actual final executor. `product_observation` and `final_observation` derive the
requested observations through those execution transport results and the native
counted theorem. `composed_observation` connects the final numeric result to
that composition explicitly. All these claims quantify over every integer list.
`observed_empty` and `observed_two` check the requested concrete results (0,7)
and (3,35).

`shifted_zero_rejected` refutes the zero law for n+1, and `no_shifted_additive`
proves that no additive homomorphism can agree with that function on all n.
`shifted_still_defined` retains the ordinary unbundled reweighting function.
The refutation does not concern all resource models or function definability.
Separately, Lean rejects the false zero obligation in `WrongH2.lean`.

## Validation and scope

`round03/check.log` is the final focused success (757 jobs, exit 0). The first
preparation attempt failed because `decide` was used with a syntactically free
input in a definitionally constant goal; exposing that constant goal fixed it.
No task expectation was revised. Round02 passed, then Round03 added explicit
native-execution-sum and composed-final-observation statements and passed.
All snapshots and failures are retained. These are preparation attempts, not
an author trial or assistance measurements.

`audit-final.log` passed with 1139 kernel-safe declarations, 519 theorem
declarations, and 17 project modules. The private reference module contributes
57 logical roots: 48 named source declarations and 9 generated proof auxiliaries.
All 57 are explicitly listed in `reference-audit-roots.txt`; the full root list
is `all-audit-roots.txt`. The audit includes imported project private/generated
roots through the baseline module-origin algorithm, not only final theorem
closures. Its axiom union is exactly propext, Classical.choice, and Quot.sound.
No unsafe runtime declarations were excluded in this audit.

The auditor is the pinned ProofAudit implementation with only its complete
entrypoint import replaced by the private reference import and its final command
moved to an importing driver. Compiling the helper before enabling the trace is
necessary to register its trace option. The first inline trace attempt checked
the axioms but exited nonzero because its just-declared trace option was not yet
registered; that failed setup transcript is retained as `audit.log`, not counted
as acceptance. The final helper and driver both exited 0. Exact adaptation diff
is retained and the audit algorithm is unchanged.

`source-policy.log` is the native Lean source-policy check of the final reference
source, exit 0. The two intentional bad-obligation checks each exited 1 at the
expected proposition; their commands, times and statuses are in
`negative-receipts.json`. They generated no accepted module and were not imported
by the audited positive reference.

No mathematical feasibility defect was found. No protocol expectation was
changed. This establishes direct native feasibility only: tool-generated routes,
wrong-type/missing/refuted evidence statuses, environment-failure handling, and
registry exhaustion still require separate prototype validation. Independent
reference/protocol review and final task/registry freeze remain launch gates.
