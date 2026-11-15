# Coordinator assessment of closed attempts

This assessment was written after both authors returned closed attempts. It is
separate from author self-reports and the frozen prospective protocol. Exact
archives and hashes are in `../authors/`; byte-identical successful submissions
are integrated as `Examples/ProofRequirementManual.lean` and
`Examples/ProofRequirementAssisted.lean`. No author proof was repaired during
packaging. Public handoff HEADs and every frozen input hash still matched after
closure. Source snapshots match their wrapper-recorded SHA-256 values and their
corresponding submitted `AttemptNN.lean` files.

## Frozen rubric results

All four task/arm cells pass. The following findings come from inspecting the
actual definitions and proofs, comparing their statements to `../tasks.md`, and
replaying the accepted artifacts. They do not rely solely on author reports.
Names in the table are relative to `ProofRequirementTrial.Manual` or `Assisted`.

| Obligation | Manual evidence | Assisted evidence | Assessment |
|---|---|---|---|
| Named sufficient E interface | `ReversalRequirements`, `reverseBlocks` | `ReversesOperation`, `reverseBlocks` | Both name the binary reversal law, not the requested three-input conclusion. The generic proofs use it twice. |
| Original E replay and dependency distinction | `OriginalReversalRequirements`, `reverseBlocks_original` | `reverseBlocks_replay` | Both replays retain the unused ambient parameter and genuinely use involution twice. The revised proofs remove both cancelling steps and no longer require involution or a unit. Both conclusions retain the exact parentheses and order. |
| Both E targets | `listReversal`, `boolReversal`, `list_reverseBlocks`, `bool_reverseBlocks` | `list_reverses`, `bool_reverses`, `list_reverseBlocks`, `bool_reverseBlocks` | List obligations use `List.reverse_append`; Boolean obligations check all pairs. Target conclusions call the generic result. Original concrete source replay is also present. |
| E applications | `list_empty`, `list_nonempty`, `bool_application` | Same names | All connect to generic specializations, retaining the frozen literal results. |
| E missing law and false conclusion | `bad_reverse_op_failure`, `bad_requirements_impossible`, `bad_target_failure` | `bad_obligation`, `bad_conclusion` | Actual Bool values refute the proposed law and the frozen conclusion; no empty carrier or unsatisfied premise is hidden. |
| Named sufficient W interface | `ObservedRightUnit`, `selected`, `selected_value` | `RightUnit`, `select`, `select_value` | Both return the required subtype with first projection exactly the input. Manual uses observation equality; assisted retains carrier equality, which the rubric explicitly accepts. |
| W replay and revision | `selected_original`, `observedRightUnit_of_rightUnit`, `selected_agrees_original` | `select` | Manual replays the original full law, then proves the weakening and equality of whole subtype data. Assisted preserves the original dependency pattern unchanged. |
| Both W targets and data recovery | `selectedList`, `selectedBool`, their value theorems, `selectedList_eq_source` | `listSelected`, `boolSelected`, their value theorems, `listSelected_source` | Both prove model obligations, call their generic construction, retain `[]`, `[1,2]`, `true`, and recover `Source.selected` as subtype data. |
| W inhabited wrong selection | `natAlternative`, `nat_witness_exists`, `nat_selection_impossible`, `nat_observed_right_unit_missing` | `natWitness`, `nat_witness_exists`, `nat_selection_impossible`, both missing-law theorems | The same fiber contains 1 but cannot select 0. The law failures are checked at 0, so existence cannot substitute for the specified selection. |
| Erasure rejection | `listAlternative`, `list_witness_values_differ`, `erased_witnesses_equal`, `no_recovery_from_nonempty` | `alternative`, `selected_alternative_differ`, `no_projection_recovery`, `list_erasure_no_recovery` | `[1]` and `[2]` inhabit exactly the same fiber. Equal `Nonempty` proofs cannot let one function recover both different projections. Assisted proves a reusable obstruction and instantiates it; manual uses proof irrelevance directly in the concrete proof. |

## Statement review

E quantifies over arbitrary carrier, operation and reversing function before
all three inputs. Its binary assumptions are satisfied in the supplied models;
there is no circular client-theorem field. W keeps carrier and observation types
independently universe-polymorphic, with the same input in the subtype predicate
and projection theorem. Proof irrelevance identifies only proof components;
it does not identify the distinct list data. The erasure statements choose one
recovery function before quantifying over every witness in a fixed fiber.
Neither claims that selecting some inhabitant is impossible.

The manual source's failed `Attempt02` retains the same statement for
`selectedList_eq_source`. Its raw diagnostic is failure to synthesize
`Trans Eq Eq ?m.15` at a chained equality step. `Attempt03` replaces only that
proof with `Subtype.ext` and `selectedList_value`. A coordinator replay of the
unaltered failed source reproduces the same diagnostic. This is a host
elaboration failure; it does not refute the mathematical equality. The earlier
manual warnings concern structure syntax and proposition declaration style.
Assisted's two archived Lean diagnostics are empty, with exit 0 in each record.

## Post-trial comparison

`Examples/ProofRequirementComparison.lean` is coordinator work after closure,
not an author submission, repair or new grading requirement. Its
`reversal_requirements_iff` identifies the two E laws. `observed_of_carrier`
translates the assisted W law to the manual W law, and `selections_equal`
compares their full subtype results under that law.

The independently chosen separating model is `A=Nat`, `m=Nat.add`, `e=1`,
with constant observation into `Unit`. Adding one leaves that observation
unchanged, so the manual construction validly selects 0. Carrier right-unit
would imply `1=0` at input 0 and is rejected through the assisted author's own
negative theorem. The checked `constant_observed_unit`, `constant_selection`
and `observed_does_not_imply_carrier` establish the difference in sufficient
requirements. Both authors still pass W; this does not establish global
minimality or that the ledger caused the stronger choice.

## Evidence limits and validation

Authors report fresh contexts, no prior private-solution or other-arm exposure,
and no outside sources. Root records no interventions. The assisted author
reports reading the supplied ledger before authoring; the manual author received
none. The allowlisted trees and unchanged input hashes are checked evidence;
without a raw agent-session export, the complete reading history is not
independently reconstructed. Authored command transcripts are labeled as such;
they abbreviate some read/source-writing commands. The compiler commands and
their diagnostics are recorded exactly by the wrapper.

`accepted-artifacts.json/.log` records successful coordinator Lake replay of both
exact submissions and the comparison module. `original-manual-failure.json/.log`
records the expected failed replay separately. `integrated-check.json/.log`
records the successful development check of all 998 modules and exhaustive
axiom audit, with source hashes. Exact-candidate acceptance evidence is supplied
to the review coordinator after commit. Raw logs
retain compiler whitespace; whitespace-only findings in those archives are
intentional preservation exceptions, not formatting changes to authored code.
