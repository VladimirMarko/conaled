# Local 10019: primitive and outcome compatibility

This is the next assigned slice in the existing `pfds/pure-suspensions`
implementation loop, with fixed review base
`b422800fb5b6dc1253823057c0ea71644274d77c`. Root owns the Representation
module, commits, entrypoints, complete validation, reviews and checkpoints.
The assigned files are `Pure/Compatibility.lean`, its example module and this
report. No completed 10014 or earlier pure-value source is changed.

## Intended boundary and approved design

The partial fault graph preserves the common diagnostics and their Nat
payloads. Raw `expectedAddress` corresponds to pure `expectedSuspension` for
the nonaddress/nonsuspension forcing case. Raw `missingAddress` and
`expectedReferenceValue` have no image, and pure excluded-effect faults have
no raw preimage in this graph. The graph is a compatibility table, not an
unreachability or type-safety theorem. The actual execution bridge still needs
its memory/domain and effect arguments.

`PrimitiveResultRep world` separates returned values, raised packets and
stuck faults. `ResultRep world` additionally separates matched environments
and ordinary mismatch. It uses the root-owned `ValueRep`/`EnvRep` and the fault
graph, and keeps reached raw memory outside this outcome relation. The
relations transport along immutable-world extension using the existing
representation transport results.

`OperationCompatible raw pure` states that for every immutable world and
every related input pair, the **actual operation results** are related in that
same world. `ParametersCompatible operations raw pure` requires this law only
for selected operations and separately requires equal Match/Bind exception
tags. It contains no expression-evaluation, termination, no-reentry, memory
invariant or source type-preservation premise. The parameter operations remain
separate definitions; source-basis typing/name validity is not asserted.

This compatibility law alone does not enforce a hereditary source domain.
`ValueRep` can relate closures containing effectful syntax or values containing
unselected primitive tokens. A subsequent execution interpretation must also
establish preservation of an admissibility policy for values, captured
environments and recursive groups. This is a separate obligation; no premise
about a complete expression evaluation is hidden in the primitive law.

## Concrete usable operations

Identity returns its input and supports arbitrary related values, including
addresses representing suspensions. The integer and Boolean adapters apply
an explicit scalar function to the corresponding atom and otherwise return
the common primitive fault. The small `BasicOperation` basis instantiates
identity, integer successor, integer zero-test and Boolean negation.

`basicRaw_output_origin` and `basicPure_output_origin` state that a result is
the existing input, an atom, or the primitive fault. Thus this basis introduces
no new closure, suspension or primitive token. The connected
`basic_preserves_value_policy` client derives preservation of any pure-value
predicate containing the input and all atoms. It deliberately leaves the
later hereditary-domain policy unspecified.

The concrete client expects 41→42, zero→true, true→false, and an integer
supplied to Boolean negation→primitive fault on both sides. Each case obtains
its representation conclusion from the generic operation law, while checking
the independently specified output. Additional cases retain raised versus
returned outcomes, matched bindings versus mismatch, the forcing-fault
correspondence and the rejection of inconsistent basis exception tags.
The bad-forcing-operand client also calculates both actual one-step machine
transitions before applying the fault relation; the table entry is not merely
asserted between two manually chosen result constructors.

## Discriminating address-equality case

The example-only diagnostic operation reads a record with exactly two
address-valued fields, compares the addresses, and returns a Boolean. Other
shapes give a primitive fault. Its labels are irrelevant to this diagnostic;
the concrete pairs use distinct labels 0 and 1. The checked theorem proves
equivariance for every injective address renaming, using the existing actual
`Core.Relocation.Equivariant` definition.

The immutable world assigns addresses 0 and 1 the same suspension meaning:
body integer 7, empty capture, no recursive descriptor. Two calls to the actual
`Suspensions.delay` operation create the two corresponding raw cells. The
client records both cell lookups, frontier 2 and the raw/pure capture relation.
It also proves that every address named by this world is allocated in that
actual two-delay memory.
Thus noninjectivity of the semantic world is compatible with ordinary fresh
allocation; it does not confuse physical address equality.

The aliased raw pair (0,0) and distinct raw pair (0,1) both represent exactly
one pure pair. The raw operation returns true and false respectively. Any
compatible pure function would have to return both Boolean atoms on that
one input, which is impossible. The proof uses the atom-output inversion
lemma for `PrimitiveResultRep`; it does not assume general functionality of
`ValueRep`, and does not assume that worlds are injective.

This is a deliberately excluded diagnostic primitive. It is not a claim that
Standard ML allows equality at suspension type, nor a new effect admitted to
the pure basis. Its role is to show precisely why address-renaming
equivariance alone cannot replace the primitive interpretation law.

## Current evidence and remaining work

The root-owned Representation core passed its focused check and remains
unchanged in this slice. Compatibility revision 1 then completed at
2026-11-02 20:41:31 UTC with exit 1 and unchanged input hashes:
`active-validation/suspension-pure-compatibility-r1.{json,log}`. Its original
Compatibility core passed in 11 seconds. The only reported example errors
were attempts to reduce the well-founded address-renaming definitions by
definitional equality. The corrected proof uses their public simplification
equations; no proposition or independently expected result was weakened.

The corrected example and the approved output-origin additions were captured
as uncompiled drafts in checkpoint 018, commit
`86b394f5537cd9a61ac9b9708b5fef8face6d047`. The exact same source bytes then
passed revision 2: 2026-11-02 20:48:58.273086–20:50:20.302938 UTC, exit 0,
751 jobs. The updated core compiled in 27 seconds and the complete example
in 43 seconds. All 21 local source modules and 5 configuration files had
identical queued, acquired-lock and terminal SHA-256 hashes. The evidence is
`active-validation/suspension-pure-compatibility-r2.{json,log}`. The wrapper
used the pinned offline Nix environment, `LEAN_NUM_THREADS=1`, the shared
focused-build lock, and this worktree's private project outputs.

| Checked source | SHA-256 |
| --- | --- |
| `Applications/Suspensions/Pure/Compatibility.lean` | `bee261d1fc3dbf637030df6b964b2a249ca83ef10343d6fb4c3aaf4049b0cc92` |
| `Examples/SuspensionPureCompatibility.lean` | `d8072593abca3cbf857683558009b1bda5d03b8cdf3070acade3b8479b860efc` |
| Unchanged imported `Pure/Representation.lean` | `dbcf7f1fb656ede59bfb57db5bca97f2d145cf5226aa27e2bb635465e5b5f980` |

The earlier pure Syntax/Value/Machine APIs remain unchanged. `git diff --check`
for the two owned source paths passed. Source inspection found no admission,
new axiom, suppressed linter or raised proof budget. Complete-candidate build,
exhaustive proof audit and independent reviews remain parent-owned gates;
this focused result is not ticket acceptance or an execution-adequacy theorem.

## Statement review and checked connections

The review covered the quantification over all worlds, preservation of exact
outcome classes, noninjective worlds, scalar-input failures, and the distinction
between an operation law and a claim about an expression's whole execution.
The concrete basis witnesses satisfiability of the law. Its admissibility
boundary is explicit, and neither a well-typedness nor a no-reentry premise is
silently assumed.

| Public claim or interface | Retained connection and boundary |
| --- | --- |
| `FaultRep` and its negative cases | `wrong_force_operand_connected` computes both actual forcing transitions; missing-address and reference-kind cases are rejected by the graph, without claiming they are unreachable in the unrestricted raw machine. |
| `PrimitiveResultRep`, `ResultRep` and world transport | Scalar clients use `basic_operation_compatible`; raised, matched and mismatch clients preserve their result constructors. `raised_is_not_a_value` excludes an incorrect outcome coercion. Transport changes the world through existing representation laws and does not change a result. |
| `OperationCompatible`, `ParametersCompatible` | The four-operation basis discharges the universal laws for arbitrary worlds; `mismatched_basis_tags_rejected` demonstrates the separate exception-tag condition. Restriction changes only which operation tokens require the same law. |
| `basicRaw_output_origin`, `basicPure_output_origin` | Identity returns its existing input; scalar adapters produce an atom or the primitive fault. `basic_preserves_value_policy` derives a useful policy-preservation result through the public pure origin theorem. |
| Address-renaming equivariance versus interpretation compatibility | `pointer_equal_equivariant` proves the former for every injective renaming. `pointer_equality_no_compatible_pure` refutes the latter for every proposed pure function by two represented inputs with unequal Boolean results. |
| Realizability of the address discriminator | `two_delays_same_meaning` and `world_addresses_allocated` connect the noninjective world to two actual delay allocations. `aliased_rep` and `distinct_rep` feed the incompatibility proof; `identity_preserves_alias_abstraction` confirms that identity still satisfies the law on both inputs. |

No expected result or theorem statement was changed in response to compiler
feedback. Revision 2 changed only the address-renaming proof and added the
approved independent output-origin obligations.

## Remaining integration obligations

The overall 10019 obligations remain
the actual creation/closing provenance invariant, cache witnesses derived from
finite runs, all-outcome interpretation with explicit fault correspondence,
proper nested-body occurrence certificates, and the resulting actual
no-reentry and separate successful-cache/resource theorems.
