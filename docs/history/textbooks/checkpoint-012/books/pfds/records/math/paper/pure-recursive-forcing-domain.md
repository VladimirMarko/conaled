# Local 10019: hereditary code domain

This is the parent-approved follow-on to the checked primitive-compatibility
slice, within the same implementation loop and fixed review base
`b422800fb5b6dc1253823057c0ea71644274d77c`. Owned files are
`Applications/Suspensions/Pure/Domain.lean`,
`Examples/SuspensionPureDomain.lean`, and this report. Parent owns commits,
entrypoints, tracker, whole-candidate validation, reviews and checkpoints.

## Why this boundary is needed

`ValueRep` preserves source code and represented values, but does not itself
restrict effects inside that code or select primitive tokens. A primitive can
therefore satisfy `OperationCompatible` while returning an identically coded
raw/pure closure whose body allocates a reference. The execution bridge needs
a hereditary code-domain invariant as well as representation compatibility.
Neither law assumes a whole expression's finite run or absence of reentry.

## Approved definition shape

`RecursiveForm` traverses existing `Core.Expr` syntax. Its only additional
conditions occur at recursive declarations: existing
`Core.Recursive.Permitted`, distinct recursive binder names, and the same
checks in all nested RHS/body code. Three small helpers traverse optional
expressions, named expression lists and clause bodies. The traversal imposes
no pattern condition of its own, and walks children even in effectful source
forms; it remains independent of the effect restriction.

`CodeAllowed operations expression` conjoins the existing
`ExpressionAllowed` with this recursive-form condition. Named-code and
clause-code variants reuse the existing corresponding effect predicates.
Patterns retain exactly `PatternAllowed`. There is no second inductive
syntax/effect hierarchy.

This is a minimal bridge domain, not the full Standard ML source judgment.
It adds no typing, nonempty match, record-label distinctness, namespace,
well-scoping, hygiene, termination or no-reentry condition. Duplicate recursive
binder names are excluded because creation/closing a full descriptor must not
lose a delayed binding through shadowing. Other pattern and environment
shadowing remains represented by the existing operations.

The finite mutual predicates `ValueAllowed`, `EnvAllowed`,
`OptionalValueAllowed`, `GroupAllowed` and `OptionalGroupAllowed` inspect
stored code, selected primitive tokens and earlier captures. `RhsAllowed`
checks the existing wrapper's exact source expression. A group checks all RHS
code, distinct descriptor binder names, and its earlier outer environment.
The predicate definitions never call `Group.members`, never traverse an
unrolled semantic cycle, and never require a body evaluation witness.

## Intended reusable interface

The module provides source constructor/inversion facts (`CodeAllowed.*_iff`),
named/clause list inversions and membership, value constructor inversions,
the selected-token equivalence, and environment lookup/append/extension.
`GroupAllowed.of_decoded` connects the existing exact RHS decoder to the
source-code and binder-name conditions. Group projections return allowed RHS
code, distinct names and the earlier captured environment.

The parent-requested `decode_permitted` helper obtains successful whole-list
decoding and an exact ordered source round-trip from
`Core.Recursive.Permitted` alone. The mutual-source client now consumes that
existence result before constructing its allowed descriptor, and verifies
that the decoded bindings equal the independently specified original group.

`RhsAllowed.instantiate`, `GroupAllowed.members` and
`bodyEnvironment_allowed` prove preservation when constructing recursive
members and their body environments. These theorems use the finite descriptor
premise; member expansion is absent from the predicate definitions.

`PrimitiveResultAllowed` checks returned values and raised packets. Diagnostic
faults contain no returned code and are admitted here; their raw/pure
correspondence remains the separate `FaultRep` obligation.
`OperationPreserves` and `ParametersPreserve` express this output-domain law
independently of `OperationCompatible`. The existing basis's
`basicPure_output_origin` proves `basic_operation_preserves` for every selected
subset of its operation tokens.

## Connected clients and independently expected outcomes

- The existing mutual `f () = force s; s = $(f ())` descriptor is admitted.
  The client uses the source decoder, generic group/member/environment
  preservation, and the original checked round-trip lookups. It does not
  assert that the cycle terminates.
- The existing returned closure captures an environment containing its own
  suspension meaning. The client proves it allowed and checks the actual
  two-transition function-formation run and its original suspension lookup.
- Applying integer 3 as a function to integer 4 remains in the domain. The
  independently expected raw and pure outcome is `expectedFunction`, reached
  in five transitions on each machine. This checks the stated lack of a type
  safety premise and retains the explicit fault relation.
- A nested, delayed declaration with an integer RHS is rejected. A descriptor
  with duplicate recursive name 5 is rejected. An unselected primitive token
  nested inside a record is rejected.
- The scalar basis discharges the generic output-domain law, and successor
  retains the expected 41-to-42 result through that public law.
- The diagnostic constant primitive returns a reference-allocating closure.
  Its raw and pure results satisfy `OperationCompatible`, but its output is
  excluded by `ValueAllowed`, so it fails `OperationPreserves`. This exposes
  the missing obligation without strengthening representation itself.

## Current validation status

Revision 1 passed both the new core and all connected clients on its first
focused pass: 2026-11-02 20:59:28.666685–20:59:48.547427 UTC, exit 0, 753 jobs.
The core compiled in 10 seconds and the example in 2.6 seconds. All 23 local
source modules and 5 configuration inputs were unchanged across queue, lock
acquisition and completion. Evidence is
`active-validation/suspension-pure-domain-r1.{json,log}`. The check followed the
shared worker's green/frozen raw Recursive extension; no imported source was
changed by this slice.

After that terminal result, the parent requested the small source-only
whole-list decoder existence/round-trip helper. Revision 2 checked that
addition and its connected mutual client successfully:
2026-11-02 21:03:09.956704–21:03:31.850381 UTC, exit 0, 753 jobs. Core compilation
took 9.4 seconds and the example 5.4 seconds. All 28 source/configuration hashes
were identical at queue, lock acquisition and completion. Evidence is
`active-validation/suspension-pure-domain-r2.{json,log}`. The pinned offline Nix
shell, `LEAN_NUM_THREADS=1`, shared focused-build lock and private project
outputs were used for both passes. No source or expected result needed a
compiler-feedback correction.

| Checked source | SHA-256 |
| --- | --- |
| `Applications/Suspensions/Pure/Domain.lean` | `822af891bf84e007a57c5ad96f53dc6e8c861c49be6dbec084cf78b6513e6203` |
| `Examples/SuspensionPureDomain.lean` | `dea47aed43321e1671d9ad59964008cda44f1d8597c342fe258a0aa482bbd8b5` |
| Imported raw `Applications/Suspensions/Recursive.lean` | `cbf1dfda736afb9f8e4e9bc4b023030edcb6713de9902a8828cdc1489f0d0934` |
| Imported `Pure/Compatibility.lean` | `bee261d1fc3dbf637030df6b964b2a249ca83ef10343d6fb4c3aaf4049b0cc92` |

Git HEAD during these focused checks was
`86b394f5537cd9a61ac9b9708b5fef8face6d047`; the frozen per-file hashes identify
the new draft source exactly. Parent alone stages/commits the shared worktree.
Earlier 10014 and pure Syntax/Value/Machine/Compatibility sources were not
changed by this slice. Source inspection found no admissions, new axioms,
suppressed linters or raised proof budgets. Complete-candidate validation,
exhaustive proof audit and both independent review axes remain parent-owned.

## Statement review and handoff

The source constructor/inversion facts expose the same existing effect
judgment plus only the recursive-form traversal. The extra traversal ignores
pattern syntax and imposes no hidden clause, record or name-sorting condition.
Its restriction is hereditary through all stored code, including delayed and
function bodies, without evaluating that code.

The value/group mutual predicates are finite: a descriptor checks its source
RHS list and earlier capture. `GroupAllowed.members` constructs allowed
members from that existing proof; member expansion does not occur in the
definition of admissibility. The mutual-cycle and returned-closure clients
demonstrate that the premises admit the intended recursive representations.

| Public result | Checked connection |
| --- | --- |
| `CodeAllowed.*_iff`, named/clause inversions and `CodeAllowed.force` | Build the original mutual function/suspension code and returned-closure clauses. The delayed invalid-RHS client isolates the nested recursive-shape restriction. |
| `decode_permitted`, `GroupAllowed.of_decoded` | `mutual_source_decoded` recovers exact ordered bindings from the source condition, verifies the expected descriptor, and supplies the construction used by `mutual_group_allowed`. |
| `EnvAllowed.lookup/extend`, `GroupAllowed.members`, `bodyEnvironment_allowed` | `mutual_cycle_allowed` derives both allowed members from the existing checked lookups and retains the exact original round trip. |
| Stored code and capture admissibility | `returned_closure_connected` combines an allowed recursive capture with the actual two-step function-formation run and unchanged suspension back-reference. |
| Distinct group names and selected tokens | Duplicate-name and record-nested unselected-token clients are rejected by the public descriptor/value projections. |
| Explicit raw faults | `admitted_application_faults` proves CodeAllowed and both actual five-step `expectedFunction` runs, together with their `ResultRep` connection. |
| `basic_operation_preserves`, `basic_parameters_preserve` | The scalar client obtains its output-domain result through the public law and separately checks successor's expected 41-to-42 value. The proof uses the already checked output-origin theorem. |
| Separate operation obligations | `compatibility_does_not_supply_domain` combines representation compatibility with failure of domain preservation for the same effect-bearing constant primitive. |

The domain permits diagnostic faults because they contain no returned code;
the Compatibility fault graph still controls which raw and pure diagnostics
correspond. No conclusion here states type preservation or excludes raw faults.
No formal claim assumes a whole evaluation or no-reentry property. The source
and API are now frozen for the shared worker's separately owned runtime-domain
layer, `Pure/DomainState.lean`.

## Remaining integration obligations

The forthcoming control/frame preservation, immutable-world memory evolution,
finite all-outcome interpretation, proper nested-body occurrence certificates
and actual no-reentry theorem remain separate obligations. This domain alone
does not establish ticket 10019 or chapter acceptance.
