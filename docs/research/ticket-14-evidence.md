# Ticket 14: matrix and stack compiler migration

Implementation base: `101577b2ece550803c8ea6e75995bf2f648496c4`.
Updated ticket review base: `0b0411bca2b1ce56ee84bf1e06814e27be818792`.
Ticket 18 was incorporated without conflicts at merge
`4d54022e61c0b84fd4bee5ff0ed3c6a9e87b4fa5`; both public entrypoint imports remain.
The unrelated `a6cd22b` changes are preserved and excluded from the ticket diff.
This record is the declaration ledger for comparison with ticket 20.

## Caller ledger

| Declaration or obligation before | After | Accounting |
|---|---|---|
| `MatrixCompiler.Slots`, `encode`, `decode`, `decode_encode`, `encode_decode`, `Code`, `denote`, `first`, `second`, `pair`, `Prim`, `meaning`, `primitive`, `target`, `slotsFintype`, `slotsDecidableEq`, `first_mulVec`, `second_mulVec`, `denote_primitive` | Same declarations in `Applications.Linear.Operations` | Moved unchanged to break the old Compiler → Maps → Compiler cycle. No reduction claimed for this move. |
| `MatrixCompiler.sound.ident`, `.comp` used `denote_id`, `denote_comp` | `Maps.matrixValues_laws.ident`, `.comp` | Structural soundness now follows the composed map, whose laws use `RawMap.comp_laws`; the public `denote_id` and `denote_comp` now project these sound fields, deleting their old direct algebra proofs. |
| `MatrixCompiler.sound.fst`, `.snd`, `.pair` used `denote_first`, `denote_second`, `denote_pair` | `Maps.matrixValueProducts_laws` | Product preservation is inherited from `ProductMap.comp_laws`; simplification only discharges the encode/decode comparison adapter. The public `denote_first`, `denote_second`, `denote_pair` project the resulting fields; their previous direct proofs are deleted. |
| `MatrixCompiler.sound.terminal`, `.primitive` | Unit reduction and `denote_primitive` retained | Local terminal representation and primitive meaning obligations remain. |
| `MatrixCompiler.compile_correct`, `StackMachine.compile_correct` used foundation `compile_sound` | `FirstOrderNaturality.compile_sound` | Both actual backends consume the same generic naturality proof and legacy-target adapter. No new source induction. |
| `MatrixCompiler.compileSquare.commutes` repeated encode/decode manipulation | `Maps.interpretation_commutes` followed by `compile_correct` | Reuses the coordinate/value interpretation seam. |
| `Examples.MatrixStack.jointSquare` used concrete synchronization | `Comma.Exact.agree` through `ofSquare` and `toSquare` | Uses the shared agreement carrier; concrete matrix and bytecode sides unchanged. |
| `agree_preserving_tail` rewrote separate source correctness results | Agreement output property plus `Certified.correct` projected onto the tail | Removes the repeated semantic equality argument. The bytecode tail certificate remains indispensable. |

`StackMachine.Certified` operations, their bytecode implementations, `run_append`,
and their tail certificates are unchanged. `StackMachine.sound` retains its
local definitional operation obligations. The encode/decode identities, projection-action and primitive proofs remain public in Operations.
The five denotation lemmas remain in Compiler as projections of the shared sound instance. Moving them is not counted as
removed work. New imports add no Mathlib dependency to the root foundation.

## New adapters and checked uses

All new declarations are in `Examples.MatrixCompilerPreservation`:

- `sourceObjects`, `Prim`, `sourceModel` specialize the general cartesian model
  to finite coordinate matrices; primitives are arbitrary typed matrices.
- `doubledModel` uses the actual `MatrixDoubling.doublingMap`,
  `doublingTerminal`, and nonidentity shuffle `doublingProducts`.
- `primitive_preserved` discharges primitive compatibility by matrix equality.
  `compile_doubled` consumes `cartesian_naturality`, including the existing
  terminal and product comparison laws from ticket 16.
- `identityModel`, `retag`, `identityInterpretation`, and `identity_laws` connect
  the identity interpretation from the same comma example to these coordinates.
  Retagging changes only the source tag; its hom action is identity.
- `compile_identity` uses generic naturality with definitional local model
  preservation. `compile_interpretations` relates identity and doubling for
  every context, result type and term, by composing the two preservation facts.
- `compiled_square` combines that compiler-preservation equality with
  `MatrixDoubling.embedArrow.commutes`: the sides are the compiled matrices and
  the connectors are the actual first-copy injection matrices.
- `tripleTerm`, `triple_doubled`, `triple_entries` check a nonidentity matrix
  primitive under a captured let and pair/projection. Expected coefficients are
  three on the first copy and zero across copies. `triple_entries` rewrites by
  the public compiler-preservation theorem before checking these entries.

These adapters introduce no new syntax induction or matrix algebra proofs.
The original `generated_coefficients`, `linear_example_with_tail`, and
`joint_outputs_agree` remain checked uses of the migrated concrete backends.

## Statement review

The missing connection was architectural: existing backend correctness could
prove agreement, but did not use the shared map or agreement constructions.
The old conclusions remain the expected statements; they were not weakened to
make the migration pass.

`MatrixCompiler.sound` still denotes the original matrix action conjugated by
encode/decode. Its compiled theorem and square retain all commutative semirings,
source terms and coordinate inputs. `jointSquare` retains the subtype of inputs
with equal decoded observations. `agree_preserving_tail` still quantifies over
all terms, all typed stack tails and all tail values, returning the entire
bytecode result, including the unchanged tail. No injectivity of arbitrary
observation maps is assumed.

The new matrix compiler claims concern equality of finite matrices, not equality
of observed functions. `Prim a b` ranges over every actual matrix between the
recursively selected coordinates, so its primitive hypotheses are inhabited.
The doubled product comparison rearranges copy-major and product-major sums;
it is not replaced by a definitional product identification. Identity retagging
preserves the coordinate carrier. The all-term square uses first-copy matrix connectors at the source and result.
The all-term theorem includes empty contexts,
unit, products and lets. `triple_entries` exercises a nonzero primitive and a
zero off-diagonal coefficient, excluding a zero-only or identity-only model.

This client specializes Felix's raw structure-preserving maps and comma squares
at `6f36d28097db7ea5f5df3263db3e8be08f74e490` (inspected Raw and Vertical).
It claims no universal closedness or completion of the wider Felix port (#8).

## Validation

Lean 4.35.0 and pinned Mathlib through the checked-in Nix/direnv environment.
`direnv exec . lake build Examples.MatrixStack` passed.
`direnv exec . ./check-foundation.sh` passed (exit 0).
`direnv exec . ./check.sh` passed (exit 0), freshly rechecking all 79 modules and
the transitive axiom audit after the final source changes. Logs are
`/tmp/conaled-spec15/foundation14.log` and `/tmp/conaled-spec15/check14.log`.
`git merge integration/spec-15` confirmed the incorporated review base above;
`git diff --check` passed.
`Applications.Linear.FirstOrderNaturality` now imports Compiler explicitly because it uses
`sound` and `linearCombination`; Maps imports only Operations to avoid a cycle.
No runtime behavior, proof infrastructure, toolchain or dependency pin changed.

After incorporating ticket 18, both required commands passed again (exit 0):
`direnv exec . ./check-foundation.sh` and `direnv exec . ./check.sh`.
The latter freshly checked all 84 modules and passed the exhaustive axiom audit.
Logs: `/tmp/conaled-spec15/foundation14-integrated.log` and
`/tmp/conaled-spec15/check14-integrated.log`. No source edits followed validation.
