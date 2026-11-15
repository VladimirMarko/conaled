# #1034: bounded foundation import-footprint correction

## Status and scope

Read-only preparation against formal source candidate
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`. This assessment examined integrated
root Lean modules, `SquareKit`, `Applications`, and `Examples`; it excluded
archives, historical formalizations, and experiment trees. The inventory has
954 modules including `ProofAudit`. No formal source was changed or compiled
for this assessment. This file is the sole written output.

The recommended correction is exactly two first-line replacements:

| File | Current import | Proposed import |
| --- | --- | --- |
| `Squares.lean` | `import Lean` | `import Init` |
| `Dependent.lean` | `import Lean` | `import Init` |

Keep every other byte of these modules unchanged. Preserve their module names,
namespaces, declarations, theorem statements, proof bodies, and existing public
entrypoints. Complete checkpoint 039 before making or testing this correction;
then use a new frozen candidate in the existing formal implementation/review
loop. Whole-book chapter order remains unchanged.

## Evidence and actual dependencies

`validation/1033-native-environment/import-footprint-experiment.json` records a
scratch-only replacement of the first line of `Squares.lean`. It compiled with
the pinned native launcher, exit 0, no diagnostics, in 4.7896 seconds, with
491,512 KiB reported maximum RSS and 2,944 major faults. I independently checked
that the scratch source differs from the current original only by this import
line. The earlier original-source sample reported by the coordinator was
136.82 seconds, 844,264 KiB maximum RSS, and 144,730 major faults; its record is
`validation/1033-native-environment/native-squares-resource-sample.json`.
These are individual observations under changing cache/memory conditions,
not a controlled project-wide speedup estimate.

`Squares` defines representations, commuting squares, products, coproducts,
exponentials, and a Boolean obstruction. It uses ordinary `Type`, functions,
`PUnit`, `Prod`, `Sum`, `Subtype`, equality, `funext`, and elementary tactics.
It neither uses Lean expression/environment APIs nor defines metaprogramming
commands. The scratch compilation directly supports `Init` sufficiency for
this unchanged body.

`Dependent` defines the split family model and its certificates, using `Sigma`,
`Fin`, `Nat`, `HEq`, equality transport, functions, and ordinary proofs. Its
destructuring tactics include `rcases` and `obtain`; the pinned distribution's
`src/lean/Init.lean` publicly imports `Init.RCases`, whose source supplies their
syntax. Its other observed dependencies likewise belong to `Init`, including
the `Fin` example and `Nat.lt_succ_self`. There is no `Lean.*` API use or custom
elaboration. This is source-based support for the second replacement, not a
claim that the changed module has already compiled.

Inspected original source hashes:

- `Squares.lean`: `2556c4c895a747bc0092239b5dc5b220e8a6d4d6cf8a6f9fe66ab96fa2462dc7`
- `Dependent.lean`: `3b00a4e84d18cebe0fec6bbc94de957d60ecff321808149936bb76278f5bde1b`

## Consumers and expected reach

A static graph of integrated source import headers finds 22 direct consumers
and 480 transitive consumers of `Squares`, and seven direct consumers and 37
transitive consumers of `Dependent` (counts exclude each root itself).
Together the roots and their consumers cover 490 modules. Replacing both
imports removes every path to an explicit *local* umbrella `import Lean` for
482 modules. External dependency import closures were not expanded: many of
these consumers independently import Mathlib, Std, or Lean tactic modules.
The count therefore does not mean 482 modules become Init-only or receive the
measured Squares improvement.

Concrete direct consumers match the mathematical interfaces: `SquareCompiler`
uses `Squares.Rep` and commuting-square operations; `SquareKit.Relations`
constructs relational views of those squares; `SquareKit.EquationTranspose`
and `Applications.Languages.Witnesses` use the same foundation without an
independent external-library import. `SquareKit.TypeFamily` refers explicitly
to `DependentSquares.Ext`, `Tm`, reindexing, and context-extension equations;
`Applications.Progress.DependentFeedback` and the preservation-author examples
use its existing certificates. `Verification.lean` already audits principal
theorems from both original foundations.

The integrated scan found explicit Lean metaprogramming API/command uses in
the graph tooling branch and `ProofAudit`; those modules retain independent
Lean imports. No such use was identified in either proposed foundation body.
Unresolved downstream elaboration or reliance on accidentally re-exported
facilities is exactly what the forthcoming focused and full checks must
assess. If a consumer needs a specific library API, add its actual owning
import there only after concrete evidence, rather than restoring an umbrella
dependency to a mathematical foundation.

## Lean imports to retain in this correction

There are exactly five integrated umbrella `import Lean` occurrences. The
other three are outside this two-line correction:

| Module | Actual dependence and disposition |
| --- | --- |
| `SquareKit.Internal.CoreSyntax` | Public conversion functions expose `Lean.Expr`, `Lean.Level`, and `Lean.Name`; proofs manipulate that syntax. It requires Lean data APIs. `Lean.Expr` is a plausible later narrower import, but this assessment did not validate that replacement or its consumers. Keep the current import now. |
| `SquareKit.Internal.GraphPrimitiveEnvironment` | Stores exact pinned `Lean.ConstantInfo` declarations, including expression bodies, constructors, and recursor metadata. `Lean.Declaration` owns that type and imports `Lean.Expr`; this is a possible separate narrowing, not part of the current correction. Keep the current import now. |
| `SquareKit.Internal.GraphEmission` | Uses `MetaM`, `TermElabM`, quotations, command elaboration, environment inspection, `addDeclCore`/`addDecl`, and axiom collection. It implements real host elaboration and installation. Keep its Lean import and all checks. |

`ProofAudit.lean` already explicitly imports `Lean.Util.CollectAxioms` and
`Lean.DeclarationRange`, and uses `CommandElabM`, environment/declaration
metadata, and `Lean.collectAxioms`. Retain these imports and the complete
audit. Also retain the existing explicit `Lean.Elab.Tactic.Omega` and
`Lean.Elab.Tactic.NormCast` imports in the affected application/example
modules. `Compiler.lean` and `FirstOrder.lean` import `Std`, not the Lean
umbrella; changing them would be an additional investigation and is outside
this recommendation.

## Validation boundary

Focused compilation should first resolve `Dependent`'s currently untested
Init-only body and representative existing consumers; it should preserve the
source/import identities and report actual results. The full fresh and
guarded incremental project checks, managed proof audit, audit regression,
independent Standards/Spec reviews, and final candidate verification remain
the existing acceptance requirements. They also assess all downstream
elaboration and mathematical interfaces after the import change. Do not treat
the scratch Squares timing, this plan, or #1033 environment acceptance as
formal candidate acceptance. The changed import headers necessarily change
module dependency metadata, so identical old/new `.olean` hashes are not an
appropriate requirement for this correction.
