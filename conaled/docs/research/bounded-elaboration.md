# Bounded composable elaboration

This experiment for [#147](https://github.com/VladimirMarko/conaled/issues/147)
implements the elaboration contract proposed in the
[codata and elaboration research](codata-elaboration-termination-contracts.md).
It is an ordinary Lean library under `Applications/Elaboration/`, imported by
the public entrypoint. Its syntax and interfaces may evolve. Its theorem
statements describe a bounded fragment, not a replacement for Lean elaboration
or a proposed universal IR.

## Supported source and target

`Source Γ Δ t` has natural literals, typed local and declaration references,
natural metavariables, addition, vector construction and a dependent consumer.
The context `Γ` and declaration signature `Δ` are lists of object sorts.
`Var Γ t` is a typed de Bruijn reference, so callers must provide an already
scoped, typed body. `Phrase` additionally permits an overloaded outer literal
whose sort has not been selected. This experiment does not parse raw strings
or infer arbitrary unannotated bodies.

The object sorts are natural numbers and a dependent packet
`(n : Nat) × Vector Nat n`. A vector source computes its length and entry,
then produces that many copies of the entry. The consumer takes the length
and a vector indexed by it, and returns the length plus the sum of the entries.
`Core` makes the pair constructor and dependent elimination explicit. It is a
separate small target syntax, not an existing Agda or Lean core serialization.
Source and core denotations specify each operation separately. `Faithful`
requires equality for every metavariable interpretation, local valuation and
declaration valuation. A well-typed target computing different entries fails
this relation.

This fragment has a fixed principal object universe, zero. The natural
identifier on a vector constructor denotes a universe variable to be solved
to zero. This is a monomorphic universe check: there is no universe algebra,
cumulativity, universe-polymorphic generalization or solver for arbitrary
universe inequalities. The annotation participates in `Core.Typed` and final
acceptance; a missing assignment or an assignment to one fails. Both sorts
are inhabited Lean types. The development does not transfer native Lean
identity, cubical paths or modal principles to another setting.

## Relation and evidence

| Interface | Meaning |
|---|---|
| `Resolves p expected s` | Declarative resolution policy: known bodies match their optional expected sort; overloaded literals require an expected sort. |
| `Elaborates p expected o` | The inferred, scoped target preserves the selected source meaning; its explicit constraints have exactly the source obligation meaning and characterize target assignment typing. |
| `Assignment` / `Solves` | Partial assignments for natural metavariables and universe variables; every listed obligation must hold. |
| `Pending p expected o cs` | An intermediate problem may strengthen the output constraints. Its solution set must be contained in the original set. |
| `Accepted p expected f` | The final output is admissible and its retained assignment solves all its constraints. |
| `DeclarationElaborates δ p expected f δ'` | Closed declaration elaboration extends the signature by the inferred sort, preserves every old declaration, and installs the selected source value in the new head. |

`Output` and `Final` retain code, type, constraint data and assignment functions
in `Type`. Their constructors contain no soundness proof fields. Success is
proved separately for `elaborate`, `elaborateReordered`, `checkConstraints`,
`finalize` and `install`. `Assignment.value` has a mathematical default for
unassigned holes, but `finalize` cannot accept a referenced hole through that
default: its `.assigned` obligation requires an actual `some` value.

Assignment refinement preserves previously assigned meta and universe values.
Constraint refinement restricts the set of possible solutions. These are
different directions and have separate composition theorems. `Pending.refine`
and `Pending.accept` connect successive constraint problems to final acceptance.
`Source.eval_refine` proves that a solved source keeps its computed value under
further assignment refinement. The checked length problem adds `metaEq 3 5`
to an open vector's requirements, then accepts the computed packet from that
refined solution.

The elaborator generates constraints; the caller supplies assignments. It is
not a unification engine. Solving larger problems or importing assignments from
an external solver would require preserving the same checked contract.

## Compatibility and strategy reuse

`lower_subst` relates source substitution to target substitution, including
substitution of a computed vector length. `Source.eval_subst` and
`Source.subst_comp` give semantic and composition laws.
`lowered_substitution_typed` requires both the old source obligations and the
obligations of supplied substitutions. Substitution cannot silently introduce
an unresolved hole. `weaken_sound` handles added local context entries;
`environment_extension` and `lowered_environment_extension` handle added
declarations. `install_admissible` proves the full closed-declaration judgment.

`loweringSquare` uses the existing `Relational.RelSquare`. A second pass
reverses the operands of every natural addition and proves semantic and typing
preservation. `reorderedLowering` is their existing `Relational.compose`;
`translation_composition` applies its preservation law. The two elaborators
therefore produce different syntax while sharing `Elaborates`.
Commutativity of pure natural addition justifies this particular strategy.
It does not authorize reordering effects or noncommutative operations in a
future setting. Constraint refinement also reuses relational squares and their
composition rather than defining another generic category of contracts.

## Separate claims

- **Soundness:** `elaborate_sound`, `elaborateReordered_sound` and
  `finalize_sound` connect successful executable passes to the declarative
  judgments. `lower_sound` supplies source fidelity independently of typing.
- **Fragment completeness:** `resolve_complete` and `elaborate_complete`
  cover exactly `Resolves`, with its typed bodies and explicit overload policy.
  `checkConstraints_correct` is an equivalence for a supplied assignment.
  None claims that constraint search finds every possible assignment.
- **Search termination:** resolution is finite case analysis; lowering and
  reordering recurse on syntax; final checking recurses on a finite constraint
  list. Lean checks those definitions structurally. There is no fuel exhaustion,
  unrestricted proof search or host-performance bound in this pass. Supplied
  assignment functions have Lean's total-function meaning; this is not a
  compiler/runtime adequacy theorem for arbitrary external functions.
- **Coherence:** `elaborations_coherent` compares successful outputs under the
  same request and expected-type policy, using the same metavariable
  interpretation and environments. Different unsolved assignments may compute
  different lengths. Coherence does not identify those choices.
- **Diagnostics:** ambiguous overload and expected-sort mismatch arise before
  code generation. `checkConstraints_diagnostic` proves that the returned
  obligation occurs in the problem and fails under the supplied assignment.
  Such failure does not assert global unsatisfiability.

## Checked uses and caller effort

`Applications/Elaboration/Examples.lean` constructs a declaration with length
`2 + 3` and entry `7`. Through the public soundness and finalization results,
it obtains a retained packet with length five and entries `[7,7,7,7,7]`.
Installing that declaration supplies a second declaration's dependent consumer,
which computes `40`. Another packet with the same length but entry `8` is
observably different and cannot satisfy the first source's fidelity contract.
The cases also cover substitution, weakening, environment extension, both
strategies, refined constraints and the distinct rejection paths.

An ordinary Lean caller writes constructors, typed variable references, an
optional expected sort, and partial assignment functions. `elaborate` returns
an `Except Diagnostic Output`; `finalize` checks the supplied assignment;
`install` extends a closed declaration environment. Generic clients use the
soundness theorems rather than recreating preservation proofs for each term.
`Examples.producer_accepted` and `consumer_accepted` show that proof burden.
The caller currently chooses universe-variable identifiers and supplies solved
values explicitly. Automatic allocation and inference are future producer work.

For [#116](https://github.com/VladimirMarko/conaled/issues/116), an additional
surface can supply this bounded `Source` or target another fragment entirely.
It must justify its own source correspondence, scoping and typing before using
this pass. The present two strategies demonstrate common-contract reuse; they
do not establish that Agda-like or slean parsers exist. For
[#117](https://github.com/VladimirMarko/conaled/issues/117), these checked
constructors and diagnostics can inform an authoring fixture, but no matched
LLM authoring experiment was run here. The independent #107/#108 assessment
and its fresh theorem remain untouched.

No lazy runtime, unrestricted codata, Agda importer, arbitrary dependent
inference or global mathematical-setting translation follows from this bounded
model. Those routes remain possible without requiring them to adopt this
syntax or its eager finite-vector implementation.
