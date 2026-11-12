# Oracle-relative computation and symbolic realization

[#498](https://github.com/VladimirMarko/conaled/issues/498) adds a finite program
language whose denotations are exactly the partial functions recursive in one
supplied oracle. It proves that an oracle answering ordinary halting still
cannot decide halting for its own enlarged class. A finite symbolic compiler
preserves complete partial denotations. An ordinary executable code translation
requires an actual ordinary program implementing the oracle.

## Source and scope

The source is Turing's [*Systems of Logic Based on Ordinals*, §4](https://people.math.ethz.ch/~halorenz/4students/Literatur/TuringOrdinalLogic.pdf),
printed pp. 172–173, PDF pages 21–22 counting from one. The inspected scan has
SHA-256 `e55e9c7060a85658f8228a777dcc4c739ced805eb635a93add60920e2a78bde6`.
Its prefatory discussion is not part of Turing's text. The PDF is not copied
into the repository; no explicit redistribution license was established.

Turing considers an oracle for number-theoretic problems and shows that its
machines cannot decide their own circle freedom, which concerns infinitely
many output figures. This development is a modern partial-recursive halting
adaptation of that relative-diagonal argument. Finite-input termination is not
circle freedom, and the ordinary halting oracle below is not identified with
Turing's original oracle. No historical tape-machine equivalence or full
ordinal-logic construction is asserted.

The implementation reuses Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`, whose source files are Apache-2.0:

- [RecursiveIn.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/RecursiveIn.lean)
  defines the actual closure under relative partial recursion and oracle
  substitution.
- [PartrecCode.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/PartrecCode.lean)
  supplies ordinary codes, evaluation, coding adequacy, and bounded evaluation.
- [Halting.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Halting.lean)
  supplies `ComputablePred.halting_problem` for ordinary code at a fixed input.
- [TuringDegree.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/TuringDegree.lean)
  identifies singleton-oracle reducibility and derives its composition from
  substitution. This study needs neither a new degree theory nor its quotient.

## Programs, observations and adequate coding

[Core.lean](../../Applications/OracleComputation/Core.lean) has nine constructors:
zero, successor, the two unpairing projections, query, pairing, composition,
primitive recursion and unbounded minimization. Queries contain no function or
proof; `eval` receives a possibly partial oracle separately. Minimization uses
Mathlib's `Nat.rfind`, including the requirement that earlier tests be defined.
A later successful test cannot bypass an earlier divergent computation.

`eval_recursiveIn` proves soundness against `Nat.RecursiveIn {oracle}`.
`recursiveIn_iff_exists_code` proves the converse by induction on every
constructor of the Mathlib closure. Thus the denotation covers that entire
relative class. It is not restricted to a fixed finite collection of queries,
and it is not surjective onto all native functions.

[Coding.lean](../../Applications/OracleComputation/Coding.lean) emits finite
postfix instruction lists. A stack parser constructs source syntax and rejects
unknown tags, missing operands and non-singleton final stacks. `parse_emit`
proves recovery; the standard encoding of finite lists gives natural-number
indices. `ofIndex_index` proves the retraction, and
`recursiveIn_iff_exists_index` gives the resulting adequate enumeration.
Malformed numeric indices default to the zero program. This convention does
not affect the recovery equation used in the diagonal.

These functions construct concrete descriptions without reading the oracle.
The coding theorem does not assert that the two-argument universal evaluator
is itself relative recursive. That stronger universal-execution theorem is
neither assumed nor needed for the separation proved here. No new
`Primcodable` instance for the source syntax is claimed.

The observations are result membership `v ∈ eval oracle c n` and domain
membership `(eval oracle c n).Dom`. The latter is termination in this partial
semantics, not a timeout, fuel bound, syntactic validity or physical behavior.

## Two separations

[Separation.lean](../../Applications/OracleComputation/Separation.lean) defines
`OrdinaryHalts c` directly as `(Nat.Partrec.Code.eval c 0).Dom`. A classical
case distinction produces a total mathematical answer, encoded as 0 or 1, for
each ordinary code index. `haltingAnswer_boolean` verifies that range and
`haltingAnswer_one_iff` connects it to the independent ordinary property.
`haltingOracle_not_partrec` reduces any proposed ordinary implementation to
Mathlib's impossible ordinary halting predicate. Noncomputability is proved
from the actual enumeration and evaluation relation, rather than stipulated
as a field of an oracle interface.

The query program realizes that answer relative to the supplied oracle.
However, for every supplied partial oracle O, define

```
SelfHalts O n := (eval O (ofIndex n) n).Dom
```

Suppose a total O-relative function d returns zero exactly for non-halting
indices. Adequacy provides a code c for d. The explicit program
`rfind (comp c left)` searches the same total test `d n = 0` at every candidate
index. `search_constant_dom` proves that it terminates exactly when d n is zero.
Evaluating this program at its own recovered index contradicts the stipulated
answer. `no_relative_halting_decider` formalizes this argument; it assumes
neither a universal solver nor representability of an arbitrary native
anti-diagonal function.

`jump_not_recursiveIn` applies the result to the mathematical 0/1 self-halting
answer. `haltingOracle_cannot_solve_own_jump` instantiates it at the actual
ordinary halting oracle. This is a nonvacuous enlarged class: ordinary
computations and the additional halting query have syntax, while its own
self-halting remains outside its relative closure. The theorem does not claim
jump completeness, an entire hierarchy theorem, or a physical impossibility.

## Realization contracts and symbolic compilation

[Compilation.lean](../../Applications/OracleComputation/Compilation.lean)
interprets artifact instructions on a stack of partial functions. This
interpretation is defined independently of the source evaluator; its operation
clauses share the specified partial recursion and search operations. The
syntax parser and semantic interpreter are different instances of the same
instruction machine. `run_emit` preserves an arbitrary stack tail, exposing
operand order and composition. `artifact_emit` proves equality of complete
partial denotations; `artifact_result` and `artifact_termination` retain the
selected observations. Malformed artifacts have no denotation, which is
different from a valid artifact denoting a divergent program.

A query instruction is the finite list `[4]`. Its generation is meaningful
when the selected interpretation supplies the halting oracle, despite the
proved absence of an ordinary implementation. Generating that instruction is
not an implementation of its mathematical primitive.

There are concrete, composable realization contracts:

| Construction | Required evidence | Result |
| --- | --- | --- |
| Extensional oracle replacement | Equal partial answers at every input | Equal source denotations |
| `eval_subst` | The source oracle is recursive in the target oracle | Relative computability of each source denotation |
| `substitute_realizes` | A selected target program realizes the source oracle | An executable code transformation preserving full partial behavior |
| `substitute_comp` | Two selected program substitutions | Their exact syntactic composition law |
| `toOrdinary_correct` | A selected ordinary `Nat.Partrec.Code` for the oracle | Ordinary code with equal partial denotation |
| `ordinary_code_exists` | A proof that the oracle is partial recursive | Existence of an ordinary realizing code |

The last row supplies a proposition, not a chosen executable witness. The
explicit translation takes such a witness as data. Its minimization case
adjusts to Mathlib Code's different `rfind'` argument convention; this macro is
covered by the preservation theorem.

These are particular realization relations with explicit composition premises,
not a mandatory hierarchy of mathematical, artifact, effective and physical
capabilities. No physical interpretation is selected. A target's computational
capability does not select its logic or supply arbitrary proposition proofs.
The Lean results use the repository's verification metatheory; they do not
establish foundation independence or adopt an external evidence API for #489.

## Checked clients and statement review

[Examples/OracleComputation.lean](../../Examples/OracleComputation.lean)
retains the following clients of the public results:

- An ordinary program adding two realizes the query. A source program searches
  for zero, then queries twice; it yields four for every input. Its explicit
  instruction list and ordinary compilation are connected to the preservation
  theorems, so reversed composition order would not satisfy the example.
- Concrete ordinary zero and divergent programs receive positive and negative
  halting answers. The divergent ordinary code comes from the proved compiler,
  not an assumed negative instance.
- The mathematical halting query has an artifact denotation, while no
  ordinary code agrees with that denotation at every input.
- Relative self-halting is impossible for the halting-oracle class and for an
  ordinary computable oracle. Neither instance requires contradictory premises.
- Total constant-one answers make an unbounded search diverge; replacing them
  with constant-zero answers makes it terminate. Unequal answers also change
  query results. Thus preservation across changed oracles needs actual premises.
- Two macro realizations compose through the public substitution law. Parser
  and semantic-interpreter rejection cases retain malformed-artifact behavior.

Statement review checks that the closure includes minimization, adequacy is
relative to one fixed oracle, and the new coding retraction is proved. The
ordinary and relative enumerations remain distinct. The diagonal needs a total
decider; it does not mistake a partial recognizer for a decider. Its zero-answer
condition needs no extra 0/1-range premise. The canonical mathematical answers
do have that range. Whole-program totality is never inferred from oracle
totality. Compilation equalities preserve divergence as well as terminating
values and are quantified over every source program.

## Reuse and remaining scope

Existing [diagonal constructions](../../SquareKit/DiagonalConstruction.lean)
prove selected-row fixed-point facts and reject a Boolean-function surjection.
[Coverage transport](../../SquareKit/DiagonalCoverage.lean) transports an
already supplied representation; it does not construct relative program
coverage. The present partial-computation diagonal uses an actual code rather
than adding an impossible surjection hypothesis to those interfaces.

[Assemblies](../../SquareKit/Assembly.lean) already require ordinary
partial-recursive trackers and provide `Hom.has_code`.
[Assembly partial maps](../../SquareKit/AssemblyPartialMap.lean) impose ordinary
recursively enumerable support conditions. A halting oracle cannot silently
be inserted as an ordinary tracker; these useful contracts remain unchanged.
The [clean reversible oracle](../../Applications/Uncomputation/Oracle.lean)
proves scratch restoration for a supplied Boolean function, not that the
function has an effective implementation.

[#109](https://github.com/VladimirMarko/conaled/issues/109) retains general
categorical recursion and fixed-point interpretation work. This local study
does not add recursion to the existing total typed compiler. Its partiality,
minimization and oracle-realization requirements are concrete inputs to that
work and to [#493](https://github.com/VladimirMarko/conaled/issues/493).
Further universal oracle evaluation, relative recursion theorems, historical
machine equivalences and external-foundation comparisons require their own
proofs. None is silently supplied by this slice.

The public entrypoint imports the examples and their four library modules.
Acceptance uses the repository's full build and exhaustive axiom audit on the
committed candidate, plus independent Standards and Spec review. The external
handoff records exact candidate identities and results; this note does not
substitute for those checks.
