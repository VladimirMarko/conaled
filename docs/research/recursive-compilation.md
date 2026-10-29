# Compiling finite list recursion

Issue [#218](https://github.com/VladimirMarko/conaled/issues/218) implements the
finite-fold experiment from [the recursion priorities](recursion-and-reactive-priorities.md).
The source has an explicit recursive construct and typed scalar bodies. One
compilation supports ordinary evaluation and an interpreter that counts executed
primitives and list visits. Its preservation contract also supports pushing a
postprocessing term through a fold.

## Source, target and termination

[Program](../../SquareKit/ListFoldCompiler.lean) has two constructors:

```text
fold : Term [] accumulator → Term [element, accumulator] accumulator
       → Program element accumulator
post : Program element accumulator → Term [accumulator] result
       → Program element result
```

The bodies use the existing [first-order language](../../FirstOrder.lean): typed
variables, products, projections, local bindings and supplied primitives. Lists
are the outer runtime input, `List (Val B element)`; this experiment does not add
list types to the shared scalar type grammar. A body receives the current element
and accumulator, while the seed is closed. There are no free external contexts,
nested list folds inside a body, or arbitrary recursive calls.

`iterate` specifies source meaning by recursion on the input list. `eval` adds
structural recursion over the enclosing program. `iterate_executes` constructs a
finite source execution with exactly `xs.length` body visits. This count concerns
visits, independently of the primitive-cost observation below. Scalar meanings
are total Lean functions; an arbitrary supplied primitive is not proved to
terminate in an external runtime.

`compile` instead recurses over the finite program syntax and invokes the existing
first-order compiler on each seed and body. Its type has no runtime-list argument.
`compile_fold` states by definitional equality that compiling a source fold emits
one target fold applied to the compiled seed and body. Lean checks the separate
structural recursions of compiler and evaluator; compilation never unrolls the
runtime list.

A target supplies scalar operations, list arrows, `fold` and `post`. Its `Sound`
contract requires scalar soundness, a fold-denotation equation and a postcomposition
equation. `compile_sound` derives preservation for every source program from these
laws. The fold equation is an additional obligation beyond the scalar cartesian
operations. The ordinary target uses functions and `List.foldl`.

## Actual counted execution

[Resources.FoldCompiler](../../Applications/Resources/FoldCompiler.lean) interprets
scalar arrows as functions returning `Measured value Nat`. Composition and pairing
execute their operands using the existing resource `bind`; primitives execute
their supplied meaning and add their declared constant charge. Wiring costs zero.
The list arrow executes the compiled seed once and then uses `Resources.run` to
execute the compiled body, charging one additional unit per consumed list cell.
Postprocessing executes its compiled term after the fold.

`scalar_cost` proves the primitive cost of each compiled scalar term.
`compile_cost` proves the resulting program formula:

```text
cost(fold seed body, n) = cost(seed) + n * (1 + cost(body))
cost(post program finish, n) = cost(program, n) + cost(finish)
```

These equations follow from the instrumented interpreter. Primitive charges are
constant with respect to their inputs; input-dependent charges require a different
analysis. They are modeled operation counts, not timing, allocation or speedup
claims. The target is cartesian-sound after projecting values. It does not satisfy
cartesian equalities of costs: duplicating an effectful arrow can duplicate work.

The `erasure` square uses the existing `Resources.erasureSquare`. Fold soundness
reuses `Resources.run_value_fusion`; a checked reweighting example applies
`Resources.reweight_run` to the actual compiled square-accumulation transitions.

## Two consumers and preservation failures

[The checked clients](../../Examples/RecursiveCompilation.lean) use the existing
`Arithmetic.Prim` and its integer meaning. Total accumulates `acc + x`. Sum of
squares binds `x*x` once and accumulates `acc + square`. Independent source
specifications identify these with `xs.sum` and `(xs.map (fun x => x*x)).sum`.
Each primitive, including the zero seed literal, costs one.

| Input | Total: value, cost | Sum of squares: value, cost |
| --- | --- | --- |
| `[]` | `(0, 1)` | `(0, 1)` |
| `[2, -1, 3]` | `(4, 7)` | `(14, 10)` |
| Any length `n` | `xs.sum`, `1 + 2*n` | sum of squares, `1 + 3*n` |

`fold_fusion` reuses `SquareKit.ListFusion.foldl_reachable`. Its obligations are an
invariant containing the seed and closed under the body, preservation of the seed
by a map `h`, and commutation of `h` with the body on reachable states.
`compiled_fusion` combines this law with compiler correctness across any two sound
targets. Both clients instantiate it to move doubling from a postprocessing term
into the accumulator body; checked instances cross ordinary and counted targets.
This preserves observed values. For total on `[1,2]`, postprocessing costs six and
the fused body costs seven, so cost equality would be false.

The examples also establish the failures that the hypotheses exclude:

- A target with the same sound scalar operations but a fold that ignores every
  input element computes zero for total on `[1]`. `bad_fold_law` proves that it
  cannot satisfy the fold contract with its actual function observation.
- Doubling the accumulator while adding an unchanged input fails the body
  commutation law at accumulator zero and input one. The claimed output-fusion
  equation also fails on `[1]`.
- An endlessly silent recursive machine has no finite evaluation, by the existing
  `Progress.silent_no_evaluation`. The selected grammar has no constructor for
  that general recursive call.

## Reuse, provenance and remaining obligations

The algebraic source of this experiment is finite list iteration and its fusion
law, already formalized in [ListFusion](../../SquareKit/ListFusion.lean).
The [ADWH-derived bracketing development](../../Applications/Bracketing/Interpretation.lean)
already uses fold fusion, and its [recursive algorithm](../../Applications/Bracketing/Recursive.lean)
already proves well-founded termination by strict split lengths. Those results
were inspected as existing foundations. This change adds a typed source-to-target
contract around a bounded fold fragment; it does not replace the algorithm proofs
or reconstruct a general initial-algebra library.

An ordinary client can use Lean functions directly. A source client authors its
seed/body terms, primitive meanings and any source-specification theorem. A new
target authors operations and their `Sound` laws once. A fusion client supplies
its invariant, seed equation and body equation; it does not repeat compiler
induction. Cost clients additionally choose explicit primitive charges and a
cost observation. The examples preserve this separation of authored mathematics
from reusable transport proofs.

General partial recursion, guarded fixed points, indexed recursive data, retained
incremental state and automatic incremental A* remain outside this experiment
under [#109](https://github.com/VladimirMarko/conaled/issues/109) and
[#111](https://github.com/VladimirMarko/conaled/issues/111). No universal fixed-point
preservation follows from the finite-fold contract.
