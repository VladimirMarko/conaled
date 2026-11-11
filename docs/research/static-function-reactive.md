# Static functions before reactive execution

Issue [#483](https://github.com/VladimirMarko/conaled/issues/483) adds a bounded
source route for static function parameters. `Expr.mapPair body input` embeds
in the existing typed lambda language as a combinator accepting a function:
`(fun f => (f input.1, f input.2)) (fun x => body)`. Its residual contains two
first-order substitutions. The delayed consumer compiles that residual once
and executes the stored circuit on subsequent inputs.

The reusable source and binder laws are in
[StaticFunctionSpecialization](../../SquareKit/StaticFunctionSpecialization.lean).
The [reactive wrapper](../../Applications/FRP/StaticFunctionReactive.lean)
provides named identity, negation and captured-mask bodies and a finite list
of mapping stages. [Checked examples](../../Examples/StaticFunctionReactive.lean)
retain a direct first-order client alongside the staged client.

## Source and phases

`Expr` permits first-order leaves, application of a supplied first-order body
under one binder, pairs, projections and `mapPair`. Contexts and residual types
are the existing first-order types: ground, unit and products. Function values
cannot occur in those contexts or results. The generic theorem is conditional
on an interpretation of primitives, as in the existing compiler. The executable
client specializes it to total finite Boolean gates.

The generic source can use surrounding first-order values in a function body;
all such applications occur locally and no environment escapes. The reactive
frontend's `StaticBody` has just its Boolean argument. Static Boolean captures
are literal gates. `maskBody mask` accepts a configuration Boolean before any
runtime input is supplied. Arbitrary recursion, effects during specialization,
whole-Lean compilation and dynamic closure storage are outside this syntax.

`source_correct` relates the explicit STLC embedding to source meaning in every
open environment. `residual_correct` relates the first-order residual to that
same meaning. Residualization is total structural recursion on the finite
source and finite body trees. Its result type has no lambda, application or
function type constructors. These facts establish elimination and termination
for this selected syntax; the categorical source compiler alone would not.

Capture avoidance reuses `FirstOrderCompiler.Term.subst`, `liftSub` and their
semantic laws. `residual_substitution` and `residual_renaming` quantify over open
contexts and agreeing environments. The retained separator substitutes an open
Boolean argument beneath a fresh let binding whose value is false; the result
remains the argument, including when it is true. The STLC embedding uses the
existing higher-order renaming law beneath the combinator's function binder.

`Arithmetic.Staging` remains useful for evaluating a static integer and inserting
it in a first-order body. It does not provide higher-order elimination. The
existing STLC reduction relation supplies sound beta steps, but no general
normalization algorithm. This route needs neither general normalization nor a
runtime closure representation.

## Reactive observations and admission

The independent source machine outputs the previous pair and retains the newly
mapped pair. With negation, seed `(false,true)` and inputs
`[(false,false),(true,false),(true,true),(false,true)]`, the outputs are
`[(false,true),(true,true),(false,true),(false,false)]` and final state is
`(true,false)`. These values were frozen before lowering. The two-input prefix
ends in `(false,true)`; restarting there gives the remaining ordered outputs.

`machine_correct` proves equality with that initialized machine through the
existing reactive compiler. `run_correct` covers every current continuation
and every finite input list, preserving both output order and final state.
It does not require restarting from the seed. Runtime tests independently use
Boolean operations, rather than the source evaluator, to check the compiled
runner.

`assess` consumes a request and a logical storage capacity. A static request
constructs the actual residual circuit and checks retained cells plus its arena.
Success carries that bound for that executor. Insufficient capacity is a
rejection of the declared bound; semantic correctness remains valid. Dynamic
function arguments, escaping environments and opaque native functions return
`unsupported`. This means that this route lacks the required representation or
analysis, not that no implementation of their behavior is possible.

`admitted_uniform` bounds every arena allocation prefix at every stream prefix.
Finite local execution and conditional service use the existing
`Indefinite.Program` proofs for the compiled circuit. Input availability, fair
scheduling and sink acceptance remain explicit finite-wait premises; no physical
deadline, crash recovery or host allocator guarantee follows.

## Regional value boundary

`boundary_correct` accepts any producer with a proved ordinary pair-valued
boundary, regardless of the producer's internal language. The concrete client
executes the existing rich sum/case producer, runs a circuit duplicating its
Boolean result, then executes the specialized pair transform and delay.
`regional_correct` compares this pipeline with the independently defined rich
oracle and native mapping.

`RegionalExecutes` carries the raw producer's work and allocation derivations,
the actual adapter circuit derivation and the consumer circuit derivation.
The selected schedule retains their arenas through tick completion and charges
one Boolean boundary copy and one pair copy. `regional_uniform` includes three
input cells, two retained state cells and every prefix of this execution's
allocation trace. This conservative schedule avoids claiming reclamation that
has not been implemented. It is a local extension at a value boundary; it does
not enlarge the closed F/D/N `Regional.Plan` catalog or assert that its old
admission record covers this new executor.

## Costs and duplication

[StaticFunctionCost](../../SquareKit/StaticFunctionCost.lean) constructs the
residual together with a syntax-work count. Substitution counts visited source
constructors and materialized substitution images. Weakening an image beneath
a binder is charged by its constructor count. The model counts tree copies
even when a host may share values; it is not a wall-clock or heap model. The
measured traversal's returned syntax is the syntax compiled by `program`, and
`measured_correct` proves equality with the uninstrumented residualizer.

Specialization work, residual nodes, target tick work and target arena are
reported as separate quantities by
[test-static-function-reactive.py](../../scripts/test-static-function-reactive.py).
A retained family repeats identity `mapPair`. Its output function is unchanged,
but its residual has `4 * 2^n - 3` constructors. No cancellation optimization is
performed. This separates semantic simplicity from code growth and prevents a
claim of universally bounded specialization growth or guaranteed speedup.

The executable fixture reports these deterministic model counts. They can be
reproduced with `direnv exec . python3 scripts/test-static-function-reactive.py`
after building the example module.

| Static stages | Specialization work | Residual nodes | Tick work | Tick arena |
|---|---:|---:|---:|---:|
| Negation | 15 | 9 | 21 | 131 |
| Identity | 13 | 7 | 17 | 113 |
| Captured true mask | 21 | 15 | 29 | 173 |
| Negation then negation | 39 | 21 | 41 | 235 |
| No mapping stages | 3 | 3 | 11 | 79 |

These counts concern the transition body. Seed evaluation is separate, before
reactive execution. The two retained Boolean state cells are additional to the
tick arena. The runtime suite compares 6,820 continued runs, covering five
configurations, all four starting continuations and every pair-input word of
length zero through four. Each run also checks a two-input prefix/restart split.
Four rich-input cases exercise the concrete regional boundary. Positive capacity,
insufficient capacity, dynamic-function, escaping-environment and unknown-native
outcomes are checked through the public admission path.

## Author effort and next contract

The ordinary client is a Boolean pair mapper and an initialized delay. A direct
first-order author supplies seed and transition terms. The staged author supplies
unary bodies and a list of stages; `mapPair`, `liftBody` and `stagedBody` hide
context indices and delay wiring. New primitive bodies still use the existing
typed syntax internally. The author must provide a source-meaning connection
for a new helper and retain its examples. This is an implementation comparison,
not an independent author trial or measured usability result.

The example does not justify adopting a general runtime-closure interface.
A next bounded experiment could use a finite function tag selected at runtime,
with an explicit finite captured-state representation and an exhaustive dispatcher.
Its contract would need code identity/version, validity and observation of
captured state, dispatch and copy costs, retained lifetime, and a migration
relation preserving both code selection and captures. Invalid tags and incompatible
captures would need actual rejection. Admission would need evidence for that
specific dispatcher and state shape. The present unsupported outcomes are not
permission to reinterpret function values silently as such tags.
