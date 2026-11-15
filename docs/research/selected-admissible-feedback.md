# Selected admissible feedback

Issue [#451](https://github.com/VladimirMarko/conaled/issues/451) recovers the
selected-feedback declarations in Felix revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`. It does not add traced-category laws.

## Source correspondence

| Pinned declaration | Checked recovery |
| --- | --- |
| `Raw.agda`, `Traced.WF`, `Traced.trace` | `SelectedFeedback.WF`, `SelectedFeedback.trace` |
| `Instances/Function/Raw.agda`, `traced` | `FunctionFeedback.Witness`, `trace`, `selected` |
| `Construct/Product.agda`, `traced` | `SelectedFeedback.product` |
| `Subcategory/Object.agda`, `traced` | `SelectedFeedback.reindex` |
| `Instances/Setoids.agda`, unfinished selected fixed-point congruence | `selection_not_congruent`, `trace_congruent`, `outputCongruent_of_unique` |

The interface lives in [SelectedFeedback.lean](../../SquareKit/SelectedFeedback.lean).
It needs raw arrows and a product object function, not projections, pairing,
category laws or trace axioms. Admissibility is `Type`-valued. The function
witness chooses an output and a feedback state for every input, retaining both
choices. Lean stores the equation as a subtype proof; it erases that proof,
not the selected output or state. This is the nested dependent-pair witness in
the source, with Lean's `Prop`-valued equality.

[SelectedFeedbackTransport.lean](../../SquareKit/SelectedFeedbackTransport.lean)
uses the componentwise raw category from #450. Its witness is the pair of
component witnesses. Object reindexing keeps arrows between the interpreted
objects and conjugates a body through the explicitly supplied product
comparisons. The comparison points from the interpreted product to the product
of interpreted objects. Conjugation uses its inverse arrow on input and forward
arrow on output. Neither comparison inverse laws nor injectivity of the object
function is assumed.

## Cases and statement review

[SelectedFeedback examples](../../Examples/SelectedFeedback.lean) are imported
by `SquareApplications`. The body `(x,s) ↦ (s,s)` admits constant false and true
witnesses with different traces. The product example retains those two choices
in its two components. The reindexing example uses a constant object function
and the diagonal/projection comparison; its failure to be an inverse is proved.
Thus raw transport does not silently promise an isomorphism or trace laws.

For the setoid obstruction, inputs are Boolean with universal equivalence,
while state and output have equality. The body is congruent, but selecting
state equal to input produces noncongruent outputs. `trace_congruent` exposes
selected-output congruence as the sufficient condition it actually needs.
`outputCongruent_of_unique` supplies it from uniqueness modulo output relation
across related inputs; it does not require state uniqueness. The constant
selection checks that the corrected condition is satisfiable.

The guarded-stream bridge applies to a parameterized body with a guarded state
component. `guardedWitness` constructs its state using `solve_fixed`.
`guarded_trace_unique` uses `unique` to compare every admitted witness, not just
two seeds of the construction. The initialized delay example recovers its
constant stream and reads coordinate three through this bridge. No theorem
asserts that initialized delay solves every unguarded pointwise equation.

These checks review the choice quantifiers, witness retention, comparison
direction, equality assumptions and nonvacuity. There is no active upstream
traced-law record to recover. Naturality, sliding, vanishing and yanking would
require additional admissibility and selection contracts. Computational equality
witnesses remain the separate #453 task.

## Validation

Focused checks cover both library modules and the retained consumers. Integrated
build, exhaustive proof audit and independent Standards/Spec review are pending.
This package alone does not complete #8.
