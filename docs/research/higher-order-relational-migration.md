# Higher-order interval migration (#21)

The existing interval compiler uses full-source naturality through
`STLCRelations.compile_spec`. This is the path used by
`IntervalAnalysis.HigherOrder.compile_contains` and its captured lambda and
case theorems. The runtime operations and public enclosure statements remain
unchanged.

## Caller-work ledger

| Declaration | Before | After and remaining obligations |
|---|---|---|
| `STLCRelations.target` | Local product projection, pairing, currying and application relation proofs | `RelationalCategory.products.fst`, `.snd`, `.pair`, `RelationalCategory.closed.curry`, `.evaluation`; these five repeated relation proofs are removed, with no new proofs replacing them. |
| `STLCRelations.target` identity/composition | Relational identity and composition | Unchanged. |
| `STLCRelations.target` terminal/sums/distribution | Local Unit relation and matching-tag proofs | Retained; terminal uses the existing Unit carrier and distribution retains the entire captured environment. |
| `STLCRelations.target` primitives | `Primitives.correct` | Retained; the implementation and semantic horizontal map are both present. |
| `STLCRelations.inclusion` (new) | No typed-category adapter | Maps a source type to `object base`; retains the entire `RelSquare`. |
| `STLCRelations.inclusion_laws` (new) | No adapter laws | Equality congruence, identity and composition reduce to the same arrows. These are new boundary obligations, not removed work. |
| `STLCRelations.interpretation` (new) | Direct `.spec` projection in Sound | `inclusion` composed with `RelationalCategory.semantics` using `RawMap.comp`. |
| `STLCRelations.interpretation_laws` (new) | Local Sound identity/composition equations | `RawMap.comp_laws` applied to `inclusion_laws` and `RelationalCategory.semantics_laws`. |
| `STLCRelations.interpretation_preserves` (new) | Pointwise operation equations in Sound | The shared `STLCNaturality.Preserves` package. Operation equations move here; they are not claimed as deleted proofs. Distribution still checks both sum tags. |
| `STLCRelations.sound` | Locally constructed semantic correctness record | Compatibility adapter from the composed map laws and full-source preservation package. Its public type and denotation remain the same. |
| `STLCRelations.compile_spec` | Original `CategoricalCompiler.compile_sound` | `STLCNaturality.naturality`, then `compile_ofTarget` and `semantics_compile`. Equality congruence for semantic pairing, copairing and currying is supplied locally. No syntax induction is added. |
| `STLCRelations.compile_preserves`, `compile_apply_preserves`, `compileRelation`, `compileWitnessSquare` | Relation preservation plus semantic recovery | Same statements and bodies; semantic recovery now follows the shared theorem. The witness carrier still retains represented and semantic values. |
| `IntervalAnalysis.HigherOrder.primitives` | Literal/add/multiply/negate enclosure proofs | Unchanged: `singleton_contains`, `add_contains`, `mul_contains`, `neg_contains`. |
| `IntervalAnalysis.HigherOrder.compile_contains`, `capturedLambda_contains`, `capturedCase_left_contains`, `capturedCase_right_contains` | Logical-relation specialization | Same statements and bodies, now consuming the migrated `compile_spec` through `compile_preserves`. |

The code increase is adapter work. The removed repetition is specifically the
five relation-preservation proofs in `target`, not every obligation in Sound.

## Checked cases and statement review

The existing cases supplied the expected mathematics before this migration:
`capturedLambda_contains` encloses `x*x+c` with separate assumptions for the
captured scalar and argument. `capturedCase_left_contains` encloses `f x+c`;
`capturedCase_right_contains` encloses `f c + -x`. Each branch retains the
captured function and scalar. `RepresentsFunction` quantifies over every related
interval/point input. The branch hypotheses use the same runtime and semantic
sum tag; opposite tags remain unrelated.

These universal cases are the retained checked specializations. The existing
concrete executions distinguish branches: with increment, payload `[-1,2]`
and captured `[10,11]`, the left result is `[10,14]` and the right result is
`[9,13]`. `fourthPower_contains` also retains source-level higher-order
application, and its execution gives `[-8,16]` on `[-1,2]`. There was a missing
connection to shared preservation, not a missing proof of these propositions.

`inclusion_laws` asserts equality of complete relational arrows;
`interpretation_laws` asserts equality only of their semantic projections.
`interpretation_preserves` quantifies over all relevant types and arbitrary
arrows, with primitive compatibility obtained from the existing semantic field.
Primitive relation preservation is separately required by `Primitives.correct`.
Neither package assumes the final all-term theorem. `compile_spec` retains all
terms, contexts, bases, primitive implementations and semantic environments.
`compile_preserves` then uses the compiled arrow's relation proof for every
related pair of environments. None of these statements equates two interval
computations based on equality of point functions.

The `sound` compatibility adapter and the five operation replacements preserve
the old types and reduce to the old runtime/semantic functions. Existing clients
compile without statement changes. The retained interval cancellation theorem
continues to distinguish enclosure computations from point semantics.

## Architectural scope

The correspondence is to Felix's separate raw operations, maps and local
operation-preservation obligations at revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, especially
`Homomorphism.agda`'s `CartesianH` and `CocartesianH`. Its
`CartesianClosedH` TODO is not treated as a completed transport theorem.
This migration consumes the local full-source preservation theorem from #19
and relation adapter from #12. It adds no universal closed-law transport,
arbitrary interval decoder, unknown-tag join analysis, or witness erasure.
