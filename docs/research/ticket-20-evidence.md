# Arithmetic pipeline migration (#20)

Review base: `96fe25784c6664880d1dc2b9c6b9814a1712fb12`.
The unrelated `a6cd22b` changes remain in the branch and outside this diff.

The intended claim is unchanged: every arithmetic source program, environment,
finite change and stack tail admits exact recomputation/update agreement, and
an interval input related to the updated environment encloses that output.
Finite changes retain their quadratic cross term; enclosure remains `Contains`.

## Declaration ledger

| Declaration | Before | After and accounting |
|---|---|---|
| `RelationalCategory.semanticsProducts` | Absent | New strict product comparison for semantic projection, at arbitrary relational objects. Comparison arrows are identity functions. |
| `RelationalCategory.semanticsProducts_laws` | Absent | One shared proof of projection/pair preservation, independent of the chosen relations. |
| `FirstOrderRelations.interpretation`, `interpretation_laws` | Absent | New boundary adapter selects the existing relational objects and leaves arrows unchanged. Congruence, identity and composition each require a local definitional check. Count these as new adapter obligations, not removed work. |
| `Incremental.Compiler.interpretation`, `interpretation_laws` | Absent | New boundary adapter sends finite-update maps to graph relations of their exact update squares. Keeps old outputs and changes. Congruence, identity and composition each require a local definitional check. Count these as new adapter obligations. |
| `FirstOrderRelations.sound.ident`, `.comp`; `Incremental.Compiler.sound.ident`, `.comp` | Each proved semantic preservation directly | Inherited from composition of the boundary map and `RelationalCategory.semantics` via `RawMap.comp_laws`. The boundary identity/composition obligations above remain; this row alone is not a reduction in obligations. |
| Both `sound.fst`, `.snd`, `.pair` families | Six independent definitional proofs | Six applications of the same three `semanticsProducts_laws` fields. No new per-target product law is proved. This removes the repeated product-soundness proof family. |
| Both `sound.terminal`, `.primitive` | Local definitional proofs | Retained. The terminal object uses `Unit`, and primitive semantics are still a local requirement. |
| `FirstOrderRelations.compile_spec` | Original function-specific compiler theorem | Shared `FirstOrderNaturality.compile_sound`, whose preservation path uses the shared map/model naturality theorem also consumed by MatrixCompiler and StackMachine. |
| `Incremental.Compiler.compile_update` | Update certificate plus original compiler soundness | Same update certificate, with run/evaluation agreement supplied by `FirstOrderNaturality.compile_sound`. |
| `ArithmeticPipeline.stack_after_update` | Rewrites two stack correctness results and the incremental update theorem | `Comma.Exact.agree` synchronizes the update square and the actual bytecode square. Its agreement subtype supplies output equality, as in MatrixStack. A local exact-square adapter changes the incremental semantic arrow to source evaluation using `compile_update`; count this certificate as retained work. Tail equality remains an application of bytecode correctness. |
| `ArithmeticPipeline.stack_enclosed`, `incremental_output_enclosed` | Interval preservation transported along stack equality and finite-update agreement | Public statements and proof composition retained; their interval compiler now follows the migrated relational interpretation and shared naturality. |
| `Incremental.ident`, `comp`, `pair`, update operations, cache operations; both compiler `target` definitions | Concrete operations with local certificates | Unchanged. No execution machinery is moved to a second target. |
| `arithmeticPrimitives.correct`, interval primitive enclosure lemmas and `primitives.correct` | Ring update laws and interval inequalities | Unchanged local obligations, including multiplication's cross term and four-corner interval multiplication. |

## Checked cases and statement review

This is a proof refactoring, so the existing public cases are retained rather
than adding duplicate arithmetic calculations. The missing connection was to
the shared interpretation/composition APIs; the old statements were already
provable. `shared_updated_enclosed` consumes `incremental_output_enclosed` for
the nonlinear let-shared program. `shared_stack_example` still computes 39.
`shared_update` exercises exact finite changes through `compile_update`, and
`cachedSquareExample_correct` retains two cache advances ending at input 6 and
output 36. `tangent_is_not_a_finite_change` still rejects omission of finite
quadratic effects. `interval_cancellation_is_wider` retains the dependency-loss
counterexample independently of the semantic projection.

The two new interpretation maps quantify over arbitrary primitive signatures,
base objects and primitive certificates. Their equality relation compares
whole relational arrows, including both implementations and specifications;
it does not identify interval computations by their point semantics.
`semanticsProducts_laws` quantifies over arbitrary relations and arrows. Its
comparison is the identity because semantic product carriers are actual pairs.
The two product-soundness consumers instantiate it at different relations:
ordinary interval relations and graph relations of finite updates.

The changed pipeline proof still quantifies over every context, result type,
term, input, change, list of tail types and value of that tail. Its agreement
input is inhabited by the old-input/change pair and the separately updated
stack input. The witness is definitional equality of their observations; no
output agreement is assumed. The retained interval hypothesis is containment
of that updated input, not containment of the old input. Cache invariants and
primitive update laws are untouched. No semantic data erasure is claimed.

## Reference and limits

The construction follows the projection homomorphisms in pinned Felix
`6f36d28097db7ea5f5df3263db3e8be08f74e490`,
`src/Felix/Construct/Comma/Homomorphism.agda`: composition of interpretations
reuses category preservation. This migration also proves semantic product
preservation for relational arrows. It does not assert exact decoding of an
interval or generic closure of comma categories. Full-source migration and
remaining capability gaps belong to the other #15 tickets.

## Validation

Commands run from this worktree through the checked-in Nix/direnv shell:

- `direnv exec . lake build Examples.ArithmeticPipeline`: passed.
- `direnv exec . ./check-foundation.sh`: passed (exit 0).
- `direnv exec . ./check.sh`: passed, all 86 modules rechecked from source;
  exhaustive audit union `[propext, Classical.choice, Quot.sound]`.

Local log paths are `/tmp/conaled-spec15/20-build.log`, `20-foundation.log`, and
`20-fresh.log`. Project build output is worktree-local; only pinned dependency
packages are shared. No proof-audit implementation or runtime operation changed,
so no new runtime harness or proof-audit regression fixture was introduced.
