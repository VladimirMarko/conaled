# Client interfaces after issue #24

Baseline: `47b556e83229ce11b27b5b7b4444c089a1e96ac3`.
The task is the bounded interface follow-up in GitHub issue #24. Existing
public theorem statements and executable operations are retained.

## Structural soundness

`MatrixCompiler.sound` previously extracted three product laws with repeated
unfolding lists. Each list named `matrixValueProducts`, `ProductMap.comp`,
`Comparison.comp`, `evaluateProducts`, `valueProducts`, `Comparison.id`,
`values`, `FunctionCategory.ops`, `FunctionCategory.products`,
`Comparison.map`, `coordinates`, `evaluate`, `matrixProducts`,
`FirstOrderCategory.products`, `coordinateProducts`, and `decode_encode`.
It also converted identity and composition equations to pointwise equations.

It now calls `FirstOrderNaturality.soundOfProducts` with the existing composed
map and preservation packages, two value-comparison equations, and the existing
primitive meaning proof. No product implementation is unfolded in the client.
`Maps.matrixValueProducts_hom` and `matrixValueProducts_inv` discharge the two
comparison equations using `decode_encode` at the product type. They apply to
all nested values, over any commutative semiring. Matrix action, finite sums,
coordinate splitting, and encode/decode inverses remain in Operations and Maps;
the adapter proves no matrix algebra.

`FirstOrderRelations.sound` uses the same adapter. Its new `semanticProducts`
and `semanticProducts_laws` restrict the existing relational semantic product
package to the frontend's selected objects. Previously this client projected
identity, composition, projection, and pairing proofs separately. It now
supplies the composed map laws, the restricted product package, identity
comparison equations, and primitive compatibility. The interpretation retains
both an implementation and a semantic function, unlike the raw matrix target.

The adapter's cost is one definition with map laws, a product comparison and
its laws, two pointwise comparison equations, and primitive compatibility as
inputs. It centrally derives every `Sound` field. Its terminal field uses
uniqueness of `Unit`: any interpreted terminal arrow has this value. This
explicit value-level terminal fact needs no coordinate or terminal-map
unfolding. The two matrix comparison lemmas and the relational restriction
package are the entire additional representation-specific cost. The adapter
requires identity action only at the final nested-value interface; it does not
require intermediate coordinate comparisons to be strict. The existing
`MatrixCompilerPreservation.compile_doubled` and `compiled_square` continue to
check the non-strict matrix image interface separately.

## Exact output agreement

`ArithmeticPipeline.stack_after_update` previously built an incremental square,
converted both squares with `Comma.Exact.ofSquare`, called `agree`, converted
back with `toSquare`, constructed a synchronized subtype input, and projected
the output subtype's property. It now passes the two compiler squares, equality
of their semantic maps, and equality of their input observations to
`Comma.Exact.outputs_agree`. The inputs remain the old value/change pair and
the updated value with its arbitrary stack tail.

`Incremental.Compiler.compileSquare` is the one new compiler adapter. Its
implementation returns the source evaluator's old output and the compiled
finite change; its semantic map is the source evaluator. `compile_update`
discharges its square law once for every change object, primitive package,
source term, old input, and change. It assumes no additive or invertible change
structure. Existing arithmetic finite-change rules remain unchanged.

`MatrixStack.agree_preserving_tail` uses the same `outputs_agree` interface on
arbitrary coordinate vectors and stacks. It no longer constructs a synchronized
input or extracts its proof. `jointSquare` and `joint_outputs_agree` remain
available for callers that actually need the joint implementation.

The cost of `outputs_agree` is one theorem. Internally it performs the comma
conversion, calls the existing `agree`, and eliminates the output subtype.
Its only compatibility obligations are equality of the two semantic maps and
equality of the input observations. It neither assumes nor derives injectivity
or surjectivity of an observation. Output representations may be redundant.
Both application proofs still obtain preservation of the tail from the
bytecode certificate separately; equality of first observations alone would
not establish that fact.

## Relation preservation

`Digital.compose.correct` previously invoked `witnessMap.map`, projected its
horizontal `left` arrow, constructed a total witness-space pair containing a
proof, and extracted the output subtype property. It now invokes
`RelationalCategory.compose_preserves` on the two relational arrows and the
ordinary stability hypothesis. The signal and the timing/value observation
are its semantic inputs; no total witness representation reaches the client.

The cost is one theorem eliminating `ops.comp`'s preservation certificate at
ordinary related inputs. It is valid for any three relations and any two
composable relation-preserving arrows. `Digital.relation_compose`,
`Digital.square_compose`, `witnessMap`, and `witnessMap_laws` keep the connection
to shared category composition and exact witness semantics checked.

`IntervalAnalysis.neg_add_contains` is a second consumer of this theorem,
composing existing addition and negation squares on arbitrary enclosing
intervals and rational points. Its conclusion is enclosure of `-(x + y)` by
`neg (add I J)`, not exact decoding or equality of interval sets. Its cost is
one universal application theorem and no new implementation. Inverted intervals
remain permitted; a related point supplies the needed nonempty instance.
`interval_cancellation_is_wider` retains the explicit loss-of-dependency case.

## Statement review and checked uses

The initial gap was a missing public connection, not an unprovable application
claim: the baseline already proved all three target clients through internal
representations. The retained universal clients serve as the first cases.

- `soundOfProducts` quantifies over every frontend target, base value type,
  arrow, and input. Product comparison identity is an explicit hypothesis,
  established by matrix encode/decode and by relational semantic projection.
  Its primitive premise is local, not compiler correctness assumed wholesale.
  The matrix and relational `sound` statements retain their original meanings.
- The two matrix comparison lemmas cover arbitrary product types and values.
  The relational product restriction covers arbitrary base relations and
  primitive packages; it does not require a decoder for the relation.
- `compileSquare` preserves the update observation, including input-dependent
  changes. `outputs_agree` quantifies over two independent representation
  carriers with common semantic input/output types. Its conclusion compares
  decoded outputs, not representations themselves. The two all-program
  clients retain arbitrary inputs and arbitrary tails. Existing
  `incremental_output_enclosed` still transfers the exact result into enclosure.
- `compose_preserves` runs the first arrow before the second and concludes the
  target relation. Digital stability and interval enclosure exercise different
  relations. `neg_add_contains` has satisfiable premises (singleton intervals
  suffice), and its arbitrary-point statement also covers wider intervals.
  Existing timing stability and hazard results retain their original claims.

No source language, higher-order relation, foundation file, or audit machinery
is changed. No runtime operation is changed; runtime tests and audit regression
fixtures are therefore not added for this task. The required foundation and
fresh source/audit runs are recorded with the review candidate outside the diff.

## Felix comparison

The reference inspected is Felix commit
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, as pinned in `docs/SOURCES.md`.
`src/Felix/Homomorphism.agda` separates `ProductsH` comparison data,
`StrongProductsH` inverse laws, and `CartesianH` preservation, and derives
alternate projection/pairing equations from those laws. The new soundness
adapter follows that separation at the existing Lean frontend boundary;
comparison normalization is a representation fact, not a new category axiom.

`src/Felix/Construct/Comma/Type.agda` packages two arrows with a commuting
condition. Its domain and codomain projections and the category homomorphisms
in `Construct/Comma/Homomorphism.agda` are the corresponding shared capability
behind the exact and witness interfaces. The new eliminators keep that
construction central while returning the equality or relation a caller needs.
The latter upstream file still marks Cartesian/closed/logic homomorphisms as
work to do. This change claims no completion of those upstream tasks or the
broader Felix port in #8; those remain separately tracked work. It closes the
three caller-interface gaps identified in #24 using the constructions from #15.
