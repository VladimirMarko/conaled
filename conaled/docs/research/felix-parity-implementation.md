# Architectural parity implementation evidence (#15, #23)

Implementation coverage is assembled below. This document supplies evidence
for the required independent full-spec integration review; its disposition and
milestone completion are recorded on #15 by the workflow. Ticket reviews are
separate from that final review. The historical [source inventory](felix-parity.md) remains a record of
what was missing at the inspected baseline.

## Revisions and evidence boundary

- Felix reference: `6f36d28097db7ea5f5df3263db3e8be08f74e490`.
- Inspected local foundation: `c17daf5a66b9812fdbc0cb37cd4e9c49b1949ce8`.
- Implementation start and full-spec review base:
  `b57f9f383a527bcd40bd201cd8354e1f8315185c`. Intervening baseline changes
  were planning/tracker documentation; the Lean baseline was unchanged.
- Combined implementation and #23 incorporated review base:
  `bdef52594f560611dbb42ff66136806936c7164d` on `integration/spec-15`.
  This includes all thirteen implementation tickets preceding #23.
- Lean: 4.35.0; Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
  `lean-toolchain`, `lake-manifest.json`, `flake.nix`, and `flake.lock` retain
  the checked-in versions.
- User commit `a6cd22b` is preserved. Its changes to `docs/extensions.md` and
  `docs/history/README.md` are outside #15's implementation and review scope.

The tables use ticket acceptance criteria in their published order. Names
under `SquareKit` omit that prefix unless another namespace is explicit.
Each numbered row covers the corresponding criterion, including its negative
constraints. The original P1–P6 requirements are mapped separately so that
splitting the work into tickets does not lose a requirement.

## P1–P6 coverage

| Original requirement | Implemented declarations and checked consumers | Tickets |
|---|---|---|
| P1: arbitrary objects, independent universes, raw operations/equivalence/congruence/laws | `CategoryOps`, `HomEquiv`, `CategoryCongr`, `CategoryLaws`, `TerminalOps`, `ProductOps`; `CodeCategory`, `MatrixCategory`, `FirstOrderCategory` | #9 |
| P1: lawful quotient with exactly the declared relation and all supported descents | `HomQuotient.mk_eq_iff`, `category`, `mk_comp`, `mk_pair`; optional `mk_copair`, `mk_distribute`, `mk_curry`; `LawfulQuotient.comparison` | #9, #18 |
| P1: optional sums, distribution and closure, independently selected | `CoproductOps`, `DistributionOps`, `ClosedOps` and their separate laws; `Examples.OptionalSquares`, `STLCExact.model`; `FirstOrderCompiler.no_exponential` retained | #18, #19 |
| P2: composable maps and Mathlib interoperability | `RawMap.comp_laws`, `toFunctor`, `ofFunctor`, `quotientFunctor`; `Comparison.toIso`, `HomQuotient.preservesBinaryProduct`, `preservesTerminal` | #10 |
| P2: induced/reflected category/cartesian laws, strict and non-strict comparison | `RawMap.induced`, `transportLaws`, `TerminalMap.transportLaws`, `ProductMap.transportLaws`; `CodeCategory.laws`, `MatrixCompiler.Maps.matrixValueProducts_laws` | #10 |
| P3: raw comma operations, projections, lawful connection, products with explicit hypotheses | `Comma.ops`, `fst_laws`, `snd_laws`, `quotientMap_eq_iff`, `productOps`, `productLaws`, `rawBinaryFanIsLimit`, `lawfulLimitIsLimit` | #11, #16 |
| P3: exact round trips and all existing exact operations | `Comma.Exact.ofRep`, `toRep`, `ofSquare`, `toSquare`; product/optional comparison lemmas; `Comma.vertical`; `Comma.Exact.agree`; `Squares.synchronize_as_agree` | #11, #16, #17, #18 |
| P3: non-function identity/doubling matrix semantics and nonidentity comparison | `MatrixDoubling.doublingMap_laws`, `doublingProducts_inverse`, `comparison_nonidentity`, `triple_commutes`, `matrix_product_commutes` | #16 |
| P4: graph/witness maps, product/composition/function compatibility and distinct contracts | `RelationalCategory.graphMap`, `witnessMap`, `graphWitness_laws`, `witnessProducts_laws`, `witness_evaluation`, `witness_curry`; `Examples.RelationalBridge.interval_multiplication`, `timing_composition` | #12 |
| P5: both arbitrary-object compilers, non-strict coherence, explicit primitives | `FirstOrderNaturality.cartesian_naturality`, `STLCNaturality.structured_naturality`; `Examples.FullSourceNaturality.Lift.naturality` | #13, #19 |
| P5: old interfaces and composed preservation without another syntax induction | Both namespaces' `ofTarget`, `compile_ofTarget`, `compile_sound`, `preserves_comp`; `STLCNaturality.naturality_comp`; `STLCExact.compile_comparison` | #13, #19 |
| P6: actual migrated clients, quantified inputs and stack tails | `Examples.MatrixStack.jointSquare`, `agree_preserving_tail`; `Examples.ArithmeticPipeline.stack_after_update`, `incremental_output_enclosed`; `IntervalAnalysis.HigherOrder.capturedLambda_contains`, both `capturedCase_*_contains`; `Applications.Timing.Digital.compose` | #14, #20, #21, #22 |
| P6: compiler preservation between non-function matrix interpretations | `Examples.MatrixCompilerPreservation.compile_interpretations`, `compiled_square`, `triple_entries` | #14 |
| P6: caller accounting, final inventory, validation and independent review | Combined ledger below and linked per-client ledgers; validation below. Final independent integration review is recorded on #15. | #23 |

## Ticket acceptance trace

### #9: raw operations and lawful adaptation

1. `CategoryOps` and the separate optional interfaces quantify over object/hom
   universes without `Ty` or primitives. The original root foundation is unchanged.
2. `HomQuotient.category` requires congruence and laws; `mk_eq_iff` identifies
   exactly the setoid. `mk_ident`, `mk_comp`, `mk_terminal`, `mk_fst`, `mk_snd`,
   `mk_pair` prove descent, retaining raw representatives.
3. `ofCategory`, `ofCategoryLaws`, `LawfulQuotient.homEquiv` and `comparison`
   reuse lawful Mathlib categories/quotients under their actual hypotheses.
4. `CodeCategory.association_not_equal`, `association_classes`,
   `product_classes`; `MatrixCategory.association`, `pair_recover` distinguish
   semantic syntax equivalence from equality of actual matrix entries.
5. `Examples.CategoryInstances.matrix_add_after_pair` checks arbitrary inputs;
   `FirstOrderCategory` requires no closure. [Foundation correspondence](category-foundation.md)
   records Felix Raw/Equiv/Laws and the optional structure delivered by #18.

### #10: maps and law transport

1. `RawMap`, `MapLaws`, `RawMap.comp_laws`, `toFunctor`, `ofFunctor`,
   `quotientFunctor` supply maps and composition, including congruence.
2. `ComparisonLaws`, `TerminalMapLaws`, `ProductMapLaws`, `Comparison.toIso`,
   `HomQuotient.comparisonIso` supply non-strict inverse/comparison equations.
3. `RawMap.induced`, `induced_reflects`, `transportLaws`,
   `TerminalMap.transportLaws`, `ProductMap.transportLaws` require induced
   equivalence or reflection. None infers raw equality from preservation alone.
4. `CodeCategory.laws`, `terminalLaws`, `productLaws` derive associativity,
   uniqueness and beta/eta from evaluation. `Examples.CategoryMaps` checks
   composed evaluation through Mathlib Type arrows.
5. `CodeCategory.evaluationProducts` is strict; `MatrixCompiler.Maps`
   composes coordinate and nested-value interpretations with encode/decode.
   [Map transport evidence](category-map-transport.md) states the pinned
   `LawfulCategoryᶠ` and `LawfulCartesianᶠ` hypotheses.
6. That document lists all five replaced Code declarations and all new
   evaluation/comparison adapters. Generic closed-law transport is not asserted.

### #11: general comma and exact category recovery

1. `Comma.Obj`, `Hom`, `ident`, `comp`, `ops` require common-target laws and
   interpretation preservation, without source category laws for construction.
2. `Comma.toMathlib`, `fromMathlib`, `homToMathlib`, `homFromMathlib`,
   `quotientMap`, `quotientMap_eq_iff` provide lawful connections and preserve
   both raw sides before quotienting.
3. `Comma.equiv`, `congr`, `laws`, `fst_laws`, `snd_laws` separate component
   laws from operations. `Examples.CommaSquares.semantic_projection_laws`
   uses `RawMap.comp_laws`.
4. `Comma.Exact` round trips and identity/composition comparison lemmas
   recover both objects and both horizontal maps, with arbitrary decoders.
5. `Examples.CommaSquares.ordered_composition`, `semantic_composition`,
   `increment_nonidentity`, `code_composition`, `code_quotient_association`
   check order and arbitrary composition. Products/pasting/optional scope is
   discharged by #16–#18 below.

### #16: comma products and actual matrices

1. `Comma.terminalOps`, `productOps`, `first`, `second`, `fork` construct
   raw arrows with target cartesian laws and strong comparisons. Source laws
   enter `terminalLaws`/`productLaws` separately.
2. `Comma.lawfulLimitIsLimit` needs preservation by the right functor for
   that diagram; `rawBinaryFanIsLimit` connects converted raw projections.
   This lawful limit result does not impose both raw strong-map hypotheses.
3. `Comma.Exact.ofRep_product`, `ofSquare_pair`, `ofSquare_terminate`,
   `first_pair`, `second_pair`, `pair_eta`, `terminal_unique` recover the
   original exact operations and laws.
4. `MatrixDoubling.Source`, `identityMap`, `doublingMap`, `duplicate_id`,
   `duplicate_comp` use distinct tagged finite objects and natural matrices.
5. `doublingProducts_inverse`, `doublingProducts_laws`,
   `comparison_middle_entry`, `comparison_nonidentity`, `triple_nonidentity`,
   `triple_commutes` check the shuffle and a square with matrix connectors.
6. `matrix_identity_commutes`, `matrix_comp_commutes`,
   `matrix_product_commutes`, `first_fork`, `second_fork`, `fork_eta`
   cover arbitrary compatible matrices; no exponentials are required.

### #17: vertical pasting and synchronization

1. `Comma.vertical` assumes equivalence of interpreted middle arrows and
   target congruence/associativity. No extra interchange/coherence theorem is
   claimed without a proof.
2. `Comma.Exact.ofRep_after`, `ofSquare_vertical` recover arbitrary exact pasting.
3. `Comma.Exact.agreement`, `agree`, `agree_first`, `agree_second`,
   `agree_comp` retain both implementations. `Squares.synchronized` and
   `synchronize` delegate to this construction.
4. `Squares.synchronize_agrees`, `synchronize_as_agree` and
   `Examples.CommaAgreement.independent_composition`, `synchronized_execution`,
   `vertical_output` retain and exercise the public contracts.
5. `CommaVertical.lean` records the pinned Felix vertical construction:
   compatibility is target equivalence; the Type recovery uses pointwise
   equality. No decoder injectivity is required.

### #18: optional exact structure

1. `CoproductOps`, `CoproductCongr`, `CoproductLaws`, `DistributionOps`,
   `DistributionLaws`, `ClosedOps`, `ClosedCongr`, `ClosedLaws` are separate.
   Distribution has no arrow argument requiring another congruence field.
2. `Comma.Exact` sum/exponential object and arrow comparisons recover
   `FunctionRep`, evaluation, curry and uncurry. `copair_left`, `copair_right`,
   `copair_eta`, `uncurry_curry`, `curry_uncurry` recover beta/eta.
3. `HomQuotient.coproducts`, `distribution`, `closed` and their laws/`mk_*`
   lemmas prove descent. `OptionalMathlib` uses chosen coproducts,
   `CartesianMonoidalCategory`, `MonoidalClosed`, and `IsIso` for distribution.
4. `Comma.Exact.exponential_carrier` retains specification functions as data;
   no general comma closure or erasure theorem is claimed.
5. [Optional capability table](optional-exact-structure.md) distinguishes
   general, lawful and Type-specific hypotheses. `Examples.OptionalSquares`
   checks both sum tags, distribution, curry/evaluation and beta/eta.
6. Root foundation files remain dependency-free; #19 supplies scoped
   non-strict preservation rather than adding assumptions to first-order clients.

### #12: relational bridges

1. `RelationalCategory.graphMap`, `witnessMap`, their `*_laws`,
   `graphProducts`, `witnessProducts` connect graphs and total witnesses to
   general squares. `witness_evaluation`/`witness_curry` handle function relations.
2. `graph_roundtrip`, `exact_roundtrip`, `ofSquare_toSquare`, `witness_compose`,
   the three `recover_*` product lemmas and two curry recovery lemmas reuse
   map/product/closed packages. `closedLaws` retains local relational closed proofs.
3. `Examples.RelationalBridge.successor_graph`, `interval_multiplication`,
   `timing_composition`, `timing_witness_composition` check both maps and the
   actual `Contains`/`Stable` contracts.
4. `interval_cancellation_is_wider` remains checked, as do
   timing stability results. Whole-arrow equality never identifies interval
   computations merely because their point meanings agree.
5. Witness carriers store represented and semantic values. `witnessFunction`
   is only a forward map, not a false exponential isomorphism. Local enclosure,
   function-relation, and signal proofs remain required in the migrations below.

### #13: first-order preservation

1. `FirstOrderNaturality.Model`, `cartesian`, `compile` interpret the frontend
   using category/terminal/products and primitives; shared operations contain no `Ty`.
2. `naturality`, `cartesian_naturality`, `image` state comparison-aware
   coherence and explicit primitive compatibility for arbitrary terms.
3. `ofTarget`, `compile_ofTarget`, `soundMap_laws`, `sound_preserves`,
   `compile_sound` recover legacy interfaces; `FirstOrderCompiler.no_exponential`
   and all root declarations retain their statements.
4. `MatrixCompiler.Naturality.compile_coordinates`, `coordinate_linearCombination`,
   `finiteModel` check finite matrices/evaluation. `preserves_comp` reuses
   map composition without another syntax induction.
5. [First-order obligation table](first-order-naturality.md) separates shared
   congruence/coherence/induction from coordinate comparisons and primitives.
6. #14 below instantiates identity/doubling preservation; #19 supplies full STLC.

### #19: full-source preservation

1. `CoproductMapLaws`, `DistributionMapLaws`, `ClosedMapLaws`,
   `imageDistribution` and `STLCNaturality.image` give optional, non-strict
   comparison/coherence without imposing them on cartesian clients.
2. `STLCNaturality.naturality`, `structured_naturality`, `preserves_comp`,
   `naturality_comp` cover every constructor, explicit primitives and composition.
3. `ofTarget`, `compile_ofTarget`, `sound_preserves`, `compile_sound` recover
   `CategoricalCompiler` interfaces. `STLCExact.compile_comparison`,
   `compile_commutes`, `compile_apply_commutes` recover exact interpretation.
4. `Examples.FullSourceNaturality.Exact.captured_lambda`, `left_branch`,
   `right_branch` check independent captured inputs and both tags. `Lift.naturality`
   and `Lift.composed_naturality` exercise non-strict optional comparisons.
5. Existing local beta/eta laws remain; no universal closed-law transport or
   completion of Felix's `CartesianClosedH` TODO is inferred.
6. [Full-source evidence](full-source-naturality.md) inventories comparison,
   primitive and structural obligations. Preservation uses explicit local
   coherence; comparison invertibility is separately proved where claimed.

### #14, #20, #21 and #22: migrated clients

| Ticket / criterion | Declaration-level evidence and obligation accounting |
|---|---|
| #14.1 | `Examples.MatrixStack.jointSquare` uses `Comma.Exact.agree`; `agree_preserving_tail` projects agreement and the bytecode tail certificate for every term and tail. |
| #14.2 | `Examples.MatrixCompilerPreservation.primitive_preserved`, `compile_identity`, `compile_doubled`, `compile_interpretations`, `compiled_square` use actual matrix interpretations and the shuffle comparisons. |
| #14.3 | `jointSquare` consumes shared agreement in the existing client, preserving matrix and bytecode implementations. |
| #14.4–6 | [Matrix ledger](ticket-14-evidence.md) names moved operations, retained primitives, new model/retag adapters and five replaced denotation proofs. Combined accounting follows below. |
| #20.1 | `ArithmeticPipeline.stack_after_update` uses shared agreement; `incremental_output_enclosed` reaches shared first-order naturality through the interval compiler. All programs/inputs/changes/tails remain quantified. |
| #20.2 | `Incremental.Compiler.compile_update` retains the finite-change certificate. `cachedSquareExample_correct`, `tangent_is_not_a_finite_change`, and interval `Contains` remain distinct checked obligations. |
| #20.3 | `FirstOrderRelations` and `Incremental.Compiler` use `RawMap.comp_laws`, `RelationalCategory.semanticsProducts_laws`, and `FirstOrderNaturality.compile_sound`; MatrixCompiler uses the same map/compiler machinery. |
| #20.4–5 | [Arithmetic ledger](ticket-20-evidence.md) charges both new boundary adapters, removes repeated product-soundness proofs, retains primitives/tails and `interval_cancellation_is_wider`. |
| #21.1 | `STLCRelations.compile_spec` uses `STLCNaturality.naturality`; `compile_preserves` and `HigherOrder.compile_contains` feed the existing three captured lambda/case theorems. |
| #21.2 | `RepresentsFunction`, matching sum tags, independent captured scalar/function and enclosure hypotheses retain their original meanings and statements. |
| #21.3 | `STLCRelations.target` consumes `RelationalCategory.products` and `closed`; `interpretation_laws` uses `RawMap.comp_laws`. No new syntax induction; `primitives.correct` stays local. |
| #21.4 | [Higher-order ledger](higher-order-relational-migration.md) accounts for inclusion/map/preservation adapters, moved Sound equations and five deleted relation proofs; no point-function quotient or witness erasure. |
| #22.1 | `Applications.Timing.Digital.compose.correct` obtains its certificate through `RelationalCategory.ops.comp` and `witnessMap.map`, for arbitrary admissible signals/timings/values. |
| #22.2 | `Digital.matrix_stable`, `Circuit.compile_matrix_stable`, `Adders.fullAdder_stable`, `hazard_at_seven_tenths`, `hazard_before_and_after` retain setup/hold and independent value/timing semantics. No feedback/physical implementation claim. |
| #22.3 | `Digital.square_compose` uses `witnessMap_laws.comp`; unary/binary/constant gate stability proofs remain local. |
| #22.4 | [Timing ledger](ticket-22-evidence.md) records moved adapters and shared facts; `Applications.Timing.Examples.delayed_double_not` and `delayed_double_not_constant` exercise actual composition. |

### #23: consolidated coverage

1. The P1–P6 table and numbered ticket trace cover every published requirement;
   the deferral section assigns broader Felix work to #8.
2. The fresh public-entrypoint check below includes non-function matrices,
   non-strict comparisons, exact/relational bridges, both compilers and clients.
3. The combined ledger below identifies shared maps/compiler/agreement machinery
   and a removed proof family in each required client.
4. The ledger and linked declaration inventories charge new adapters and retain
   primitive/representation obligations; moved work is explicitly excluded.
5. The revision boundary, validation record and limitations update the inventory.
   Milestone status is determined by the independent review workflow on #15.
6. The fresh foundation and complete build/audit results below provide evidence
   for that review while preserving existing public statements.

## Combined caller-work ledger

The comparison baseline is the full-spec starting commit above. Individual
migration ledgers also record their immediate integration bases. Rows below
count proof responsibilities, not lines or declarations moved between files.
All new adapters are charged here or in the explicitly linked detailed ledger.

| Caller work at baseline | MatrixStack path after migration | ArithmeticPipeline path after migration |
|---|---|---|
| Concrete operations | `MatrixCompiler` coordinate operations moved unchanged to `Applications.Linear.Operations`; `StackMachine.Certified` operations unchanged. No reduction credited. | Incremental operations, cache certificates, interval operations and compiler targets unchanged. No reduction credited. |
| Category preservation | `Maps.matrixValues_laws` uses `RawMap.comp_laws`; `sound.ident/comp` inherit it. Old direct `denote_id/denote_comp` algebra replaced by projections. | Both `FirstOrderRelations.interpretation_laws` and `Incremental.Compiler.interpretation_laws` compose with `RelationalCategory.semantics_laws` using `RawMap.comp_laws`. New local boundary identity/composition obligations offset the moved Sound work; no reduction credited to this row. |
| Product preservation | `Maps.matrixValueProducts_laws` uses `ProductMap.comp_laws`; `denote_first/second/pair` now project soundness. Their direct algebra proofs are deleted. | Both Sound records' `fst/snd/pair` fields use the same three `RelationalCategory.semanticsProducts_laws` fields. Six separate definitional proofs become shared applications; no new per-target product proof replaces them. |
| Compiler soundness | `MatrixCompiler.compile_correct`, `StackMachine.compile_correct` use `FirstOrderNaturality.compile_sound`. | `FirstOrderRelations.compile_spec`, `Incremental.Compiler.compile_update` use the same `FirstOrderNaturality.compile_sound`. |
| Independent implementation agreement | `jointSquare` uses `Comma.Exact.agree`; `agree_preserving_tail` projects its result. | `stack_after_update` uses `Comma.Exact.agree` on update and bytecode squares; output equality comes from its agreement carrier. |
| New adapters | Code evaluation/comparisons from #10; `Maps` coordinate/value maps, comparisons, inverse and local preservation proofs; all #14 `sourceObjects`, `sourceModel`, `doubledModel`, `identityModel`, `retag`, `identityInterpretation`, `identity_laws`, `primitive_preserved` obligations are counted. | `RelationalCategory.semanticsProducts` and its shared laws; `FirstOrderRelations.interpretation` and laws; `Incremental.Compiler.interpretation` and laws; local update square's source-evaluation certificate from `compile_update` are counted. |
| Irreducible local obligations | Coordinate finite sums, encode/decode inverses, `denote_primitive`, primitive meaning, terminal representation, bytecode execution and arbitrary-tail certificates. | Finite update/cross-term and cache invariants, arithmetic primitive ring laws, four-corner interval multiplication/other enclosure proofs, terminal/primitive Sound fields and bytecode tails. |
| Syntax induction accounting | Generic preservation plus compatibility inductions are introduced once in #13/#19. Existing dependency-free compiler inductions remain. No removed application induction is claimed. | Same shared theorem; neither migration adds a source induction. |

Thus both clients consume **the same** `RawMap.comp_laws`,
`FirstOrderNaturality.compile_sound`, and `Comma.Exact.agree`. Matrix-specific
product comparisons use the generic `ProductMap.comp_laws`; relational semantic
projection proves product preservation once for arbitrary relations. The concrete
reduction required by #15 is the replaced matrix denotation algebra and the
shared relational product-soundness proof family. Moving coordinate operations,
adding adapters, and retaining primitive/tail proofs do not count as reduction.

The other adapter families are accounted for in [map transport](category-map-transport.md),
[first-order preservation](first-order-naturality.md),
[optional exact structure](optional-exact-structure.md),
[full-source preservation](full-source-naturality.md), and the higher-order/timing
ledgers linked above. Exact and relational bridges retain both horizontal maps;
function witnesses and exact function representations retain semantic data.
These are construction/proof costs, not erased runtime encodings.

### Matrix map adapter inventory

The following declarations in `MatrixCompiler.Maps` account for the new
representation boundary in full. They are not counted as deleted caller work:

- Raw models: `matrices`, `matrixTerminal`, `matrixProducts`, `coordinates`,
  `coordinateTerminal`, `coordinateProducts`.
- Maps and local preservation: `evaluate`, `evaluate_laws`, `coordinateFunctions`,
  `coordinateFunctions_laws`, `values`, `values_laws`.
- Coordinate comparisons: `coordinateFunctionTerminal`,
  `coordinateFunctionProducts`, their `_inverse` and `_laws` proofs;
  `evaluateTerminal`, `evaluateProducts` and their `_laws` proofs.
- Value comparisons: `valueTerminal`, `valueProducts`, their `_inverse` and
  `_laws` proofs, using the existing encode/decode inverse equations.
- Composed packages: `matrixFunctions`, `matrixFunctions_laws`,
  `matrixFunctionProducts`, `matrixFunctionProducts_laws`,
  `matrixFunctionProducts_inverse`, `matrixFunctionTerminal`,
  `matrixFunctionTerminal_laws`, `matrixFunctionTerminal_inverse`,
  `matrixValues`, `matrixValues_laws`, `matrixValueProducts`,
  `matrixValueProducts_laws`, `matrixValueProducts_inverse`.
- Derived laws and compatibility: `coordinateLaws`, `coordinateTerminalLaws`,
  `coordinateProductCongr`, `coordinateProductLaws`, `matrixProductLaws`,
  `matrixTerminalLaws`, `matrixValues_denote`, `interpretation_commutes`,
  `matrix_product_comparison`, `composed_matrix_action`.

Inverse/preservation proofs for concrete comparisons remain local. Composed
packages reuse generic map composition; category/product laws reuse transport.
`Examples.MatrixCompilerPreservation.Prim` supplies arbitrary typed matrices,
and its model/retag/primitive obligations are listed in the #14 ledger.

## Closed law transport (#37)

[Issue #37](https://github.com/VladimirMarko/conaled/issues/37) extends the initial
milestone with [SquareKit/ClosedMap.lean](../../SquareKit/ClosedMap.lean).
The older per-ticket records above describe their delivery scope; their closed
transport exclusions do not describe this extension.

| Capability | Local evidence and hypotheses |
|---|---|
| Currying congruence | `ClosedMap.transportCongr`: map congruence, reflection, target composition/currying congruence and currying preservation. |
| Uncurrying preservation | `ClosedMap.map_uncurry`: category/product/evaluation preservation, target category/product laws and product comparison inverses. No source closed laws or exponential inverse equations are needed for this lemma. |
| Beta, eta and naturality | `ClosedMap.transportLaws`: lawful target category/products/closure, local preservation, both comparison inverses and reflection. `RawMap.induced` and `induced_reflects` supply the source relation without injectivity. |
| Identity and composition | `ClosedMap.id`, `comp`, `id_laws`, `comp_laws`, `id_inverse`, `comp_inverse`; reuse `RawMap.comp_laws`, `ProductMap.comp` and comparison composition. |
| Raw-code consumer | `CodeCategory.closedCongr`, `closedLaws`, `closed_eta` use the existing evaluation map. `closed_eta_not_equal` retains the distinction between raw trees and semantic equivalence. |
| Non-strict and composed uses | `Examples.ClosedTransport.Wrapped.closedLaws` transports through `Box (a × b)` and `Box (a → b)` comparisons. `composedClosedLaws` interprets raw code through ordinary functions into wrapped operations using shared composition and the induced relation. |

The existing `ClosedMapLaws` fields and comparison inverse equations suffice.
`map_uncurry` derives the needed coherence from evaluation and product
preservation. `uncurry_curry` and `curry_uncurry` conjugate the target bijection
by the comparisons. `ClosedLaws.ofBetaEta` derives naturality from those two
laws and category/product laws. The source needs no closed-law premise.
Composition needs no category or closed laws in the intermediate model.
Operations, congruence, equivalence and laws remain separately selectable;
object and hom universes are independent.

The raw-code adapter now supplies closed laws through transport. Its callers
need no structural proofs of beta, eta or naturality and no syntax induction.
Local obligations are `evaluationClosed` (curry and evaluation preservation) and
`closedComparisonLaws`, alongside the existing category/product preservation
and comparison inverses. `CodeCategory.closed_eta` recovers the statement of
`CategoricalCompiler.closed_eta`. The dependency-free proof in `Compiler.lean`
remains for that public foundation's import policy; it is not a dependency of
the transported proof. `FunctionCategory.closedLaws` supplies the ordinary
function model's laws by reduction. Product `hom_ext` and `pair_comp` move from
`CommaProducts` to `CartesianMap`, preserving their names and statements for
both consumers.

The pinned Felix `Homomorphism.agda` supplies exponential comparison arrows
but leaves `CartesianClosedH` unfinished; `MakeLawful.agda` implements category
and Cartesian transport and ends with a closed-transport TODO. The local
construction fills this gap under the stated hypotheses. Mathlib's existing
`MonoidalClosed` laws are already adapted in `OptionalMathlib`; they concern
lawful categories with equality. This transport also supports raw syntax and
chosen hom setoids without quotienting executable representatives.

Statement review checked all new declarations against those hypotheses and
relations. Raw eta was already provable in the foundation; the missing piece
was its derivation through the shared interface. The retained cases connect
beta, eta and environment naturality to `CodeCategory.closedLaws`, check both
inverse equations for genuinely wrapped carriers, and derive source laws after
composing interpretations. `Wrapped.captured_offset` checks the expected
addition result for arbitrary captured and applied values. No claim concerns
arbitrary functors, arbitrary closed comma categories, or dependent Π-types.

## Deferred work and limits

[Issue #8](https://github.com/VladimirMarko/conaled/issues/8) owns the full Felix
port and unfinished constructions. This milestone supplies scoped optional
preservation needed by existing compilers. The #37 extension adds closed-law
transport under explicit preservation and inverse hypotheses. Neither claims
arbitrary comma closedness, initial objects/right distribution beyond
the selected interfaces, traced/feedback constructions, indexed dependent
frontends, generic hardware optimization, or runtime witness erasure. Upstream
TODOs are not treated as proved mathematics. Existing AD, scan/FFT, parsing and
timing applications remain checked but are not claimed as new full-Felix ports.
No production circuit or certified floating-point implementation is asserted.

## Validation and completion gate

The #23 change is documentation only; no new formal statement requires a new
statement review. Per-ticket statement reviews remain in their implementation
records. The combined source is checked through the public `SquareApplications`
import graph, including both non-function matrix models, exact optional recovery,
relational bridges, both generic compilers and every migrated application.

On the combined implementation revision above, both commands passed from the
#23 worktree using the checked-in flake shell:

- `direnv exec . ./check-foundation.sh`: exit 0; dependency-free foundation passed.
- `direnv exec . ./check.sh`: exit 0; all 93 modules freshly rechecked and the
  exhaustive transitive axiom audit passed. Its union is exactly
  `[propext, Classical.choice, Quot.sound]`.

Logs are `/tmp/conaled-spec15/23-foundation.log` and `23-full.log`. The exact
candidate containing this report is recorded in the #23 handoff. No Lean source,
proof-audit infrastructure, runtime operation, toolchain or dependency changed
in #23, so no additional runtime or audit-regression fixture was required.
The initial command encountered the worktree's unapproved `.envrc`; after
`direnv allow .` and linking the pinned dependency packages, both checks above
completed. Project build output remained local to this worktree. The final full-spec review must compare the starting commit to the
passing integration candidate, exclude the unrelated user documentation, and
report Standards and Spec independently. Until that review passes on the actual
integration tip, implementation coverage and builds do not establish milestone
completion.
