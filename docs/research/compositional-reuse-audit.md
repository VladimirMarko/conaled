# Reuse of existing compositional machinery

Research delivery for [#349](https://github.com/VladimirMarko/conaled/issues/349),
coordinated by [#235](https://github.com/VladimirMarko/conaled/issues/235).
The inspected baseline is `03f13f4b72f327b9cb13e9a96d12ca53f2736184`.
This report records source inspection and paper specializations of existing
Lean declarations. It adds no Lean theorem and claims no measured productivity
improvement. The examples labelled paper below have not been elaborated.

## Finding

The library already derives many whole-program results from local laws.
The strongest immediate opportunities are exposing those results at existing
client boundaries and sharing adapters. A new universal interface is not
necessary to discharge the concrete repeated inductions identified here.
Changing logic, dependent contexts, or the information carried by meaning
remains a separate mathematical requirement; existing interfaces do not settle
those questions by being reusable within their present scope.

## Declaration and caller evidence

Paths below are relative to the repository root. Declaration names identify
both the shared result and the inspected caller; this is not an import census.

| Capability | Derived result and actual caller | Assessment |
|---|---|---|
| Exact horizontal and vertical pasting | `Squares.compose`, `vertical`; `Applications/Convolution/Polynomial.lean` uses them in `normalizedMulSquare` and `languageMulSquare` | Already combines normalization with multiplication and then changes coefficient meaning. Neither proof needs an institution package. |
| Relational composition and witness presentation | `SquareKit/Relations.lean`: `compose`, `witnessSquare`, `witness_compose`; `SquareKit/RelationalCategory.lean`: `witnessMap_laws`, `witnessProducts_laws`, `witness_evaluation`, `witness_curry` | The bridge retains representation and semantic value. It does not justify executing or erasing that semantic value. `Sequences.AbstractFIFO.Simulation.runSquare` already derives all-word relational preservation by composition. |
| Category and optional law transport | `RawMap.induced`, `transportLaws`, `comp_laws`; `ProductMap.transportLaws`; `ClosedMap.transportLaws`; coproduct/distribution siblings | `Applications/Linear/Maps.lean` obtains coordinate and matrix laws through transport and composes matrix→coordinate→value interpretations. `CodeCategory.closedLaws` derives semantic beta/eta. This is successful reuse, not a missing feature. |
| Compiler/relational bridge | `Applications/Incremental/Core.lean`: `Compiler.sound` uses `RawMap.comp_laws` and `RelationalCategory.semanticsProducts_laws`; `compile_update` uses `FirstOrderNaturality.compile_sound` | Local target facts already induce all-term compilation correctness. Wrapping this final theorem as an institution field would not derive anything further. |
| Primitive-rule proof expansion | `GuardedRuleInterpretation.RuleInterpretation.transport`, `compose`, `reduct`; `Internal/DependentJudgments/PrimitiveSigma/Reindexing.lean`: `retain` | Already replaces a duplicated proof induction in a same-signature extension. The unchanged algebra explains exact reduct composition; it does not establish arbitrary signature-changing interpretations. |
| Indexed construction/observation | `IndexedCompositional.Rule.fold_morphism`, `bind_morphism`, `Behavior.observe_morphism`; `Applications/Languages/IndexedCompositional.lean`: `recovered`, `recovered_tree`, `recovered_concat`, `recovered_star` | Local output/transition laws give arbitrary-term selected decisions and the entire finite trie. `read_morphism` still repeats the generic finite-path argument because the public client observes words, not `Behavior.Path`. |
| Compatible extensions | `ObservationComposition.Rule.compare_observations`; `EquationComposition` and `Applications/Languages/EquationComposition.lean` | A common independent interpretation plus local compatibility derives agreement. Equality of old cells alone is not assumed sufficient for two extension orders. |
| Finite state simulation | `Applications/Progress/Reactive.lean`: `Feedback.run_related`; `FRP/Pipeline.lean`: `response_run_related`; `FRP/LifecyclePipeline.lean`: `run_consumer_related` | Reuse already retains every optional output position and final related states. The pipeline `run_factor` and `run_append` proofs still have parallel recursions across engine and lifecycle variants. |
| Reachable-state fusion | `SquareKit/ListFusion.lean`: `foldl_reachable`, `scanl_reachable`; `Resources/Workload.lean`: `run_value_fusion`; `Resources/SymmetricWorkload.lean` uses it | This existing abstraction is a better first candidate for FIFO erasure proofs than introducing another evaluator. `Resources/FIFOContracts.run_erases` independently proves the analogous induction. |
| Quantitative observations | `Resources.Measured.reweight_bind`, `Resources.Workload.reweight_run`, `PreservationBounds.comparison_comp`, `Interaction.Refines.bound` | Additive preservation and monotone bounds have different hypotheses. `FIFOContracts.reobserved_bound` already composes both. Exact value squares cannot replace the accounting premise. |
| Choice of adjoints | `AdjointComparison.curry`, `uncurry`, `mate`; `SheafDependentProduct.comparison_curry`, `baseChange_comparison`; `Examples/NativeSliceProducts.lean` | Already derives compatibility between chosen right adjoints, including base-change comparisons. This is a concrete reusable capability for richer interfaces, not an unused discovery. |

The declaration bodies and callers above are the primary local sources. The
[Felix implementation record](felix-parity-implementation.md) supplies the
broader inventory, but its historical exclusions must be read with its later
closed, coproduct and distribution transport sections.

## Paper specialization A: word observations as indexed paths

The parser's public `read` returns `Decision (P word)` under the bound
`word.length ≤ n`. The generic observer follows a typed path and returns the
output at its final index. For the existing parser behavior, define the adapter

```
wordPath P n word bound :
  behavior.Path (P,n) (fun suffix => P (word ++ suffix), n - word.length)
```

This is a paper signature, not checked Lean code. At the empty word use the
stop path, with the elementary index identifications. At `a :: rest`, the
bound gives a successor depth; use a step labelled `a`, followed by the path
for the derivative language and remaining word. Prove by induction that
observing this path agrees with `read`, transporting its final output along
`word ++ [] = word`. Then `Behavior.observe_morphism` supplies
`read_morphism` for every coalgebra morphism. Both sides transport along the
same index equality, so the result is equality of selected decisions, not
merely equal truth values.

Existing callers `recovered` and `recovered_trie` can keep their word-oriented
statements. `Rule.fold_morphism` continues to discharge construction induction;
the path adapter discharges observation induction. Its one-time cost is the
index calculation, depth subtraction and the `read`/path identification. The
repeated cost removed is proving path preservation again for each word-facing
observer. The current short direct proof may remain preferable if the adapter
is awkward and has no second consumer. This is an API/encoding opportunity,
not evidence of missing mathematics or a measured saving.

A cross-domain check can use a depth-indexed finite state machine: requests
consume one command and output records its full retained state. It has the
same depth/path issue without parser syntax. Requiring this second client
prevents a parser-specific wrapper from being advertised as a generic gain.

## Paper specialization B: finite execution and erasure

`Resources.run_value_fusion` already proves that a measured execution decoded
after running equals a native fold, assuming an invariant and a one-step
commuting equation. Instantiate it for `FIFOContracts.Instrumentation m`:

- measured step: `m.measured`;
- specification step: `Sequences.AbstractFIFO.step ops`;
- decoder: identity on the queue;
- invariant: `True`, with trivial closure;
- local commuting fact: `m.erases`.

Its conclusion is exactly the left side of `FIFOContracts.run_erases` equal
to `cs.foldl (fun q c => step ops c q) q`. A reusable identification of
`AbstractFIFO.run` with that fold yields the existing theorem. No budget law,
potential, category, or equality decision procedure is required. That
identification still needs one structural proof; accounting for it matters.
Repeated state-fusion clients would then inherit the generic theorem.
`run_state` alone also suffices for this identity-decoder case, so the richer
fusion theorem should be used only when a client actually changes state meaning.

For a different domain, each FRP pipeline is a finite machine whose step
returns a new state and an emitted event. Encode its execution as a left fold
on `(state, accumulated events)`, appending the current event at each step.
`ListFusion.foldl_reachable` can transport that accumulator to the separately
run engine and consumer used by `run_factor`. The local equation is precisely
that the consumer processes the engine's current emission. List accumulation
is proof-side here; no replacement runtime or performance claim follows.
Retain the original tagged/optional event list, including `none` positions.

The two FRP `run_factor` proofs currently discharge this recursion separately.
A common runner/adapter could also derive `run_append` from fold composition,
but the source definition may be shorter than the adapters. Compare complete
native and shared caller code before migrating either pipeline. This is a
bounded reuse experiment with observable acceptance tests, not a directive to
refactor every state loop.

## Canonical mates as an optional capability

For `a : L ⊣ R` and `b : L ⊣ S`, the canonical comparison
`a.rightAdjointUniq b` is already available. `AdjointComparison.curry` states
that postcomposing a transpose under `a` with this comparison gives the
transpose under `b`. `uncurry` derives the corresponding elimination equation.
For a square `t : G ⋙ L' ⟶ L ⋙ H`, `mate` proves compatibility when both chosen
right adjoints change. Its proof uses the counit equation and naturality of
`t`, rather than assuming the desired mate compatibility as another field.

A progressive interpretation interface can require only the adjunction when
transposition is needed, and derive these choice-comparison laws. The existing
sheaf consumer does exactly that: `SheafDependentProduct.baseChange_comparison`
is an application of `AdjointComparison.mate`. The proposed institution study
should reuse this result whenever its hypotheses fit; it should also test a
connection where they do not.

In particular, the theorem does not establish invertibility of arbitrary
mates. `DependentBaseChange.WithAdjunction.mate_isIso` has additional actual
pullback data and derives invertibility through `mate_conjugate` and the
proven left comparison isomorphism. Requiring that final invertibility field
from every new presentation would discard a useful derivation in this case.
Conversely, omitting its pullback hypotheses would overstate the theorem.
These are source-checked distinctions in the existing Lean code, not a new
formalization of adjoint logic.

## Substantive failure cases

**Exact value preservation does not transport cost.**
`Resources.Measured.same_value_different_cost` compares `((),0)` with `((),1)`.
Their value decoder agrees and their costs differ. The first has cost at most
zero and the second does not. Thus a proposed cost-transport theorem obtained
from only value-square commutation is false. `Refines.bound` instead needs
coverage of target behaviors, a cost comparison, and monotonicity; `reweight_run`
needs additive preservation. Neither condition follows from semantic value
agreement. This countercase preserves the distinction between quantitative
observation and extensional value, including when both are deterministic.

**Relations cannot always be replaced by decoding functions.** An interval may
represent both endpoints. Choosing one endpoint loses the other membership
claim. The witness-space bridge keeps the point as data, so it is not a free
runtime replacement. ADR [0002](../adr/0002-relations-and-synchronization.md)
and `Relational.witnessSquare` specify this boundary. A `Prop`-valued relation
also cannot retain several distinguishable proofs of the same relation;
higher identity data must be represented elsewhere. This is owned by #348.

**Indexed templates do not solve arbitrary dependent substitution.**
`IndexedCompositional.Signature.child` chooses each child's sort from the
operation and child position. It does not let that sort depend on a previously
constructed child's value. Encoding a whole dependent context into an index
may be possible, but its substitution/comparison laws are extra obligations.
#344 must compare the general dependent-theory machinery on its own merits.
No successful parser specialization proves that this indexed template engine
is already a universal dependent frontend.

**Effects need the specified joint observation.** The exact optional-output
simulation used in FRP preserves order and silent positions. A relation that
merely identifies the set of emitted batches cannot recover that theorem:
`[some x, none]` and `[none, some x]` have the same nonempty outputs but different
positions. Similarly, replacing a joint probabilistic observation by its
marginals requires a separate sufficiency argument. The audit does not propose
such forgetting as an adapter. See the existing
[preservation inventory](preservation-contract-inventory.md) for those contracts.

## Progressive capabilities and comparison with new frameworks

Existing `CategoryOps`, `HomEquiv`, `MapLaws`, product/closed comparisons,
reflection and law packages demonstrate branching capabilities. A map can
compose without reflecting equality; reflection can be added when transporting
source laws. `CodeCategory` uses the induced semantic relation rather than
requiring injectivity of the raw representation. Likewise a state step needs
no resource algebra to execute; measured sequencing adds one; transferring a
bound adds order and comparison hypotheses.

This is a concrete pattern for #343: a shared interpretation/comparison can
support separate satisfaction, selected evidence, dependency and computation
capabilities. For each layer, distinguish input certificates from derived
results. In the current library, local rule certificates derive whole-proof
transport, local constructor/observer compatibility derives all-term finite
observations, and primitive map laws derive categorical laws. Asking for those
final results as interface fields does not repeat those derivations.

Institutions add value where statements and model restriction change together,
especially across logics. BHL theory interpretations add value where operations
map to syntax templates and dependent rules must transport. Existing exact
squares and same-signature rule maps do not already provide either generality.
Compare the new capabilities on new clients and recover existing ones; do not
make an adapter to current code a mathematical admission requirement.

## Upstream boundary and priorities

Pinned Felix was inspected at
`6f36d28097db7ea5f5df3263db3e8be08f74e490`:
[MakeLawful.agda](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
derives category/cartesian laws under the induced `H-equiv`;
[Homomorphism.agda](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda)
separates local preservation and supplies identity/composition. No upstream
build was run here. [#25](https://github.com/VladimirMarko/conaled/issues/25)
already owns the matched interpretation, composition and comma-client comparison
with full setup/author-effort records. This audit does not duplicate or claim
completion of that evaluation.

| Priority and owner | Concrete next acceptance test | What would justify rejection or deferral |
|---|---|---|
| First: #343, coordinated with [#351](https://github.com/VladimirMarko/conaled/issues/351) | Where adjunction hypotheses fit, derive curry/evaluation/mate compatibility from existing results; compare a shared-meaning wrapper with separate capabilities. Include an actual logic change and a selected-witness consumer. | Packaging final preservation as fields with no derived reuse; imposing an adjunction on arbitrary interpretation maps. |
| First: [#353](https://github.com/VladimirMarko/conaled/issues/353), under #235 | Recover parser word observations through typed paths and FIFO state erasure through existing fusion; include a second non-parser observation client and one FRP factorization comparison. | Adapters exceed recurring work without exposing new capability; keep short native facades rather than force migration. |
| In parallel: #344 | Compare signature-changing dependent theory maps with the existing same-signature `RuleInterpretation` specialization. | A fixed indexed AST alone is not a substitute for the required dependent substitution result. |
| In parallel: #348 | Retain relational and higher-identity observations through an appropriate semantic boundary. | Graphifying a many-valued relation by arbitrarily choosing a point, or truncating selected higher data. |
| Existing owner: #25/#8 | Reproduce the three matched Felix tasks and record complete caller obligations. | Import counts or this audit's source reading are not the requested comparison. |
| Follow-ups: [#351](https://github.com/VladimirMarko/conaled/issues/351) and [#352](https://github.com/VladimirMarko/conaled/issues/352), from #350 | Test adjoint categorical and mode-based approaches on independent clients; coordinate the mate capability with #343. | Adjoint uniqueness is not evidence that arbitrary compiler or institution arrows form an adjunction. |

Successor [#353](https://github.com/VladimirMarko/conaled/issues/353), under #235:
**Exercise shared finite observation and execution adapters across parser, FIFO
and FRP clients.** Freeze the existing public
statements and native implementations above. Implement the word-path adapter
and the native-run/fold identification, recover the selected-decision and
state-erasure theorems, and compare one FRP factorization through the same
finite-execution machinery. Require exact silent/tagged outputs, a redundant
queue representation, arbitrary finite inputs, and the cost countercase.
Record setup versus recurring obligations and preserve native APIs. The result
may reject an adapter after the checked comparison; no universal runner or
repository-wide migration is prescribed. #353 owns the bounded experiment;
#235 retains coordination of broader architectural reuse.
