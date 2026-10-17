# Felix architectural parity implementation plan

This plan implements the planning deliverable in [issue #1](https://github.com/VladimirMarko/conaled/issues/1), version 2026-10-17T04:58:03Z. Read the [capability inventory and interface recommendation](felix-parity.md) first. The initial milestone is P1–P6 below. Completion of this document does not mean the milestone has been implemented. The broader port and completion of Felix remains [#8](https://github.com/VladimirMarko/conaled/issues/8).

The proposal adds reusable infrastructure and compatibility adapters in `SquareKit`, keeps implementations in `Applications`, and exercises them in `Examples`. It preserves ADRs [0001](../adr/0001-modules-and-proof-dependencies.md), [0002](../adr/0002-relations-and-synchronization.md) and the application-specific contracts. No accepted ADR is replaced by this planning change. Root foundation modules remain dependency-free. A future incompatible interface change requires an explicit ADR revision.

## Dependency order

P1 → P2. P3 and P5 can start independently after P2. P4 follows P3. P6 follows P3, P4 and P5 and supplies the non-function compiler comparison example using P3’s matrices. Thus square construction and compiler adapter work can proceed independently before their integration.

The linked issues below contain the published work packages. Each child carries the full scope, examples, acceptance criteria and validation requirements, so execution does not depend on recovering this conversation. Proposed names are sketches; existing declarations are verification seams, not permission to break their interfaces.

## Caller-work baseline and proposed reduction

The inspected local revision is `c17daf5a66b9812fdbc0cb37cd4e9c49b1949ce8`. These are source observations, not measured outcomes of a migration:

| Existing caller work | Proposed shared result | Work that remains local |
|---|---|---|
| `Applications/Linear/Compiler.lean:122–140`: `target` and `sound` each assemble the same six structural operations/laws plus the primitive case (and their hom/denotation fields). | P2 packages matrix evaluation preservation once; P5 derives the source adapter and soundness from that package. | Matrix coordinate identities, multiplication/evaluation compatibility and primitive meaning. |
| `Applications/Stack/Machine.lean:149–171` and `SquareKit/FirstOrder.lean:34–58`: two target assemblies and two `sound` assemblies with seven reflexive preservation fields each. | P3/P4 expose shared semantic projections; P5 reuses their preservation package to construct soundness. | Stack instruction/tail proofs and relational primitive preservation. |
| `Compiler.lean:266–292`: category/product/closed laws proved through `run`; `FirstOrder.lean:212–233`: additive-map category/product proofs. | P2 derives the category/product laws from lawful semantics; scoped closed results remain explicit. | Proving the semantics preserves each operation; no claim that all closed laws transport generically. |
| `SquareCompiler.lean:77–123` and `SquareKit/STLCRelations.lean:52–104`: separate full-source target and soundness assemblies. | P5 shares compiler preservation; P3/P4 supply the distinct exact and relational interpretations. | Exact exponential compatibility and function-relation obligations, with their different meanings. |

The compiler already has one syntax induction per frontend. The plan does not claim to remove duplicated application syntax inductions that do not exist. P6 must show actual reduction in repeated structural assemblies and proof obligations while charging every new adapter obligation to the same ledger. A move of code without shared callers is not a reduction.

## P1. [#9](https://github.com/VladimirMarko/conaled/issues/9): Separate raw categorical operations, semantic laws, and lawful adapters

Dependencies: none.

Implement reusable object-polymorphic operations in `SquareKit`, with hom-wise equivalence, congruence, and laws supplied separately. Start with identity/composition and optional terminal/product structure; add optional sum/distribution and closed operations needed by the full source adapter. Do not put primitives or a fixed source `Ty` into the shared operations. Keep the original foundation modules and public interfaces stable.

Reuse Mathlib categories for lawful equality-based models. For raw syntax lawful only modulo equivalence, construct a category on hom-setoid quotients after proving equivalence, congruence and category laws. Mathlib's existing `CategoryTheory.Quotient` assumes a lawful input category and is not a shortcut for this step. Prove the quotient equality iff the declared equivalence and descent of each supported operation. Keep raw executable representatives available; no extraction of executable code from quotient classes is required.

Public-interface example (design sketch, names not prescribed): a raw syntax hom `f`, its semantic setoid, and a law package produce `Q`; `Q.map (comp g f) = Q.map f ≫ Q.map g`. An existing lawful Mathlib category can supply the same operations without a second law hierarchy at the call site.

Acceptance: instantiate both raw `Compiler.Code` under `Compiler.Equivalent` and a lawful finite-matrix category over a commutative semiring. Show associativity modulo equivalence for raw terms whose constructors are unequal. Recover equality-based category laws for the matrix instance. Separate optional structure so the additive first-order target needs no closure. Document comparison with pinned Felix Raw/Equiv/Laws and the Mathlib reuse seam. Quotient lifting must not strengthen semantic equivalence into raw syntactic equality.

## Validation required

Use example-driven development and statement review for every new or changed Lean claim. Check public constructions and composition, including arbitrary inputs rather than only evaluated examples. Preserve applicable existing theorem statements, the dependency-free foundation check, and the complete build and transitive axiom audit (`direnv exec . ./check-foundation.sh`, `direnv exec . ./check.sh`). Run audit regression tests when proof infrastructure changes. Record exact revisions, commands, results, and any limitations. Runtime tests are required only for executable behavior that warrants them. Do not introduce admissions or new axioms.

## P2. [#10](https://github.com/VladimirMarko/conaled/issues/10): Share structure-preserving maps and transport categorical laws

Dependencies: P1.

Define reusable maps on objects and morphisms with preservation packages for only the operations used. Include identity/composition of maps, terminal/product comparison morphisms, and invertible comparisons where required. Do not restrict maps to definitionally identical object interpretations: match Felix's `ProductsH` and `StrongProductsH` capability. Expose an adapter to ordinary Mathlib functors on lawful categories or their hom quotients.

Transport category and cartesian laws along maps into lawful targets under the induced source equivalence, or a separately stated reflection hypothesis. Preservation alone does not prove laws under an arbitrary source equality. Require and prove the relevant congruence obligations. Keep generic closed-law transport explicitly outside this ticket; P5 needs preservation of chosen closed operations, not an unproved transport theorem.

Public-interface examples: derive `assoc`, terminal uniqueness, and product beta/eta for `Compiler.Code` from its evaluator and local operation-preservation proofs; compose two interpretation maps without re-proving preservation operation by operation. Include a product comparison that is an isomorphism rather than definitional identity, for example finite coordinates versus nested value products using `MatrixCompiler.encode`/`decode`.

Acceptance: all category/cartesian laws above are caller-visible under the declared equivalence; supply both strict and non-strict examples. A caller proves only local preservation/comparison obligations, not general category/product algebra. Recover existing raw syntax category/product results and record exactly which local definitions/proofs become shared applications. Cite the hypotheses of Felix `LawfulCategoryᶠ` and `LawfulCartesianᶠ` rather than claiming arbitrary law reflection.

## Validation required

Use example-driven development and statement review for every new or changed Lean claim. Check public constructions and composition, including arbitrary inputs rather than only evaluated examples. Preserve applicable existing theorem statements, the dependency-free foundation check, and the complete build and transitive axiom audit (`direnv exec . ./check-foundation.sh`, `direnv exec . ./check.sh`). Run audit regression tests when proof infrastructure changes. Record exact revisions, commands, results, and any limitations. Runtime tests are required only for executable behavior that warrants them. Do not introduce admissions or new axioms.

## P3. [#11](https://github.com/VladimirMarko/conaled/issues/11): Generalize comma squares and recover the exact representation interface

Dependencies: P2.

Provide general squares for distinct source categories and interpretations `L : C ⥤ E`, `R : D ⥤ E`, with object comparison arrows in `E`. Reuse Mathlib `Comma L R` for lawful categories. Support raw representatives via the equivalence-aware infrastructure and prove their connection to the lawful presentation; do not silently quotient away raw implementation data in executable callers. Reuse shared maps/law transport. Establish identity, composition, projections and the product structure under explicitly stated preservation assumptions, including non-strict comparison maps. Include general vertical pasting with a stated compatibility condition on the interpreted middle arrows; recover the concrete vertical operation from it. Distinguish Felix raw products with two strong product maps from Mathlib limit lifting with its weaker lawful hypotheses.

Public-interface examples: recover `Squares.Rep` and `Squares.Square` as the identity/identity comma specialization in types and functions, with round trips and identity/composition/product compatibility. Show a comma construction over finite matrices over ℕ, using identity and the doubling functor `n ↦ n+n`, `M ↦ blockDiag M M`, so its homs and composition are matrices rather than unrestricted functions. Prove the functor laws and exhibit an actual commuting square.

Acceptance: recover existing exact square operations and their public laws, including vertical pasting, sums/distribution, synchronized agreement, and the existing exponential/evaluation/curry beta/eta results. Supply a capability table separating general comma category/products, additional hypotheses for other structure, and Type-specific results. Do not claim arbitrary comma categories are closed. The Type exponential may remain a named checked specialization with a bridge to the general square presentation. Preserve its semantic function data and make no erasure claim. Preserve ADR 0001's dependency-free foundation by adding adapters under SquareKit, with no Mathlib import in root foundation files. If preservation of an interface proves impossible, propose an explicit ADR revision before changing it.

## Validation required

Use example-driven development and statement review for every new or changed Lean claim. Check public constructions and composition, including arbitrary inputs rather than only evaluated examples. Preserve applicable existing theorem statements, the dependency-free foundation check, and the complete build and transitive axiom audit (`direnv exec . ./check-foundation.sh`, `direnv exec . ./check.sh`). Run audit regression tests when proof infrastructure changes. Record exact revisions, commands, results, and any limitations. Runtime tests are required only for executable behavior that warrants them. Do not introduce admissions or new axioms.

## P4. [#12](https://github.com/VladimirMarko/conaled/issues/12): Connect relational contracts to the shared square infrastructure

Dependencies: P3.

Adapt `Relational.RelRep` and `Relational.RelSquare` through reusable structure-preserving maps. Retain relation preservation as the primitive contract. Connect graph relations to exact squares and total relation-witness spaces to the general square presentation. Prove compatibility with identity, composition, products and the existing function relation; retain existing round-trip and witness-composition theorems.

Public-interface examples: graph conversion of an exact square and its inverse recover both horizontal maps; interval multiplication preserves `Contains`; a stable-signal relation transports through composition. The witness carrier retains both represented and semantic values. No decoding function may replace a many-valued relation.

Acceptance: recover `toSquare_ofSquare`, `witness_compose`, relational product laws and curry/uncurry laws via the new adapters where applicable. Preserve interval enclosure and timing stability statements, and the counterexample `interval_cancellation_is_wider` showing why equality of point meanings does not imply equality of interval computations. State which generic facts are reused and which relational obligations remain local. Do not assert that witnesses are erased or that every relational analysis is an exact denotation functor.

## Validation required

Use example-driven development and statement review for every new or changed Lean claim. Check public constructions and composition, including arbitrary inputs rather than only evaluated examples. Preserve applicable existing theorem statements, the dependency-free foundation check, and the complete build and transitive axiom audit (`direnv exec . ./check-foundation.sh`, `direnv exec . ./check.sh`). Run audit regression tests when proof infrastructure changes. Record exact revisions, commands, results, and any limitations. Runtime tests are required only for executable behavior that warrants them. Do not introduce admissions or new axioms.

## P5. [#13](https://github.com/VladimirMarko/conaled/issues/13): Derive compiler soundness through shared categorical interpretations

Dependencies: P2.

Add source adapters interpreting the first-order and full source languages into the shared operations, with soundness expressed as preservation by a shared map between interpretations. Allow semantic categories beyond types/functions. Keep the fixed source grammars as frontends; remove their types and function-valued semantics as requirements of the shared categorical infrastructure. Recover the existing `Target`, `Sound`, and `compile_sound` interfaces through compatibility adapters, preserving callers.

Require only terminal/products/category structure for first-order compilation. Full STLC adds chosen exponentials, sums, distribution and their preservation obligations. Formulate the non-strict comparison/coherence conditions needed when object interpretations preserve these structures up to isomorphism. Do not treat Felix's unfinished generic closed homomorphism/law transport as a proved theorem. This ticket may prove a scoped closed-preservation interface; it must retain all existing local closed results without asserting universal closed-law transport.

Public-interface examples: first-order compilation into finite matrices and its evaluation map; a full-source captured lambda/application and captured sum case interpreted into the existing exact function representation. Show that composing interpretation maps yields compiler preservation without a fresh syntax induction. P6 will instantiate this preservation theorem between the two non-function matrix interpretations from P3; this ticket establishes the generic theorem and its existing-backend specializations independently of P3.

Acceptance: recover both `FirstOrderCompiler.compile_sound` and `CategoricalCompiler.compile_sound`, retain `FirstOrderCompiler.no_exponential`, and all existing higher-order exact/relational source examples. Prove naturality of compilation under the scoped structure-preserving map. Inventory local primitive obligations versus reusable structural obligations. Relational application integration is performed in P6 after P4.

## Validation required

Use example-driven development and statement review for every new or changed Lean claim. Check public constructions and composition, including arbitrary inputs rather than only evaluated examples. Preserve applicable existing theorem statements, the dependency-free foundation check, and the complete build and transitive axiom audit (`direnv exec . ./check-foundation.sh`, `direnv exec . ./check.sh`). Run audit regression tests when proof infrastructure changes. Record exact revisions, commands, results, and any limitations. Runtime tests are required only for executable behavior that warrants them. Do not introduce admissions or new axioms.

## P6. [#14](https://github.com/VladimirMarko/conaled/issues/14): Migrate representative applications and demonstrate categorical reuse

Dependencies: P3, P4, P5.

Route existing representative applications through the shared infrastructure: matrix/stack synchronization, arithmetic stack/incremental/interval composition, and a higher-order relational interval example. Retain application-specific primitive semantics, concrete matrix and bytecode implementations, and all public correctness statements. Preserve arbitrary stack tails, finite changes, enclosure, stability, and higher-order relation distinctions. Include timing's relation adapter from P4 in a checked composition.

Public-interface examples: `Examples.MatrixStack.jointSquare` and `agree_preserving_tail`; `Examples.ArithmeticPipeline.stack_after_update` and `incremental_output_enclosed`; `IntervalAnalysis.HigherOrder.capturedLambda_contains`, `capturedCase_left_contains` and `capturedCase_right_contains`. These are client programs of the shared abstractions, not parallel demonstrations that leave existing implementations disconnected.

Acceptance: trace each example through the generalized maps/squares/compiler preservation theorem. Record a before/after ledger of caller-written operation definitions, structural preservation proofs, syntax inductions, and primitive obligations, listing declarations rather than optimizing line counts. Remove or factor repeated caller definitions/proofs, with at least two independent backends consuming the same shared construction. Any new adapter obligations must be included in the ledger. Reject a migration that merely adds an unused abstract layer or moves duplicated proofs unchanged. Keep unavoidable representation-specific proofs local. Instantiate P5 compiler preservation between P3’s identity and doubling matrix interpretations, then recheck the matrix non-function and exact Type recoveries. Publish an updated inventory that marks the initial milestone achieved only if all P1–P6 acceptance criteria pass; remaining Felix work stays in #8.

## Validation required

Use example-driven development and statement review for every new or changed Lean claim. Check public constructions and composition, including arbitrary inputs rather than only evaluated examples. Preserve applicable existing theorem statements, the dependency-free foundation check, and the complete build and transitive axiom audit (`direnv exec . ./check-foundation.sh`, `direnv exec . ./check.sh`). Run audit regression tests when proof infrastructure changes. Record exact revisions, commands, results, and any limitations. Runtime tests are required only for executable behavior that warrants them. Do not introduce admissions or new axioms.
