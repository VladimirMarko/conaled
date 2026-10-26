# Reusable data-structure constructions and interpretation contracts

Architecture assessment for [#176](https://github.com/VladimirMarko/conaled/issues/176),
2026-10-26. Baseline: `5f55fbdec22fd01358a140286ee44cddc737410b`.
The prerequisite [#175 survey](functional-data-structures.md) was accepted at
`9cb0862f5d8909a0acd585bbe987ef9b326a2e71`. Its coverage statements are dated;
this baseline also includes the Dijkstra and measured random-access integrations
[#180](https://github.com/VladimirMarko/conaled/issues/180) and
[#181](https://github.com/VladimirMarko/conaled/issues/181).

**Build on the existing representation and interpretation interfaces.** Start
with ordered-summary construction laws, two replaceable realizations and a
small interpretation test using the existing internal derivation of relational
composition. Keep representation-specific invariants and recursion local. This
would add evidence for a toolkit without making a container its organizing
principle or requiring every ordinary Lean caller to encode a program in syntax.

This document proposes a bounded first slice and follow-up specifications. It
adds no Lean declarations, establishes no new proved claim, and settles no ADR.
Existing declarations are cited separately from proposed examples and obligations.
The [architectural standard](../agents/architectural-quality.md),
[language direction](../language-direction.md) and [shared glossary](../../GLOSSARY.md)
remain the criteria. #177 owns resource assessment; #178 owns the finger-tree
fit decision after both assessments.

## What varies, and what a contract must expose

| Variation | Example | Evidence required |
| --- | --- | --- |
| Element type | Nat and String sequences | A polymorphic construction and its stated assumptions. This does not change the mathematical setting. |
| Representation | List, valid symmetric pairs, cached binary digits, DList | A decoder or relation, invariant preservation, operation refinement and connected clients. Decoder injectivity is optional and must not be presumed. |
| Mathematical setting | Ordinary types and predicates; nonconstant presheaves with natural operations and stable predicates; sheaves with local existence | An interpretation of the argument's actual rules and a comparison to the intended mathematical observation. A monoid parameter alone supplies none of these interpretation obligations. |
| Execution/resource interpretation | Count branch visits, charge copies, retain ordered events, or model shared evaluation | An instrumented executor/erasure contract and preservation of the selected observations and bounds. Semantic equality alone cannot transfer the objective. |

An operation interface states the operations that a consumer needs. An
observation states what counts as agreement. An invariant restricts valid raw
representations. A refinement law connects an operation to an independent
specification. A cost statement adds its evaluation model and workload. Do not
put all five into a mandatory container class: length observation needs neither
indexed update nor balancing, and relation composition needs neither a monoid
nor a total decoder.

## Existing machinery and actual callers

| Need | Inspected implementation and reusable laws | Existing consumer and implication |
| --- | --- | --- |
| Exact representation composition | [`Squares.Rep`, `Square`, `compose`, `Rep.after`](../../Squares.lean) | [`RandomAccess.updateQuery_refinement`, `pushPop_exact`](../../Applications/Sequences/RandomAccess/Representation.lean) compose actual algorithms through List meaning. New realizations can satisfy that observation without exposing digit constructors to clients. |
| Invariant-bearing and many-valued interpretations | [`Relational.RelRep`, `RelSquare`, `compose`, `product`, `witnessSquare`](../../SquareKit/Relations.lean) | [`Sequences.Symmetric.editHead`, `prefixLengths`](../../Applications/Sequences/Symmetric/Observation.lean) retain validity. A relation can include `Inv r` instead of demanding an injective decoder. `witnessSquare` retains semantic data; it does not prove erasure. |
| Composition through intermediate representations | [`compRel_assoc`, `existentialSquare`, `existential_reassociate`, `Intermediate`, `forgetIntermediate_natural`](../../SquareKit/RelationComposition.lean) | The associativity theorem invokes `Internal.Associativity.inSet`; it is already an ordinary interface to an interpreted proof. `existentialSquare` requires agreement of the middle maps. Stored witness data and existential proof are distinct carriers. |
| Fold/scan refinement on reachable states | [`SquareKit.ListFusion.foldr_reachable`, `foldl_reachable`, `scanl_reachable`](../../SquareKit/ListFusion.lean) | [`Sequences.Symmetric.scanl_snocSL_refinement`, `fromSL_initsSL`](../../Applications/Sequences/Symmetric/Prefixes.lean) and [`Resources.run_value_fusion`](../../Applications/Resources/Workload.lean) avoid repeating the list induction. Their statements remain ordinary finite-list theorems. |
| Ordered measurement algebra | Mathlib [`FreeMonoid.lift`, `lift_ofList`][free], Batteries [`DList.invariant`, `append`][dlist], Mathlib [`DList.listEquivDList`][dlist-equiv] | [`Examples/PotentialAccounting`](../../Examples/PotentialAccounting.lean) uses free-monoid observations. DList already connects function composition to ordered List append. These provide semantic laws, not cached-update or cost theorems. |
| Current measured indexed consumers | [`Resources.RandomAccessCosts.measuredUpdateQuery_value`, `measuredUpdateQuery_cost`, `measuredUpdateQuery_bound`, `bulkRun_append`, `bulkRun_reweight`](../../Applications/Resources/RandomAccess/Observation.lean) | [`Examples/RandomAccessCosts`](../../Examples/RandomAccessCosts.lean) supplies checked costs and counterexamples. #181 has already reconstructed lookup/update costs deferred at #175's baseline. `observedBulk` leaves decoding traversal uncharged, explicitly; comparison work must not misread that as free materialization. |
| Bounded store updates | [`Dijkstra.Store.lookup_write`, `accum_lookup`](../../Applications/Dijkstra/Store.lean) | [`Dijkstra.Core`](../../Applications/Dijkstra/Core.lean) uses a Vector store. Repeated updates retain their order. Reuse these declarations before proposing a generic array slice; this does not imply the whole archived Arrays module has been reconstructed. |
| Operation/law separation and interpretation maps | [`RawMap`, `MapLaws`, `RawMap.induced`, `Reflects`, `transportLaws`](../../SquareKit/CategoryMap.lean); [`ProductMapLaws`, comparisons](../../SquareKit/CartesianMap.lean) | [`Examples/CategoryMaps`](../../Examples/CategoryMaps.lean) and [`MatrixCompiler.Maps`](../../Applications/Linear/Maps.lean) exercise non-strict comparisons and composition. Reflection is needed to derive laws for an independently chosen source equivalence. |
| Internal proof reuse | [`Internal.Associativity.forward`, `backward`, `inSet`](../../SquareKit/Internal/Associativity.lean); [`Presheaf.Model.sound`, `evaluation`, `formula_substitution`, `formula_restrict`](../../SquareKit/Internal/Presheaf.lean) | [`Presheaf.graph_valid`, `graph_evaluation`, `vertical_evaluation`](../../SquareKit/Internal/PresheafGraphs.lean) and [`Examples.Frobenius.fine_equivalence`, `restricted_witness`](../../Examples/Frobenius.lean) connect source derivations, model validity and objectwise observations. Model construction, not a new proof of the logic, is the proposed client obligation. |
| Local existence beyond pointwise predicates | [`SheafAssociativity.source_valid`, `left_comparison`, `right_comparison`, `associative`](../../SquareKit/Internal/SheafAssociativity.lean) | The same associativity derivations interpret on sheaves when carriers and relation subfunctors meet the stated sheaf conditions. Existentials are local, via covering sieves; an objectwise witness need not be available. No arbitrary data structure automatically satisfies those premises. |

This evidence goes beyond two representations of one Set carrier, but does not
establish transport of every data-structure construction. The restricted
[`Logic`](../../SquareKit/Internal/Logic.lean) fragment has binary atoms,
equality, conjunction and existential quantification with unary term arrows.
It has no list induction or recursive fold constructor. Applying its soundness
to relational associativity cannot transport the host-level induction inside
`foldl_reachable`. That requires a separately supported recursive fragment and
interpretations, or an explicit assumed operation/law whose realization is
proved locally.

### Felix comparison at the recorded revision

[docs/SOURCES.md](../SOURCES.md) pins Felix to
`6f36d28097db7ea5f5df3263db3e8be08f74e490`. The following comparison uses those
actual files, not an inferred feature list.

| Pinned Felix evidence | Local counterpart and consequence for this work |
| --- | --- |
| [`Comma.Type.Obj`, `_↬_`][comma] pair arrows with a commuting equation; arrow equivalence is induced by forgetting to the pair. | `Squares.Square` and relational witnesses already serve concrete representation contracts. Use a generic categorical map when categories and their chosen equivalences vary; do not repackage every sequence operation as a new comma framework. |
| [`CategoryH`, `ProductsH`, `StrongProductsH`, `CartesianH`][hom] distinguish preservation from comparison data and inverse comparison laws. | `RawMap`/`MapLaws` and `Comparison`/`ComparisonLaws` preserve that separation. Product objects need not be definitionally equal. A summary interpretation should expose only the preservation it uses. |
| [`LawfulCategoryᶠ`, `LawfulCartesianᶠ`][lawful] derive laws under homomorphically induced equivalence. | Local `RawMap.transportLaws` also permits an independently stated relation with reflection evidence. A lossy summary cannot justify raw representation equality or invariant reflection. |

The pinned `MakeLawful.agda` ends with a closed-structure TODO. Locally,
[`ClosedMap.transportLaws`](../../SquareKit/ClosedMap.lean) and
[`Examples/ClosedTransport`](../../Examples/ClosedTransport.lean) already
extend this direction through chosen exponential comparisons. The
[parity record's later closed-transport section](felix-parity-implementation.md)
supersedes its earlier scoped gaps. This work should neither reopen that solved
gap nor require exponentials for a construction that only uses ordered products.
None of the compared Felix declarations supplies a container cost theorem.

## Candidate construction: ordered summaries with replaceable realizations

Proposed semantic inputs are an element carrier A, a monoid M and a map
`measure : A → M`. The independent meaning of a finite sequence is the ordered
product of its mapped elements. Mathlib's `FreeMonoid.lift` supplies this
homomorphism, including preservation of concatenation; commutativity is
unnecessary. Do not rename that construction into a second universal fold API.

For an ordinary realization R, keep its sequence observation `decode : R → List A`
and validity predicate separate. A proposed cache adapter stores `r : R` and
`m : M`, with validity `Inv r ∧ m = summary (decode r)`. A checked operation must
preserve that predicate and refine the relevant List operation. An append
adapter can update the cache using monoid multiplication only when append's
decoder law and both input invariants hold. This specifies a law to implement,
not a theorem added by this assessment. The full sequence observation remains
available: equality of summaries is generally coarser than sequence equality.

Start with ordinary List and Batteries.DList for the append portion; both exist
and their conversion/append equations are inspected. Connect a batch-building
consumer to one final summary, then use the same ordinary summary on the
accepted symmetric-prefix observation as a second consumer. The two consumers
exercise different demands: final summary versus every prefix summary. Do not
promise that producing all prefixes costs as little as a final summary.

For an indexed-update consumer, reuse #181's measured update/query and compare
against an independently specified List update. A cached total cannot in
general be updated from only its old monoid value and a replacement element:
removing an arbitrary interior factor is not an operation of an arbitrary
monoid. Require a richer decomposition, restrict updates, or add justified
algebraic hypotheses. A tree is one possible decomposition, not the default
answer. #177 should decide the bounded cost comparison and charge encoding,
maintenance and observation.

## A bounded same-argument test in distinct settings

The proposed first cross-setting example is **refinement-chain reassociation
for ordered summaries**. It deliberately reuses an existing proof, rather than
claiming the list/cache construction has already been internalized. Give three
binary relations R (representation to sequence), S (sequence to summary), and
T (summary to final observation). Instantiate the existing two derivations of

```text
∃ m. (∃ xs. R r xs ∧ S xs m) ∧ T m o
    ↔ ∃ xs. R r xs ∧ ∃ m. S xs m ∧ T m o.
```

These are specifications for proposed checked cases. The source derivations
and soundness theorems exist; the data-structure models below are not yet Lean
implementations.

### Ordinary Set interpretation

Let A be `Nat × Bool`, let M be `Nat × List Bool` with length addition and
ordered word concatenation, and set
`summary xs = (xs.length, xs.map Prod.snd)`. Let raw cached representations be
`List A × M`. Define R by `xs = r.1 ∧ r.2 = summary xs`, S by
`m = summary xs`, and T by `o = m.1`. Plain List is the alternative realization,
with R given by equality; it does not carry a redundant cache.

`Relational.compRel_assoc` supplies reassociation for either R. No decoder
injectivity, nonempty carrier, commutative summary or witness selection function
is required. The word component is a diagnostic noncommutative observation,
not a proposed compact or fast cache. Checking a concrete realization's append
and summary laws still requires its local finite-list arguments.

### A nonconstant presheaf interpretation

Use a two-object indexing category J whose opposite has one nonidentity arrow
`fine → coarse`. Specify the presheaves and their restriction maps as follows;
identity and composition laws are part of the implementation obligations.

| Sort | Fine sections | Coarse sections | Restriction |
| --- | --- | --- | --- |
| Sequence | `List (Nat × Bool)` | `List Nat` | Map `Prod.fst` in order |
| Summary | `Nat × List Bool` | `Nat` | First projection |
| Cached representation | Fine sequence × fine summary | Coarse sequence × coarse summary | Product of the preceding restrictions |
| Observation | `Nat` | `Nat` | Identity |

At the fine object use the preceding R, S, T. At the coarse object use the
same definitions with `summary xs = xs.length` and T as equality. Each relation
must be made a subfunctor of the corresponding product: valid fine caches
restrict to valid coarse caches because mapping elements preserves length;
S and T obey the same restriction. Plain sequence representations supply the
second realization. Both monoid multiplications must be natural, with ordered
word concatenation at fine and addition at coarse.

The implementation should instantiate `Presheaf.Model` with these four carrier
functors and three stable relations, then apply `Model.sound` to the unchanged
`Associativity.forward` and `backward`. `Model.evaluation` compares the resulting
subfunctor equality with the objectwise observation; `formula_restrict` proves
that a fine witness restricts. This is an argument interpreted in a presheaf
category with compatibility along a nonidentity arrow, not merely two monoids
supplied to one Set theorem. Evaluation at each object recovers the ordinary
interpretation. No general functor between arbitrary settings is thereby built.

A required negative test is the fine raw cache
`([(3,true)], (1,[false]))`. It fails fine R because its word cache is wrong;
its coarse restriction `([3],1)` satisfies coarse R. Thus truth is preserved
along restriction for valid inputs, but fine validity cannot be recovered from
coarse validity. The same test prevents a lossy summary from becoming the
library's semantic equality. A positive test uses `(1,[true])` and retains the
actual intermediate sequence and summary in the reassociated statement.

The missing work is concrete model construction, stability/naturality proofs,
these connected cases, and a public ordinary wrapper if existing
`compRel_assoc`/`existential_reassociate` do not already meet the callers' needs.
Do not add a wrapper just to rename them. No new sequent calculus, sheaf model,
list object in an arbitrary category or recursion-preservation theorem is
needed for this bounded test. A later sheaf instance must additionally supply
sheaf carriers and relation predicates for `SheafAssociativity.associative`;
replacing its local existential with a global decoded value would change the
claim.

## Assumptions that cannot be hidden

| Concern | Required distinction and implementation obligation |
| --- | --- |
| Equality | Raw cache equality, ordered List equality, summary equality and hom equivalence are different. Use `RawMap.Reflects` only when proved; induced equivalence does not recover information discarded by a summary. |
| Witnesses | `compRel` uses existence in Prop; `Intermediate` stores a middle value as data. Sheaf composition admits local witnesses. Neither `witnessSquare` nor existence authorizes a runtime selector or removal of stored data. |
| Order | Summary multiplication preserves sequence order; no commutativity is needed. Sorted search additionally needs the ordering and its link to sequence semantics. Noncommutative test summaries catch accidental permutation. |
| Partiality | Random-access lookup returns Option; out-of-range update is totalized as List.set. Empty endpoint queries and failed search must remain visible. A relational specification can be partial, but `RelSquare.impl` itself is a total function. Do not turn absence into a default value without specifying that choice. |
| Induction/recursion | Finite-list fusion and representation recursion are host Lean proofs. The proposed reassociation proof needs only conjunction and existential rules. Transporting list induction or nested recursion requires additional semantics, not merely products or a monoid. |
| Decidability | Algebraic summary/refinement statements do not need decidable element equality. An executable invariant checker, equality-based lookup or search predicate needs its own decision procedure and correctness law. |
| Products and comparisons | Cache pairs and relation contexts use products. Categorical interpretation maps use explicit comparisons, possibly isomorphisms, rather than literal object equality. Do not assume all interpretations preserve exponentials or induction. |
| Search | A measured split must expose its initial/final predicate conditions and the appropriate monotonicity/transition claim. A summary homomorphism alone proves neither existence nor uniqueness of a split. |
| Resource observations | `Resources.reweight_run` preserves additive composition; bounds require order preservation and optimization transport requires candidate coverage. A natural semantic map can erase cost information. #177 owns the explicit models. |

## Design comparison and recommendation

| Approach | Caller effort and proof reuse | Composition and locality | Decision |
| --- | --- | --- | --- |
| **Ordinary contracts with optional interpretation adapters** | Ordinary callers supply operations, independent meanings and local refinement laws. Reuse ListFusion, FreeMonoid, squares and measured execution. Cross-setting clients supply models to the already checked derivations. | Representation recursion/cache maintenance stays local; clients compose existing contracts. Separate adapters expose actual setting requirements. | Recommended first slice. Check that the summary cache removes repeated obligations in both realizations before giving it a public structure. |
| **Require every construction through an internal container signature** | Could eventually reuse recursive derivations across settings, but current restricted Logic cannot express those folds. Callers would first need a richer syntax, model obligations and a translation from ordinary proofs. | A demonstrated recursive fragment could centralize proof work; prematurely bundling all operations/invariants/search/costs would spread irrelevant obligations to small clients. | Research successor when a concrete repeated recursive argument justifies it. Do not make it a prerequisite for ordinary data-structure use. |
| **Implement a measured balanced tree first and abstract later** | Quick access to a rich concrete interface, but consumers inherit balancing/search/measurement assumptions before variation is demonstrated. Existing simpler clients may need none of them. | Refactoring general laws out later risks tree-shaped interfaces and duplicate proofs for alternatives. | Finger trees may be an optional adapter after #178, not the foundation of this workstream. |

The first approach has a small seam backed by actual variation: List and DList
already implement append differently; symmetric prefixes and batch summary
observe different outputs; Set and a nonconstant presheaf interpret the same
relational proof differently. The first slice should demonstrate those uses,
not introduce an extensible hierarchy of speculative container capabilities.

## Proposed bounded implementation issue

**Title:** Construct ordered-summary refinements and interpret their composition.

**Outcome:** reusable cache/summary preservation laws grounded in ordinary
List and DList realizations, direct Lean clients, and the concrete Set/presheaf
interpretations of their refinement chain. Depend on accepted #176; coordinate
with #149 and #181 to reuse existing sequence/count interfaces. This is one
bounded implementation-and-review scope with two connected deliverables, not a
new task graph. Publication follows acceptance of this assessment; it does not
bypass #177/#178 or authorize performance claims.

### Ordinary construction and clients

Acceptance:

1. Reuse `FreeMonoid.lift` for independent ordered meaning and the existing
   DList conversion/append laws. Keep validity, summary agreement and List
   agreement distinct; state exactly which monoid laws each result needs.
2. Prove append/empty cache preservation for the two realizations and expose
   their ordinary refinement contracts. Do not require equality of raw
   representations or a generalized search interface.
3. Connect a batch-build/final-summary consumer and the existing symmetric
   prefix observation to the shared summary law. Include length and an ordered
   noncommutative summary, empty and duplicate-element cases, and an invalid
   cache case. A summary-only theorem must not claim full sequence agreement.
4. Use statement review and checked applications, fresh build and exhaustive
   audit. State that this slice proves semantics; resource comparisons wait for
   the models from #177. No runtime benefit follows solely from caching.

### Interpret the same refinement chain

Use the preceding concrete Set and nonconstant-presheaf models of one existing
associativity derivation, with ordinary client observations. Reuse the first
deliverable's summary definitions; source derivability remains independent of
the particular representation.

Acceptance:

1. Build the four presheaves, three stable relations and plain/cached
   realizations specified above. Prove naturality and relation stability;
   construct `Presheaf.Model` without adding assumed semantic-validity rules.
2. Apply the unchanged source `Associativity.forward/backward` through Set
   soundness and `Presheaf.Model.sound`. Connect subfunctor validity to ordinary
   endpoints with `evaluation`, preserving both intermediate witnesses.
3. Check the positive and failed-reflection examples, and restriction of the
   positive witness. Explain which proof was reused and which realization
   obligations remain local. Do not describe this as transport of list induction.
4. Preserve syntax-free ordinary entry points, statement review, fresh build and
   exhaustive audit. A new wrapper must reduce demonstrated caller work rather
   than duplicate `compRel_assoc` or `existential_reassociate`.

This scope needs neither a new package nor a change to the current directory layout.
If implementation reveals a settled architectural decision, record it through
the repository's domain-documentation workflow. Broader recursive internal
construction, arbitrary setting changes, higher identity and local-to-global
selection remain separately scoped research.

## Fit criteria for #178 and later case studies

A case study should contribute a construction or law used by distinct consumers
and support an alternative realization under the same relevant observations.
A client should import the abstract law and selected adapter, with balancing
and node constructors confined to the realization. It must identify both the
ordinary proof premises and which internal derivation, if any, is interpreted
in another mathematical setting. Useful Set-only developments remain possible
when their limit is stated, without claiming they meet the full ambition.

For finger trees, separate ordered sequence semantics, the summary homomorphism,
cache correctness, balancing/nested recursion, and split/search predicate laws.
Check whether the first two already follow from the proposed simpler slice.
Only the remaining operations required by a real consumer can justify the
additional representation. #177 must supply explicit workload/evaluation and
measurement-cost criteria before a performance comparison is accepted.
Proceeding requires a bounded source/proof scope and an alternative realization;
narrowing or rejecting the candidate is valid. This assessment does not select
that outcome or make finger trees the canonical library, compiler or language
representation.

[free]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/FreeMonoid/Basic.lean
[dlist]: https://github.com/leanprover-community/batteries/blob/66e469188fe07963e5cf666c7d4433f45b8131c5/Batteries/Data/DList/Basic.lean
[dlist-equiv]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/DList/Instances.lean
[comma]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda
[hom]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda
[lawful]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda
