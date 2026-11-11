# Full Felix correspondence at the orchestration checkpoint

Issue [#8](https://github.com/VladimirMarko/conaled/issues/8) covers the full
port, beyond the accepted #15 architectural milestone. The pinned target is
Felix `6f36d28097db7ea5f5df3263db3e8be08f74e490`. The
[source index](felix-full-correspondence-source-index.md) lists all 29 modules,
including modules outside `All.agda`, and 471 declaration, field, helper and
unfinished-proposal locators. The [baseline inventory](felix-parity.md) and
[implementation record](felix-parity-implementation.md) remain historical records.

## Current implementation and acceptance status

The full pinned programme was accepted at
[`a61fb186`](https://github.com/VladimirMarko/conaled/commit/a61fb186cf5c83a6f24fa34a947980215d369de7),
which is an ancestor of the current `master`. The
[final #8 acceptance record](https://github.com/VladimirMarko/conaled/issues/8#issuecomment-6769709817)
records completion of #449–#457 and independent full-programme Standards and
Spec reviews with no unresolved findings. Issue #8 is closed.

That accepted candidate passed all 2,431 modules, the exhaustive audit using
only `propext`, `Classical.choice` and `Quot.sound`, and exact-candidate
verification. Source validation checked module coverage, pinned blob hashes,
locator bounds and local links. These are the recorded historical acceptance
results, not a new build performed for this documentation reconciliation.
The earlier `22900e54`, `230f56f9` and `7452a19d` checkpoints remain part of the
implementation history; their pending-review status is superseded by the final
acceptance.

The table and R1–R6 contracts below preserve the original `65e2d67` assessment.
Their missing/future-work labels describe that baseline, not the current
implementation. The following mapping and implementation addenda supersede
those labels, while retaining their hypotheses and full source scope.

| Pinned declaration families | Current recovery and boundaries |
|---|---|
| Object; Raw; Function Type/Raw/Laws | [#449](initial-and-right-distribution.md) adds initial arrows and both distributions; [#450](raw-felix-constructions.md) supplies equality transport, codiagonal and derived operations. [#451](selected-admissible-feedback.md) supplies selected function feedback, without adding trace axioms. |
| Equiv; Laws; Reasoning; Homomorphism; MakeLawful | [#450](raw-felix-constructions.md) supplies the checked derived-equation recovery over existing semantic relations. [#453](computational-equivalence-witnesses.md) adds computational equivalence and category witnesses; [#455](computational-structural-witnesses.md) adds the structural laws, derived reasoning, preservation and transport. Existing #37/#333 contracts remain available. |
| Product; Squared; Monoid; Identity | [#450](raw-felix-constructions.md) supplies raw representatives and semantic laws; [#456](computational-construction-witnesses.md) supplies retained component/induced relations, laws and preservation, reusing #455 identity interfaces. Selected product feedback is in #451. |
| Prop; Object/Morphism subcategories; Pred | [#452](restrictions-predicates-setoids.md) supplies arbitrary object reindexing, Type-valued admissibility and exact PRED with total underlying functions. [#456](computational-construction-witnesses.md) adds computational relations, laws and preservation over the existing raw subcategory constructions. Admissibility and equivalence witnesses remain separate data. |
| Comma Type/Raw/Homomorphism/Vertical; Arrow | [#450](raw-felix-constructions.md) supplies semantic recovery and [#453](computational-equivalence-witnesses.md) the retained-square prototype. [#456](computational-construction-witnesses.md) extends this to component relations, category/Cartesian structures and laws, projections, preservation, compatible-middle vertical composition and Arrow specialization. |
| Setoids | [#452](restrictions-predicates-setoids.md) remains the Prop-valued specialization. [#457](computational-relation-setoids.md) supplies Type-valued element relations and retained congruence functions, pointwise arrow witnesses and structural instances. Its closed structure uses the common universe of the pinned source; other supported structures retain independent carrier/relation universes. The unfinished trace proposal has the #451 counterexample and corrected sufficient assumptions. |
| Function Lift; CAT | [#450](raw-felix-constructions.md) supplies independent-level lifting and raw Quiv/Prefunctor recovery. Cartesian preservation includes terminal and binary-product preservation. Arbitrary quivers acquire no unsupported category laws. |
| All; Comma facade; Function facade | Re-export modules add no further mathematical constructions. Their nested modules and modules outside All remain included in the source index. |
| Monoidal factoring; commented Boolean proposals; maintenance TODOs | [#454](monoidal-and-boolean-disposition.md) supplies tensor factoring, Mathlib correspondence, Cartesian recovery and a noncartesian consumer, plus a precise mathematical disposition of all seven proposed Boolean operations. The maintenance disposition below introduces no extra mathematical theorem. |

The computational layer retains selected Type-valued witnesses without
assuming uniqueness, involutive symmetry, associative witness transitivity or
higher coherence. Its explicit erasure adapters recover the existing
Prop-valued APIs; they do not recover arbitrary witnesses from erasure.
The #456 examples distinguish component and square witnesses and demonstrate
why double transposition need not return the original square witness.

Independent full-programme review at `230f56f9` found two residuals, recorded
as `8-FULL-STD-1`/`8-FULL-SPEC-1` (generic computational structural and
construction families) and `8-FULL-STD-2`/`8-FULL-SPEC-2` (general computational
setoids). The final independent full-programme reviews at `a61fb186`
explicitly resolved all four findings using #455–#457, reusing unchanged child
assessments and reviewing the residual implementations and final correspondence.
The bounded #453 prototype remains accepted under its original contract.

Final acceptance covered the original full #8 criteria, including every
indexed source item and its checked counterpart or precise mathematical
resolution, source locators and links, and preserved exact, relational and
dependent application contracts. The final review, rather than a child pass
or source locator alone, supplies programme acceptance. #25's comparison and
#109's broader recursion work have separate scope; this ledger does not reopen
#25 or the completed #266, #302/#307 and #309 contracts.

## R1 implementation update

[#449](https://github.com/VladimirMarko/conaled/issues/449) now supplies the
initial-object and right-distribution interfaces described in R1. The
[implementation report](initial-and-right-distribution.md) maps the new
operations, transport, quotient and Mathlib adapters to source fields, with
checked empty-carrier, raw-code, nonidentity-comparison and composed consumers.
The module table below retains the original `65e2d67` assessment; references to
R1 in those rows are resolved by this addendum. R2–R6 have the implementation
addenda below. The accepted #37/#333 results retain their contracts. #449
passed independent review and was included in the accepted `230f56f9` integration.

## Reading the historical dispositions

- **Covered** means the named local declarations implement the stated portion
  under the assumptions recorded below. It does not override a stated
  proof-relevance or universe restriction.
- **Specialization** means a checked narrower construction exists; its stronger
  assumptions or smaller universe range prevent a full correspondence claim.
- **Mathlib correspondence** identifies an inspected construction and the exact
  translation. A remaining raw adapter or checked recovery is stated explicitly.
- **Missing interface** means the inspected local category interfaces do not
  expose the specified generic contract. It does not mean no theorem elsewhere
  in the repository could help prove it.
- **Unresolved mathematics** means an upstream proposal lacks the hypotheses
  or laws needed for the proposed construction. The residual task must settle
  those before claiming an implementation.

Declaration families in each row include the named record's fields and derived
operations. The source index provides the individual locations. A family with
mixed coverage is split below; no blanket module-level coverage is inferred
from one successful instance.

## Baseline universes, witnesses and validation

[CategoryOps](../../SquareKit/Category.lean) separates `Obj : Type u` and
`Hom : Obj → Obj → Type v`. This matches Felix's independent object/hom levels
up to the usual Agda `Set`/Lean `Type` translation. But Felix `Equivalent q`
has a **`Set q`-valued relation**, whereas `HomEquiv.homSetoid` has a
**`Prop`-valued relation**. Its equivalence witnesses are therefore erased.
At `65e2d67`, coverage of generic equivalence, congruence, law transport and
commuting squares was limited to that proof-erased specialization. The current
#453/#455/#456/#457 layer supplies separate computational counterparts as
mapped above; the old `HomEquiv` APIs intentionally retain their Prop contract. This does not reopen #15,
#37 or #333, whose accepted contracts are the existing Lean interfaces.

A second, independent distinction concerns data stored in arrows. Felix's
morphism restrictions and predicates can store `Set m`-valued evidence while
ignoring it in arrow equivalence. That can be ported with `Type`-valued evidence
and a `Prop` equivalence on underlying arrows; it need not await an enriched
hom-equivalence theory. By contrast, an `Exists` in Lean `Prop` cannot supply an
executable selected witness without changing the contract.

The baseline declaration statements and consumers were inspected at `65e2d67`. Their earlier acceptance provenance is the [#15 record](felix-parity-implementation.md#validation-and-completion-gate),
[#37 addendum](felix-parity-implementation.md#closed-law-transport-37),
[#333 report](optional-law-transport.md), and the
[orchestration acceptance record](https://github.com/VladimirMarko/conaled/issues/235#issuecomment-6759580709).
The last records 2,357 integrated modules and the exhaustive audit at this
checkpoint. This research change has source, locator and local-link checks;
it does not claim another Lean build or an Agda replay.

The product and cancellation declarations below are defined in
[CartesianMap.lean](../../SquareKit/CartesianMap.lean); the `Comma` product
declarations are in [CommaProducts.lean](../../SquareKit/CommaProducts.lean).

## Historical module correspondence at 65e2d67

| Pinned module | Construction, local correspondence and residual disposition |
|---|---|
| `All.agda` | Re-export index. The source inventory also includes `Construct/Monoid`, `Instances/CAT` and nested implementation files; explicit imports alone are not the coverage boundary. No runtime example is defined here. |
| `Object.agda` | `Products` maps to the object fields of `TerminalOps` and `ProductOps`; `Exponentials` to `ClosedOps.exp`. `Coproducts._⊎_` maps to `CoproductOps.sum`; its `⊥` is a missing generic raw initial-object field, R1. Splitting object choices from operations is an encoding difference, not a theorem. |
| `Raw.agda` | `Category` maps to `CategoryOps`; `sub`/`sub≡` are equality transport of `ident`; R2 owns their checked recovery. Cartesian primitive operations map to terminal/product fields. Closure maps to `ClosedOps`, including `uncurry`. Binary coproducts and left distribution map to `Optional`; R2 owns checked recovery of `jam` as `copair ident ident`; initial arrows, the separately selected right inverse and derived cartesian convenience operations require R1/R2. `Traced.WF/trace` is missing as a generic selected-witness interface, R3. |
| `Equiv.agda` | `Equivalent`, setoid reasoning and `H-equiv` map to `HomEquiv`, its `refl/symm/trans`, and `RawMap.induced`, subject to the witness restriction above. `Homomorphismₒ`/`Homomorphism`, identity/composition map to `RawMap.obj/map/id/comp`. Pairing maps into a raw product category needs R2. Local `toFunctor/ofFunctor` preserve the equality-lawful case. |
| `Laws.agda` | Category axioms/congruence map to `CategoryLaws`/`CategoryCongr`; terminal uniqueness and product beta/eta/congruence to `TerminalLaws`, `ProductLaws`, `ProductCongr`. `ProductLaws.hom_ext` and `ProductLaws.pair_comp` supply product uniqueness and pairing composition. Binary coproduct beta/eta/congruence, left distribution inverse laws and closed beta/eta/congruence are covered by `Optional`. Initial uniqueness and right distribution remain R1. The complete derived tensor/unit/swap/associator equation family has no source-by-source checked recovery table; R2 must supply it, without claiming that its elementary equations are mathematically unknown. |
| `Reasoning.agda` | Equivalence chains and category reassociation use `HomEquiv` and `CategoryLaws`; `CategoryLaws.cancel_left/cancel_middle` and `Comparison.comp_laws` cover reusable inverse cancellation. Felix's fixed-length reassociation, tensor-inverse, associator, transpose and conjugation lemmas are a larger API. Existing specific matrix permutations and exact-square lemmas are specializations. R2 owns the full checked derived-equation recovery rather than inferring it from names. |
| `Homomorphism.agda` | `CategoryH`, identity and both composition spellings map to `MapLaws`, `RawMap.id_laws/comp_laws`; `ProductsH` and `StrongProductsH` to `TerminalMap`/`ProductMap` plus `ComparisonLaws`; `CartesianH` to their preservation fields. `CartesianMap` implements identity/composition and inverse comparisons. The long `F-assoc` and `F-⊗` derived family still needs checked source equation recovery in R2. `CoproductsH`/`CocartesianH` binary fields are covered by `CoproductMap`; initial comparisons are R1. `ExponentialsH` and the closed-preservation TODO are covered by `ClosedMap` (#37), not arbitrary comma closedness. |
| `MakeLawful.agda` | `LawfulCategoryᶠ` and `LawfulCartesianᶠ` map to `RawMap.transportLaws`, `TerminalMap.transportLaws` and `ProductMap.transportLaws`. Induced equivalence supplies reflection; an independently selected relation requires explicit reflection. Closed transport TODO is completed by #37. #333 extends this to binary coproduct/distribution; initial and right-distribution additions are R1, not a reopening of #333. |
| `Prop.agda` | `Categoryᴾ` and `Cartesianᴾ` are closure operations on `M f : Set m`, not assertions that arbitrary morphism predicates are closed. Tracked assembly maps are a specialization with existential tracking evidence in `Prop`; they do not supply this arbitrary `Type`-valued closure interface. R4. Commented `Logicᴾ` depends on an absent Boolean-operation package, R6. |
| `Subcategory/Object.agda` | Reindex by any `J → Obj`; injectivity is not required. Mathlib `InducedCategory D F` has exactly wrapped arrows `F X ⟶ F Y`, `homEquiv` and `inducedFunctor`, but assumes a lawful ambient category and does not recover raw representatives with nontrivial equivalence. Raw product/sum comparisons and trace conjugation are R4/R3. Existing dependent interpretations do not automatically supply this interface. |
| `Subcategory/Morphism.agda` | Arrows are `(f, sat : M f)`; induced equivalence forgets `sat`. Identity/composition require `Categoryᴾ`; products require `Cartesianᴾ`. Law transport through the forgetful map is already reusable. `Assembly.Hom`/`Hom.comp` and `Assembly.prod/pair` are checked specific consumers, not an arbitrary witness-retaining restriction. R4. |
| `Construct/Product.agda` | Objects and arrows are componentwise pairs at max universes; operations, equivalence, laws and both projections are componentwise. Mathlib `CategoryTheory.prod`, `Prod.fst/snd`, `Functor.prod'` cover the equality-lawful category case. Raw componentwise equivalence, comparisons and selected trace witnesses need R2/R3; no quotient should replace raw pairs. Commented Boolean families are R6. |
| `Construct/Squared.agda` | `unsquare` sends `(A,B)` to `A×B` and `(f,g)` to `f⊗g`. Its strong comparison is the middle-four transpose, not identity; it also exposes both componentwise and interpretation-induced equivalences. `MatrixDoubling` is a nonidentity-comparison specialization, not this arbitrary construction. R2 must recover the two equivalence choices and the induced-law theorem. |
| `Construct/Monoid.agda` | Unit objects and monoid elements as arrows; composition `g ∘ f = g ∙ f`; equivalence is the monoid's relation. Mathlib `SingleObj.categoryStruct/category`, `toEnd`, `mapHom` cover equality-lawful monoids. A setoid monoid cannot be replaced by its quotient while claiming retained raw representatives. Raw setoid correspondence and a noncommutative multiplication-order example belong to R2. |
| `Construct/Arrow.agda` | Identity/identity comma objects/arrows are covered by specializing `Comma` with `RawMap.id`; the Type instance has explicit round trips in `Comma.Exact`. Arbitrary raw arrow transposition, object composition, `Id` and `idᵀ` do not yet have that checked recovery package, R2. Vertical composition is covered by `Comma.vertical`; the upstream generalization TODO is stale beside `Comma/Vertical`. Local compatibility is weaker target equivalence, not equality of middle representatives. |
| `Construct/Comma.agda` | Re-exports Type/Raw/Homomorphism; semantic counterpart is the local `Comma` module family. No additional construction should be commissioned just to mirror the facade. |
| `Construct/Comma/Type.agda` | `Obj`, `_↬_`, `_⇉_`, both projections, paired projection and induced component equivalence map to `Comma.Obj/Hom/equiv/fst/snd`. Local commuting evidence is `Prop`, with independent source/target universes. Pairing projections into a raw product package remains R2. Checked exact and non-function matrix consumers are in `Examples.CommaSquares` and `Examples.MatrixCompilerPreservation`. |
| `Construct/Comma/Raw.agda` | `id′/comp/category`, `products/!′/fork/exl′/exr′/cartesian` map to `Comma.ident/comp/ops` and `Comma.terminalOps/productOps/first/second/fork`. Construction requires target laws and preservation, not source category laws; product construction uses strong comparisons. Local source laws enter only law proofs. The commented logic experiment is R6. |
| `Construct/Comma/Homomorphism.agda` | Both `categoryH` projections are covered by `Comma.fst_laws/snd_laws`. Composition is consumed in `Examples.CommaSquares.semantic_projection_laws`. |
| `Construct/Comma/Vertical.agda` | `_◎_` maps to `Comma.vertical`, with stronger local coverage: equivalence of interpreted middle arrows suffices. `Comma.Exact.ofRep_after/ofSquare_vertical` and `Examples.CommaAgreement.vertical_output` retain concrete recovery. |
| `Instances/Function.agda` | Re-export facade; covered portions and residuals are those of Type/Raw/Laws below. |
| `Instances/Function/Type.agda` | Same-universe functions, unit/product/sum/exponential objects map to `FunctionCategory.ops/terminal/products` and optional operations for any carrier universe `u`. Empty object requires the R1 package. `tt` is a constructor-pattern convenience. |
| `Instances/Function/Raw.agda` | Function category, cartesian, binary coproduct, left-distribution and closed operations are covered by `FunctionCategory`/`FunctionOptional`; extensional equivalence corresponds to Lean function equality using `funext`. Initial/right-distribution are R1. `traced` returns the selected `y` from each input's `(y,z,f(x,z)=(y,z))`; it is R3, with no trace axioms upstream. |
| `Instances/Function/Laws.agda` | Category/cartesian/closed/binary coproduct/left-distribution laws are covered by `FunctionCategory`, `FunctionOptional`, `FunctionOptionalLaws`. The missing initial/right-distribution packages require R1. No traced-law instance is supplied here. |
| `Instances/Function/Lift.agda` | `lift₀′/lift₀/lift₁/lift₂′/lift₂` are lifted values/unary/binary functions. `Examples.FullSourceNaturality.Lift` supplies map, inverse comparisons, preservation and composed full-source consumers, but its map is explicitly `ops.{0} → ops.{0}`. This is a specialization, not the upstream two-independent-level lift. Mathlib `ULift` and `ULift.upFunctor` help, but the generic raw comparison/recovery must be checked in R2. |
| `Instances/Identity.agda` | `Hₒ/H/catH/pH/spH/cartH` map to `RawMap.id/id_laws`, terminal/product identity comparisons and their laws. These are covered under the common proof-erased equivalence restriction. Commented Boolean instances are R6. |
| `Instances/Pred.agda` | Objects contain a carrier `Set m` and a predicate into `Set ℓm`; arrows contain a total underlying function and a dependent witness map. Equivalence compares the underlying function on **all** carrier inputs. Relational/witness and assembly models are specializations with different admissibility/observation conditions. Products, coproducts, forgetful maps and inherited laws require an explicit R4 recovery; a subtype category would lose behavior on inputs without witnesses. |
| `Instances/Setoids.agda` | Objects `Setoid ℓ ℓ`, congruent functions, pointwise target-setoid equivalence, products/sums/exponentials, both distributions and laws. Lean's `Setoid` alone is not a category of these raw congruent functions. `HomQuotient` quotients arrows, and neither it nor assembly closure proves this correspondence. R4 owns the proof-erased-setoid implementation/recovery; R5 owns arbitrary relation witnesses. The commented trace fails to supply congruence of selected outputs, R3. |
| `Instances/CAT.agda` | `CAT` stores only objects and homs, not identity/composition/laws. `_⤇_` is object/hom data. Mathlib `Quiv` and `Prefunctor` match this data at fixed object/hom levels; `Cat` imposes extra structure. `toHₒ/toH/it-⤇` correspond to projecting/assembling `RawMap` only after raw operations are separately supplied. Quiver terminal/product recovery and bridges are R2. The experimental `Functor`/`CartesianFunctor` obligations correspond to `MapLaws` and structural preservation; their composition is already supplied locally. |

## Original residual contracts and order

These contracts were published as #449–#454 after the baseline inventory.
They are retained here to preserve the full requirements and the distinction
between the bounded #453 prototype and the later #455–#457 recovery. Every
formal package needs checked specializations, statement review, integration
build/audit and independent Standards/Spec review. Preserve existing raw APIs;
reuse Mathlib for lawful interoperability. The declaration index is the
acceptance checklist, not an instruction to duplicate Agda spelling.

### R1. Initial arrows and both distributions

Add independently selectable initial-object operations, uniqueness laws,
comparisons, preservation and law transport, including lawful quotient and
Mathlib initial-object correspondence. Derive a right-distribution inverse from
left distribution and cartesian symmetry, prove its two inverse laws and
preservation, and distinguish this derived choice from Felix's independently
selected raw right inverse. Recover the independent choice under its inverse
laws by uniqueness. Do not require distribution for initial-arrow clients.

Consumers: functions including the empty carrier, a raw syntax with semantic
rather than constructor equality, and a nonidentity object comparison. Check
both sum tags and composed interpretations. This extends #333 without changing
its accepted binary-sum or left-distribution contract. No prerequisite from
#445–#447 is needed.

### R2. Raw constructions and derived-equation recovery

Provide raw product categories, projections/pairing, squared `unsquare` with
middle-four comparison, arbitrary arrow-category transpose/identity embedding,
raw setoid monoid construction and fixed-universe CAT/Quiv correspondence.
Generalize the lift consumer to independently raised universes. Reuse existing
comma, map and comparison infrastructure; keep componentwise and
interpretation-induced equivalences separately selectable.

Recover `Raw.Category.sub/sub≡` by equality transport, including the reflexive
case and equivalence of the transported identity. Recover `Raw.Cocartesian.jam`
as `copair ident ident`, with its exact operation-only assumptions. Include
Arrow object composition with the pinned source's compatible middle object,
and state that compatibility separately from the equivalence condition used
by local vertical composition. Check object composition, transpose and identity
embedding together on a nonidentity arrow example.

For each remaining declaration in `Raw.Cartesian`, `Laws`' derived Cartesian
section, `Reasoning` and `Homomorphism`'s derived preservation section, supply a
checked equation using existing lemmas or a shared new lemma, with its exact
premises. That closes the current recovery-evidence gap; merely citing
cartesian category theory is insufficient. Separate generic monoidal factoring
(R6) from completing cartesian-derived operations.

Consumers: product of raw code and finite matrices; squared products with a
nonidentity shuffle; a noncommutative monoid with explicit composition order;
identity/identity comma transpose and vertical recovery; `ULift` across two
universe levels. Reuse equality-lawful Mathlib products, `SingleObj` and `Quiv`
via checked adapters. Do not infer categorical laws for arbitrary `Quiv` objects.

### R3. Selected admissible feedback and the setoid obstruction

Expose `WF f : Type w` and `trace f : WF f → Hom A B` independently of trace
axioms. Implement the exact function witness `(x : A) → Σ y : B, Σ z : S,
f (x,z) = (y,z)`, componentwise product witnesses, and object-reindexing
conjugation through explicit product comparisons. Retain witness selection.

Discriminating example: `f : Unit × Bool → Bool × Bool` with
`f (_,s) = (s,s)` admits constant-false and constant-true witnesses, yielding
different outputs. Thus witness independence is not available from existence.
For setoids, arbitrary pointwise selected fixed points need not give a
congruent output map: take a two-element input with universal relation and the
same feedback body, with outputs and state in discrete Bool. Select the state by the input; the body is congruent but selected
outputs differ on equivalent inputs. Formalize this control and a corrected
sufficient condition (explicit congruence of selected outputs, or suitable
uniqueness modulo output equivalence). Do not silently add uniqueness to the
raw function interface.

Connect guarded-stream solutions only where `solve_fixed/unique` establish the
required witness and independence. Initialized delayed feedback solves its
specified stream recurrence, not every unguarded pointwise equation. There is
no upstream traced-law record to port; any naturality, sliding, vanishing or
yanking extension needs stated admissibility/selection hypotheses.

### R4. Witness-retaining restrictions, predicates and setoids

Construct object reindexing along arbitrary `J → Obj` and morphism restriction
with `M f : Type w`, closed under the operations requested by each client.
Lift equivalence through the forgetful map, retaining `sat` as data while
ignoring it in that equivalence. Instantiate with two different witnesses for
the same arrow. Connect the equality-lawful object case to `InducedCategory`
without imposing injectivity.

For object reindexing, construct raw terminal/product operations by conjugating
through selected product comparisons, and initial/coproduct operations through
independently selected coproduct comparisons. These raw operations must not
require inverse laws. State and prove the stronger comparison and preservation
hypotheses needed for Cartesian law recovery, and the corresponding coproduct
law recovery. Use a noninjective object map and selected nonidentity comparisons
to distinguish this construction from mere renaming. R1 supplies initial-object
packaging; R2 supplies any shared raw-construction recovery helpers. The
object-reindexed trace client remains R3's responsibility.

Recover Felix PRED with arbitrary carrier and predicate universes, including
behavior on inputs where the predicate has no inhabitant, products/sums and
forgetful preservation. Compare existing `RelationalCategory` and
`Assembly.Hom` by explicit maps with their actual contracts; neither requires
replacement. Construct the proof-erased relation specialization of the setoid
instance with congruent functions, pointwise hom equivalence, product/sum/closed
operations and both distributions. A nontrivial setoid relation must distinguish
pointwise relation from literal equality of functions. R1 supplies initial and
right-distribution packaging; R3 owns selected trace congruence.

### R5. Computational equivalence witnesses

Determine and implement the retained-witness counterpart of `Equivalent q`
without weakening `HomEquiv`'s existing quotient interface. Start with a
one-object example carrying distinguishable relation witnesses and explicitly
state what laws the witness operations satisfy. Felix asks for reflexivity,
symmetry and transitivity operations, not higher coherence or uniqueness.
Either expose that general witness interface and recover the existing
proof-erased specialization, or record a precise mathematical resolution of
which information an approved replacement retains and loses. A `Prop` squash
cannot count as witness recovery. Coordinate with #36/#235's higher-identity
work; their existence alone is not a correspondence proof.

This is a design and checked-prototype task before a broad retrofit. Its result
must state which comma/law-transport signatures can retain the witnesses, and
which intentionally erased lawful adapters remain separate. Do not reopen the
accepted proof-erased results.

### R6. Unfinished factoring and Boolean proposals

Resolve the proposed monoidal/braided factoring by identifying operations that
need only tensor/unit/associativity/braiding and those that require copying,
discarding or cartesian universal properties. Compare Mathlib's lawful
`MonoidalCategory`/`BraidedCategory` with a raw-equivalence contract before
adding an interface. Require a noncartesian consumer and checked recovery of
the cartesian instances; factoring solely to mirror filenames is insufficient.

The commented Boolean families in `Prop`, product, comma and identity modules
are unfinished proposals, not active proofs. Inventory their `false`, `true`,
`not`, conjunction, disjunction, xor and conditional equations; define necessary
object/operation preservation and closure hypotheses, then implement or give a
precise mathematical disposition. Generic Boolean-valued syntax already in
other internal languages does not prove these raw categorical contracts.
No Boolean package should become a prerequisite for category/product clients.

## Maintenance TODO disposition

The source index retains every explicit TODO and nearby unfinished trace or
logic proposal. Moving definitions between modules, infix spelling, argument
explicitness, replacing aliases by instances, factoring module parameters and
choosing shorter proofs are upstream maintenance proposals. They impose no
additional mathematical theorem; local namespace and explicit-record choices
already avoid dependence on Agda instance resolution. `Laws`' suggestion to
generalize functions from level zero is superseded upstream by
`Function.Type (ℓ : Level)` and locally by `FunctionCategory.ops.{u}`; the separate
cross-universe lift is recovered by #450. Arrow vertical generalization is already
implemented upstream and locally. Closed preservation/transport is #37.
The monoidal and commented Boolean proposals have the #454 disposition;
the selected-setoid-trace obstruction and correction are recorded in #451.

## Source and link verification

The upstream checkout was fetched read-only and fixed to the pin, not current
HEAD. The companion inventory was compared with `git ls-tree` for all 29
modules; its SHA-256 hashes identify each complete source blob, and every
listed source line is within that blob. Local Markdown file links were checked
for existence. Mathlib sources were inspected at the repository's pinned
`56a005855ea17e0b0958f73ec801ae140b0a1679`; relevant primary sources are:

- [Product categories](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Products/Basic.lean), including raw `CategoryStruct` and lawful `Category` instances.
- [Induced categories](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/InducedCategory.lean), with no injectivity premise on the object map.
- [One-object categories](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/SingleObj.lean), whose categorical composition reverses argument order relative to the multiplication notation as required by Felix.
- [Bundled quivers](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Category/Quiv.lean), with prefunctors as arrows.
- [Universe-lift categories](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Category/ULift.lean), distinct from automatically supplying raw function product comparisons.

A declaration locator is not a proof of equivalence between implementations.
The implementation reports above now supply R2's per-equation recovery and
the computational witness counterparts beyond the bounded R5 prototype. The
final independent reviews at `a61fb186` accepted these mappings against the
indexed programme. This documentation reconciliation records that acceptance;
it supplies no new formal validation or independent certification.

## R2 implementation addendum (#450)

The [raw-construction recovery report](raw-felix-constructions.md) records the
operation-only products, squared interpretation, arbitrary arrows, setoid
monoids, fixed-universe Quiv, independent-level ULift, and per-declaration
Cartesian/reasoning/preservation recovery. It preserves the original inventory
as a historical assessment. #450 passed independent Standards and Spec review
and is included in the accepted `230f56f9` integration.

## Selected feedback recovery (#451)

The [selected-feedback record](selected-admissible-feedback.md) maps the raw,
function, product and object-reindexing declarations to checked Lean APIs. Its
setoid counterexample explains the unfinished source congruence obligation;
explicit selected-output congruence and output uniqueness give sufficient
repairs. The guarded-stream connection proves independence only under actual
guardedness. #451 passed independent review and is included in `230f56f9`;
its selected-feedback contract does not assert arbitrary trace laws.

## Computational equivalence recovery (#453)

The [witness-equivalence design](computational-equivalence-witnesses.md)
recovers `Equivalent q` and induced relations with computational witnesses.
The checked comma prototype and law transport retain witnesses; explicit
erasure recovers the existing proposition-valued adapters. Distinct Boolean
witnesses and nonassociative transitivity delimit the contract. The bounded
#453 package passed independent review and is included in `230f56f9`.
#455–#457 supply the later ordinary computational families; higher coherence
is not an upstream assumption or a condition of this correspondence.

## Tensor and Boolean disposition (#454)

The [factoring record](monoidal-and-boolean-disposition.md) separates raw tensor
operations and semantic bifunctor laws from copying/discarding. It includes
Mathlib adapters, generic cartesian recovery and a checked noncartesian resource
consumer. The commented Boolean families receive an explicit operation,
closure and preservation contract with the required conditional naturality;
this is a mathematical disposition, not a claim of checked generic Boolean
instances. #454 passed independent review and is included in `230f56f9`.

## R4 implementation addendum (#452)

The [restrictions, predicates and setoids report](restrictions-predicates-setoids.md)
records declaration-level recovery for both subcategory constructions, exact
Type-valued PRED, and the proof-erased setoid instance. It includes the explicit
RelationalCategory/Assembly comparisons and discriminating checked consumers.
The historical inventory is preserved. #452 passed independent review and
completed the accepted `230f56f9` integration. Its completed resumed validation
run, rather than the earlier interrupted run, supplies acceptance evidence.


## Computational structural-law recovery (#455)

[Computational structural witnesses](computational-structural-witnesses.md)
maps every active pinned declaration in `Laws.agda`, `Homomorphism.agda` and
`MakeLawful.agda` to selected witness-producing APIs. The package includes
native preservation squares, comparison inverse witnesses, derived Cartesian
equations, universal-property adapters and target-law transport. Explicit
erasure recovers the unchanged semantic APIs. Distinct reflection choices and
nonidentity comparisons are checked in `Examples/WitnessStructure.lean`.
This extends #453's category-only prototype. #455 passed independent review
at `b429abf5` and combined review with #457 at `7452a19d`; the repaired public
entrypoint is included. The final #8 reviews at `a61fb186` accepted this package
together with the #456 constructions and resolved the structural-law findings.

## Computational constructions (#456)

The [construction witness correspondence](computational-construction-witnesses.md)
accounts for every indexed active Product, Squared, Monoid, Comma, Arrow,
Identity and subcategory declaration at the pinned revision. It extends the
separate computational layer with structural laws, selected preservation,
induced-law transport and explicit erased recovery. Component relations and
square witnesses remain distinguishable. The checked non-involutive transpose
example prevents importing proof-irrelevant square equality into this layer.
The existing selected-feedback constructions are reused with their #451
congruence boundary. The implementation at `22900e54` passed its full build
and exhaustive audit. The final acceptance at `a61fb186` records the completed
independent reviews and resolves the full-programme construction findings.

## Computational relation setoids (#457)

The [computational instance](computational-relation-setoids.md) retains Type-valued
relation and congruence witnesses from the pinned Setoids module. It supplies
all active raw structures, selected universal-property operations and law
packages, with explicit erasure comparisons into the existing Prop-valued
instance. Multiple-witness examples inspect composition, curry and both
distributions. #457 passed independent review at `9da00495` and combined
review with #455 at `7452a19d`. The final full-programme reviews at `a61fb186`
also explicitly resolved the original setoid findings.
