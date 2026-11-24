# #571: implementation and use assessment

Recommend retaining direct indexed interfaces and investigating a small derived layer for the specified Künneth map and its transport. Keep higher correspondences as a distinct, testable extension. The existing span implementation already derives ordinary coherence and retains dependent selections. A replacement must recover these clients and also demonstrate an observation unavailable in ordinary categories. Concise correspondence notation alone does not decide the comparison.

This assessment uses repository base `b202bc865dc3aaf135e117b647bef23bf3b269fa`, Lean 4.35.0, and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. All repository paths below refer to that base. I read the brief, specification, repository guidance, source report, actual declarations and clients. I had no prior involvement in the implementations and did not read the other #571 assessments. Before saving this report I sent the coordinator one progress message stating the projection/coherence finding and the distinction between arbitrary apex maps and Scholze's correspondence groupoid. I received no conclusions from another assessor. This early outgoing message is a departure from the brief's save-before-coordination rule; the initial analysis was otherwise independent.

## Contracts and source boundary

The contracts are those of `docs/research/six-functor-reusable-argument.md`, not an unspecified six-operation record:

- **K:** for proper `f:X→S`, `g:Y→S`, chosen pullback `W` with projections `p,q`, construct the specified isomorphism `f_* A ⊗ g_* B ≅ h_* (p* A ⊗ q* B)`, `h=f p`, from canonical PF, canonical BC, symmetry, and induced composition of right adjoints. Its transpose is the specified tensor of counits (E).
- **H:** for admissible `f:X→S`, construct `Hom_S(f_! A,B) ≅ f_* Hom_X(A,f^! B)` by the natural chain of Hom-set adjunctions. This requires closed fibers, both adjunctions and exceptional PF. It does not follow from K.
- **T:** preserve the specified K map, with its endpoint comparisons: `ρ ∘ F_S(K) ∘ λ⁻¹ = K'`. Existence of an isomorphism between endpoints or a second independent model proves less.

I checked the primary definitions. Scholze's geometric setup and Definitions 2.3–2.5 supply a lax symmetric monoidal correspondence functor, with right adjoints added for the six-operation version. Definition/Proposition 3.2 describes coherent simplices using cartesian grids. Lecture I provides the proper sheaf calculation. These are mathematical constructions/contracts, not implementations supplied by the local `SpanAction`. [Scholze, October 2025, printed pp. 6–8, 16–18](https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf).

Cisinski–Déglise's Examples 1.4.3 and 2.4.48 include `SH` over noetherian schemes of finite dimension. Theorem 2.4.50 supplies exceptional adjunctions for separated finite-type maps, proper comparison, BC and the PF/Hom formulas. Sections 1.1.15–16 and 1.1.31–32 construct exchanges by adjunction and discuss composition compatibility. They support the paper benchmarks; none constructs `SH` in this repository. [CD, arXiv v4, printed pp. 8–12, 28, 77–79](https://arxiv.org/pdf/0912.2110v4).

For the full correspondence comparison use arbitrary left legs and right legs in `E`, with isomorphisms, composition, pullback and diagonals in `E`, and finite limits in the base. The diagonals condition is explicit in Scholze's Lecture III setup; the preceding statement of Definition 2.3 lists the other closure conditions. For K alone use proper `P`, closed under identities, composition and pullback. Do not transfer full-correspondence hypotheses to ordinary slice clients.

## Inspected native interfaces and actual obligations

| Interface | Builder inputs and constructed result | Consequence for reuse |
|---|---|---|
| `SquareKit/DependentBaseChange.lean` | `C : Type u`, `Category.{v} C`, `HasPullbacks C`, and `h : IsPullback f' g' g f`. `leftComparison` uses the universal pullback; `pullbackComparison` is its canonical mate. `pullbackInverse` proves invertibility by projection equations. | Cartesianness is consumed, not inferred from commutativity. The comparison retains value, argument and base projections. |
| Its `WithAdjunction` namespace | Supplied `Over.pullback f ⊣ R` and `Over.pullback f' ⊣ R'`. `mate_conjugate` identifies the twice-mated comparison with conjugation of the proved left isomorphism. This establishes `mate_isIso` in this specific construction. | This is not a general rule that mates preserve invertibility. `evaluation`, `evaluation_left`, `evaluation_comp`, `transpose_map`, and `curry_baseChange` let callers use actual coefficient maps and chosen counits. |
| `SquareKit/ExponentiablePullback.lean` | One supplied pullback/right-adjoint pair, pullbacks, and an actual square. Slicing and iterated-slice equivalences construct `squareRightAdjoint` and `squareAdjunction`. | The default dependent BC specialization constructs the changed right adjoint; callers need not supply arbitrary right adjoints for all maps or local cartesian closure. |
| `SquareKit/AdjointComparison.lean` | Two chosen right adjoints of the same left functor. `curry`, `uncurry`, and `mate` prove compatibility under canonical adjoint uniqueness. Independent object/hom universe pairs are allowed for four categories. | Comparing adjoint representations preserves the actual transposed map. An arbitrary isomorphism between carriers is not the contract. |
| `SquareKit/MixedBaseChange.lean` | Arbitrary `F:C⥤D` and pullbacks produce a natural comparison with both projection equations. Preservation of pullbacks supplies its inverse. Identity, composition, and context pasting are proved without needing adjoints. | Preserve the separation between a comparison and an invertible comparison. Do not demand finite-limit preservation merely to reuse these results. Its categories have independent object/hom universes. |
| `SquareKit/Internal/GeometricMorphism.lean` | A specified inverse/direct-image adjunction plus finite-limit preservation of inverse image. Morphisms are all natural transformations of inverse images. A `Lift` stores an actual invertible comparison; lift morphisms satisfy its commuting equation. | This is a useful stronger specialization, not the minimum interface for mixed BC or spans. It has no exceptional pushforward, motivic tensor, or all-six guarantee. |
| `SquareKit/IndexedSumFamilies.lean` and `Examples/IndexedWitnessAdjunctions.lean` | `Selected γ = Σ i:I γ, P γ i` in `Type u`, versus `Truth γ : Prop`. Native `first`, `twice`, and tagged adjoint results retain the selected dependent value. | Recovery must preserve the whole selected pair. The control `no_selection_reconstruction` disproves recovering every Boolean selection from inhabitedness. |

The imports matter: `DependentBaseChange` obtains exponentiable pullback stability from `ExponentiablePullback` and mates from Mathlib. Pinned Mathlib `Adjunction/Mates.lean` has `mateEquiv_vcomp`, `mateEquiv_hcomp`, and `mateEquiv_square`; any ordinary shared layer should use these. A field asking builders to re-prove their conclusions would duplicate obligations.

The Empty/Unit control in `Examples/IndexedWitnessAdjunctions.lean` gives a commuting square which is not a pullback and a noninvertible sum comparison. Its mate in an empty slice is invertible, while the inverse-mated comparison is not. This refutes the proposed automatic-invertibility shortcut at the exact interface boundary.

## Existing span action, three-span composition and interpretation

`SquareKit/SpanAction.lean` implements `X ←l W →r Y` as `Over.pullback l ⋙ Over.map r`. Both leg classes are `⊤`; the only base requirement is pullbacks. The source is Mathlib's ordinary bicategory of spans. An arbitrary apex map, including a noninvertible one, induces `actionMap`. `actionMap_value` preserves the whole payload and `actionMap_apex` applies exactly the supplied apex map.

`compositionIso` goes from the composite-span action to sequential action. Its inverse reconstructs the compatible pair of apex witnesses. `composition_value`, `composition_first`, and `composition_second` recover payload and both apices. `compositionIso_eq_beckChevalley` identifies the entire natural isomorphism with the assembly from `DependentBaseChange.leftComparison`, `Over.pullbackComp`, `Over.mapComp`, and functor associators. This is stronger than matching endpoints.

`pseudofunctor` derives left/right whiskering, associator and both unit compatibilities. Callers do not fill those proof fields. Source bicategory pentagon/triangle laws come from Mathlib's span construction; the action satisfies its pseudofunctor equations. This is a completed ordinary coherence construction, not higher coherence between arbitrary homotopies.

`Examples/SpanAction.lean` is discriminating rather than an identity-only exercise. Its spans are:

1. `Nat ← Nat×Bool → Nat`, retaining a Boolean branch and doubling the number.
2. `Nat ← Nat → Nat`, matching a doubled number and incrementing it.
3. `Nat ← Nat×Fin 2 → PUnit`, retaining another witness while forgetting the output base.

The selected input uses dependent payload `(3,3 : Fin 4)`, apices `(3,true)`, `3`, and `(4,1)`. Two actual compositors yield a sequential action, and separate equations recover all four selections. The pseudofunctor associator equation is evaluated on this input; both unit equations are specialized. A noninvertible apex map collapses the Boolean branches while preserving payload. An odd matching index fails. Merely preserving the final `PUnit` observation would miss all these distinctions.

`native_recovery`, `native_twice_recovery`, and `native_tagged_recovery` identify normalized span outputs with whole existing native `first`, `twice`, and tagged values. They require only the original Type-family data and substitutions. Native two-substitution recovery reindexes the first recovered result; it should not be misreported as a separate computation of all three span compositors. The other example supplies that associativity evidence.

`SquareKit/SpanInterpretation.lean` already implements #632. For pullback-preserving `F:C⥤D`, `span` and `map` retain the full image apex and apex maps. `compositionIso` is the actual `PreservesPullback.iso`. `pseudofunctor` derives its span coherence; `transformation` is a `Pseudofunctor.StrongTrans` with object components `Over.post F`, not assumed equivalences. `actionIso` agrees on its underlying arrow with `MixedBaseChange.comparison`. `action_value`, `action_apex`, `composition_transport`, and `beckChevalley_transport` preserve the specified comparison, including the image of the chosen composite apex.

The client composes `Over base → Over Bool → Type`. Its source representative has independently proved payload `(3,3 : Fin 4)` and apex `(3,true)`, and the successive comparison recovers the selected output. `Over.forget Bool` preserves pullbacks but not all finite limits, so replacing its hypothesis with left exactness would exclude a valid client. Conversely, inhabitedness truncation makes the images of incompatible constant-false and constant-true maps match. `comparison_not_surjective` and `truncation_not_preserving` show why arbitrary functors cannot use the invertible API.

`span_identity`, `span_composition`, `apex_composition`, `action_identity`, and `action_composition` are current component-level equations in the interpretation variable. #633 owns packaging them into identity/composite pseudofunctor comparisons and invertible modifications, including triple-interpretation coherence. #571 should reference these results and that residual, not reconstruct or declare #633 complete.

## Universes, dimensions and comparison costs

For direct ordinary models fix base `C : Type uB`, `[Category.{vB} C]`, fibers `D X : Type uF` with `[Category.{vF} (D X)]`. Fiber functors and natural transformations live in the ordinary functor categories; packaging targets `Cat.{vF,uF}`, whose bundled objects require the corresponding larger universe. The derived layer uses the same universes. Do not identify base and fiber sizes for convenience, and do not assert large derived/motivic categories are small in their object universe. A model involving localization still owes its size construction.

The native action has the exact specialized target `Cat.{v,max u v}` for base `C : Type u`, `[Category.{v} C]`; `Over X` has objects in `Type (max u v)` and morphisms in `Type v`. `SpanInterpretation` currently requires common `u,v` for source and target, unlike `MixedBaseChange`. This is a local API restriction, not a mathematical argument against universe-polymorphic interpretations.

A concrete candidate for higher study must name its representation. For example, a simplicial presentation could place base and fiber simplices in `Type uB` and `Type uF`, with a surrounding universe strictly large enough for the categories of these objects. A finite bicategorical prototype can instead expose object, 1-cell and 2-cell universes `u0,u1,u2`. Neither annotation constructs `Cat∞`, an infinity-category model, or an infinite coherent functor. No exact implemented higher-universe signature exists in the inspected span modules; the proposed finite signature is a new experiment's contract.

| Dimension | Direct ordinary indexed / derived layer | Higher correspondence target |
|---|---|---|
| Objects and coefficients | Actual base objects and fiber objects, with dependent selection in native clients. | Objects and coefficients with their specified higher identity structure. |
| Arrows | Functors/operations; coefficient morphisms retained as data. | Correspondence operations and functors with higher mapping spaces. |
| Comparison cells | Natural transformations and natural isomorphisms are data, including inverse maps. Ordinary span apex maps need not be invertible. | Coherent equivalences and transformations are data. The precise variance and permitted noninvertible cells must be selected. |
| Equations between comparison cells | Lean equality in `Prop`; equality proofs are proof irrelevant. Associator/unit equations are proved here. | A selected homotopy can itself be observable data, with higher composition and boundaries. Encoding it merely as `Prop` loses that observation. |
| Further dimensions | No independent higher witnesses in this ordinary contract. | Need coherences in every supported dimension; a finite model establishes only its stated truncation. |

The higher representation has a recovery issue beyond Lean elaboration. Scholze's Definition 2.3 uses a **groupoid** of correspondences; for an ordinary base this retains invertible apex comparisons. The native `SpanBicat` additionally admits noninvertible apex maps, such as Boolean collapse. A bare functor from that correspondence groupoid does not recover this client. An `(∞,2)` extension, another suitable morphism notion, or a retained ordinary route is needed. This does not refute higher correspondence mathematics. It identifies the extra recovery contract. [Scholze, Definition 2.3](https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf).

| Candidate | Author and builder cost | Retention and principal risk |
|---|---|---|
| Direct ordinary indexed operations | Builders supply indexed monoidal fibers, coherent pullback, chosen adjoints, canonical mate invertibility and relevant PF theorems. Authors can write K's composite and H's Hom-chain directly. T needs a coherent map of the used fragment. | Closest to actual native clients; current modules already absorb many mate obligations. Repeated functor associator and chosen-adjoint normalization can recur unless shared lemmas are provided. It cannot represent observable higher paths by its existing equality. |
| Small derived coherence layer | Derive BC/pasting/counit and adjoint-choice compatibility once, then expose `kunneth`, `kunneth_transpose`, `exceptionalHom`, and `map_kunneth` over separate capability inputs. Existing span action and interpretation are examples of this strategy, not work still to do. | Retains ordinary data and projection lemmas. Avoid a maximal record or independent axioms for derived mate laws. A bundle of arbitrary isomorphisms would lose the canonical-map identity needed by T. |
| Higher correspondence encoding | Model builders construct or instantiate a coherent correspondence functor, external products/diagonal operations, relevant adjoints, proper comparison, and a coherent interpretation map. Authors may share a short expression only after these are installed. | Can retain genuine higher observations if its model and interpretation do so. Missing model construction, higher map preservation, and the noninvertible-apex recovery contract remain substantive costs. Ordinary K/H output alone would not discriminate it. |

The existing source has observable wrapper costs: `Cat.Hom.isoMk`, conversions to natural transformations, `Over.OverMorphism.ext`, nested `pullback.hom_ext`, explicit `erw`, and local transparency options. These are inspected proof patterns. They are not measured productivity failures, impossibility results, or reasons to replace the mathematical interface.

## Proposed author expressions and exact rejection points

These are proposed expressions, not accepted Lean syntax:

```text
K := kunneth f g A B using chosenPullback(f,g)
K.transposed = tensorCounits f g A B
transport K along F preserving ProperProjectionBaseChange

H := exceptionalHom f A B
-- proof presentation:
by yoneda T; closed; projection! f; adjoint! f; closed; adjoint f
```

For K, elaboration must infer `A:D(X)`, `B:D(Y)`, every intermediate fiber, and the actual chosen pullback cone. It requires proper `f,g`; proper `p` is derived from pullback closure of `g`. The obligations are invertibility of canonical `BC(f,g)` and canonical `PF_f(A,g_*B)` and `PF_p(q*B,A)`, with symmetry inserted on the third step. Pushforward composition is the comparison induced by the chosen ordinary adjunctions. The map is characterized by E, so an arbitrary endpoint isomorphism cannot masquerade as K.

The direct presentation expands these factors. The derived layer inserts the same factors and proves their normalization once. The correspondence route uses composition and monoidal constraints, plus the proper `! ≅ *` comparison; its ordinary observation must recover E and hence the same K. In particular a general three/six-functor correspondence package does not by its name identify `f_!` with `f_*` on a declared proper class.

For H, `f_!:D(X)→D(S)` and `f^!:D(S)→D(X)` must form the supplied exceptional adjunction; `f*:D(S)→D(X)` and `f_*:D(X)→D(S)` form the ordinary one. Closedness supplies natural Hom-set equivalences, not merely an object named `Hom`. Exceptional PF must identify `T⊗f_!A` with `f_!(f*T⊗A)` with the correct symmetry and naturality. A pair of unrelated adjunctions alone does not supply this link. Yoneda requires naturality in the test object. The resulting H is natural contravariantly in A and covariantly in B. Its inverse laws and the whole chain must be retained. This particular derivation needs no BC square, purity or biduality theorem.

For T, the route builder supplies a base map preserving the selected geometric square and properness, fiber functors with strong monoidal comparisons, pullback comparisons, and proper-pushforward comparison mates. Their counit equation C, after endpoint conversions, is required. Canonical mate construction should derive C and its ordinary pasting compatibility; arbitrary comparison isomorphisms must prove that they equal the canonical ones or satisfy the exact needed law. Monoidality and C then identify the transported transpose with target E. This is proof transport of the named map, distinct from model existence.

Expected rejections are specific:

- A commuting square without `IsPullback` cannot discharge the BC-invertibility step. The Empty/Unit control gives a concrete failure.
- An ordinary `SpanAction` model or `GeometricMorphism` alone cannot elaborate `exceptionalHom`: no `f_! ⊣ f^!` or exceptional PF is supplied. The open immersion `A¹_R\{0}→A¹_R` is the intended nonproper paper test; substituting `f_*` for `f_!` would change it.
- A transport consisting of endpoint isomorphisms without the counit comparison cannot prove T. It must reject at that equation, rather than choose an arbitrary route.
- Strong monoidality alone cannot discharge internal-Hom preservation for transporting H. An H-transport extension must specify evaluation/currying and exceptional-operation comparisons with their compatibility; T does not already prove them.
- A higher source asks for an observable path between comparison cells. An interpretation whose only output at that dimension is a proof of Lean equality must reject that observation or explicitly declare truncation, rather than call it preserved.

## Decisions and smallest discriminating implementation

**Adopt:** retain the native APIs, whole-selection recovery obligations, and K/H/T as separate benchmarks. Reuse #569 and #632 directly. Their construction provides the strongest evidence for a derived ordinary layer: builders supply ordinary geometric hypotheses and the library proves coherence and projections.

**Investigate:** add one ordinary canonical-map module over the minimal indexed tensor/adjunction/BC/PF fragment. Implement K, its E characterization, and T for a supplied compatible map; do not add exceptional fields to this module. Supply a separate closed-exceptional module for H. Reuse mates and adjoint uniqueness, with all required input laws distinguished from conclusions. This is a concrete useful next implementation, but the ordinary result alone cannot settle higher adoption.

The smallest implementation that discriminates the higher alternatives is a finite witness test alongside those ordinary recovery tests:

1. Reuse the actual three-span client and #632 transport as the ordinary face; do not build another span action. Record its selected payload/apices and current comparison equations as immutable observations.
2. Select a finite representation with genuine 2-cell data, for example the existing strict two-groupoid infrastructure referenced by `docs/research/strict-two-groupoid-checkpoint.md`, and add a coherent interpretation of one compositional correspondence fragment. The exact correspondence construction and mapping interface are new work; the existing dependent higher model is only a candidate source of data.
3. Retain one nonzero cell between parallel comparison transformations, with fixed endpoints, whiskering and composition. Give a nonidentity map of interpretations that preserves this cell and its dependency on the selected payload. Do not append a disconnected integer tag to an ordinary record and count that as higher interpretation.
4. Exhibit a truncation which preserves the ordinary object/arrow result but identifies two distinguishable selected cells. State exactly which required higher observation fails. Recover native selections under their original pullback assumptions in the ordinary specialization, and account for the collapse apex map either through the chosen higher morphisms or an explicit retained ordinary route.
5. State constructed and supplied associator/unit/interchange laws separately. Require a checked application of the retained cell after two compositions and the comparison of the two three-span parenthesizations. No claim about arbitrary infinity coherence follows from this finite check.

The test can fail the current ordinary candidate: it cannot retain the nonzero higher cell with `Prop` equality alone. It can also fail a proposed higher candidate: merely encoding cells without a dependent transport and recovery theorem is insufficient. This makes it more discriminating than running K in two ordinary categories.

**Defer:** full motivic model construction and unbounded higher coherence, pending the scoped mathematical work under #555. Keep #633's interpretation-variable packaging separate. Defer any productivity ranking until matched author tasks and effort records exist.

**Reject:** blanket migration of slice clients into a full six-functor interface; automatic mate invertibility; replacing selected pairs or higher cells by inhabitedness; treating bare correspondence notation as constructed semantics; claiming a groupoid-only correspondence model recovers noninvertible apex maps without an extension; or claiming (T) follows from independent successful interpretations.

## Evidence and validation limits

I inspected actual declaration bodies and examples at the stated clean base, including relevant imports and pinned Mathlib mates and span structures. I opened the primary PDFs through the web tool and checked the numbered sections above. The local `pdftotext` attempt failed because that binary was unavailable; no PDF conversion or Lean process was run. I did not execute a build or fresh proof audit, add declarations, modify repository sources, or operate the tracker. Existing declarations are described as inspected checked-source artifacts, not as newly replayed tests. Proposed K/H/T interfaces and the finite higher experiment are unimplemented designs.

This report is the implementation/use lens of a design challenge. It is not independent Standards/Spec acceptance, a motivic construction, or a claim that ordinary Lean mathematics is incapable of encoding higher objects explicitly.
