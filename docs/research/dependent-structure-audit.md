# Dependent structure: reconstruction and foundation choices

Research and checked reconstruction for [#314](https://github.com/VladimirMarko/conaled/issues/314), against `9b0a0fe143c6f97f399632d4bb34a179db012181`. The starting evidence is the [reassessment](dependent-architecture-reassessment.md), its three linked independent assessments, [#292](dependent-coherence-comparison.md), and the unchanged [external memo](dependent-coherence-discovery/292-external-memo.md). This report corrects two incomplete premises in that evidence: pairing naturality and display pullbacks are derived laws, and every generated context admits a derived empty substitution. Neither result requires another model field.

Adopt the derived constructions. Investigate a judgment representation whose indices do not quantify over the entire current `Model`, using signature-independent comprehension and explicit constructor requirements. Retain the existing source and groupoid interpretation until a replacement recovers their capabilities. There is no evidence here that local universes, an extensional foundation, or a larger structural record solves the ordinary author's presentation-alignment problem.

## Complete model-field inventory

The inventory reads the whole [structural record](../../SquareKit/Internal/PathTransport/Model.lean) and [contextual model](../../SquareKit/Internal/PathTransport/ContextualModel.lean), not their names. “Supplied law” means an existing premise of those records, not a newly proved independence result. An additional property is called independent below only where a counterexample is provided.

| Fields or requirement | Classification and use |
|---|---|
| `Context`, `Family`, `Section`, `Substitution` | Supplied data: objects, type fibers, term fibers and arrows. No source-generation or terminality restriction on ambient contexts. |
| `idSub`, `compSub`; `comp_id_left`, `comp_id_right`, `comp_assoc` | Supplied category data/laws. They construct `ContextCat`; composition order is `compSub σ τ = σ after τ`. |
| `subTy`, `subTm`; `subTy_id`, `subTy_comp`, `subTm_id`, `subTm_comp` | Supplied substitution data/laws. Type equations are Lean `Eq`; dependent term equations are `HEq`. They construct `indexedFamilies` independently of primitive symbols. |
| `extend`, `weaken`, `genericVariable`, `pairSub`; `weaken_pair`, `variable_pair`, `pair_eta` | Supplied comprehension data and beta/eta laws. They imply uniqueness, representability, pairing naturality, lifted-substitution laws and display pullbacks. No extra fullness law is needed for the all-squares category constructed here. |
| `empty` | Supplied distinguished context only. Ambient terminality is an independent additional property; see both countermodels below. |
| `base`, `fiber`; `base_sub`, `fiber_sub` | Signature-specific supplied assignments and stability laws. `base Γ` is stable in every context; `fiber` is an operation on a *section* of that selected base. The concrete instance uses a fixed groupoid C and a set-valued functor B on C. These are not prerequisites for generic comprehension. |
| `identity`, `reflexivity`; `identity_sub`, `refl_sub` | Supplied logical operations and stability laws on existing substitution structure. Identity returns a family; a section is not required to be a host equality proof. Formation/reflexivity alone provide no eliminator. |
| `Model.j`, `j_beta`, `j_sub` | Supplied contextual eliminator and laws, for every admitted family A, section x, finite dependent tail T, motive D and branch d. `j_sub` reindexes the tail, motive and branch using *constructed* canonical maps. It is not a law only for closed or constant motives. |
| `sectionSub`, `lift`, `pathFamily`, `pathContext`, `rootSub`, `Telescope`, `rootTail`, `pathSub`, `squareLift`, `Telescope.square`, `pathTail`, `branchMap`, `reindexBranch` | Existing derived data. Their dependency chain goes from pairing through projections and telescope recursion to the J law's dependent branch type. |
| `pair_ext`, section/variable/root equations, path and branch commuting squares | Existing derived laws, before this ticket. The new reconstruction reuses them. |
| Pairing naturality; lift identity/composition; pullback universal property; display comprehension | Newly checked derived consequences, described below. |
| Global empty-map operation and uniqueness; finite products; LF exponentials | Additional capabilities if requested by a judgment or construction theorem. Global terminality does not follow. No generic finite-product or LF claim is made. |
| Object-language Sigma formation/introduction/elimination, computation and stability | New operations with accompanying laws, absent from this fragment. Semantic context extension is not a Sigma constructor. |
| UIP, equality reflection, extensional identity, stronger J uniqueness | Properties constraining an unchanged signature, not automatically new operations. The current intensional interface does not promise them. This audit does not establish independence of every such property. |
| Pseudo comparisons of arbitrary full models, dependent source initiality, generated-empty uniqueness | Unresolved comparisons or metatheorems, with owners below. None is silently included in a record of assumed conclusions. |

A constructor package should include the equations specifying its meaning. It should not include consequences already proved from comprehension. Equally, a stronger principle on existing operations may be a legitimate optional requirement without adding an operation.

## Source judgments, indices and clients

At the pinned revision, [`Typed.lean`](../../SquareKit/Internal/PathTransport/Typed.lean) contains the following complete constructor inventory. Entries name existing constructors; they do not claim conventional rules that are not present.

| Judgment | Constructors and dependency |
|---|---|
| `CtxDeriv` | `empty`, `ext`, `path`, `telescope`, `branch`. Path contexts and branches depend on typed families, terms and telescopes. |
| `TelDeriv` | `nil`, `cons`, `pullback`, `pathReindex`. The last two depend on generated substitutions; path reindexing changes the based path context. |
| `TyDeriv` | `base`, `fiber`, `identity`, `sub`. There is no Sigma, Pi, universe, truncation or modal-lock constructor. |
| `TmDeriv` | `var`, `refl`, `sub`, `pathInduction`, `pathInductionReindex`, `genericJ`, `reindexJBranch`, `conv`. The J rules retain motive, branch, endpoint and dependent-tail derivations. Conversion is guarded by a source type equation as well as its annotation equality. |
| `SubDeriv` | `id`, `comp`, `weaken`, `projection`, `root`, `rootTail`, `pathTailMap`, `pair`. Empty substitution is now derived from these constructors. |
| `TyEqDeriv` | `refl`, `symm`, `trans`, `fiber`, `identity`, `identityType`, `subCongr`, `sub`, `subId`, `subComp`, `baseSub`, `fiberSub`, `identitySub`. |
| `TmEqDeriv` | `refl`, `symm`, `trans`, `conv`, `sub`, `subId`, `subComp`, `reflSub`, `reflCongr`, `subCongr`, `variablePair`, `jCongr`, `jCongrAt`, `jBeta`, `jBetaReindex`, `jSub`. Computation and dependent stability are explicit rules, not inferred from formation. |
| `SubEqDeriv` | `refl`, `symm`, `trans`, `comp`, `pairCongr`, `idLeft`, `idRight`, `assoc`, `weakenPair`, `pairEta`. There is no general empty-substitution uniqueness rule. |

`CtxCode = (M : Model) → M.Context`; `TyCode`, `TmCode`, `SubCode` and `TelCode` depend pointwise on those context codes. Thus even a purely structural judgment is indexed over the full J-equipped, fixed-signature model class. A term's raw expression, semantic term code, raw type and semantic type code are separate indices. `typeSound`, `termSound` and `subSound` extract annotation equality from generated conversion. The recursive `interpret*Checked` functions interpret the constructors and prove agreement with their annotations; evaluating an arbitrary code is not a source typing derivation. Equality of decoded meanings alone does not create a conversion derivation.

The relevant dependency and client groups are:

| Modules | Obligation that migration must retain |
|---|---|
| `RawContext`, `Syntax`, `Typed`, `Authoring`, `Named`, `Endpoints` | Raw binding/substitution, generated judgments, guarded conversion, semantic interpretation and checked author wrappers. |
| `Derived`, `DerivedCoherence`, `Binding`, `Concatenation`, `StructuralCongruence`, `CommandCongruence`, `TransportCongr`, `ConcatenationCongr` | Derived transport/concatenation and dependent congruence. Raw and annotation alignment remain distinct. |
| `ReindexCoherence`, `RawReindex`, `SourceReindex`, `NativeNormalization`, `TransportNormalization`, `ConcatenationBeta`, `ConcatReindexBeta` | Existing canonical reindexing and computation comparisons. They do not prove the paused fresh-command comparison. |
| `TransferFrame`, `TransferRoot`, `TransferBranch`, `TransferRootBranch`, `TransferAssembly`, `TransferApplication`, `Transfer`, `TransferConsumer`, `UniversalTransfer` | The existing generated transport-composition derivation with its motive and branch, rather than a separate target reproof. |
| `SplitFamily`, `ContextualElimination`, `TelescopeElimination`, `PathContext`, `SectionNormalization`, `GroupoidIdentity`, `GroupoidElimination`, `JNaturality`, `GroupoidSoundness` | Actual groupoid families and sections, constructed contextual J with beta and stability, including dependent tails. |
| `DerivedSemantics`, `SourceSemantics`, `ConcatSemantics`, `TransferSoundness`, `EliminationUniqueness`; `SquareKit/GroupoidTransport*` | Connections from the admitted source proof to the concrete model and route observations. |
| `Examples/TypedPathTransport`, `DependentCongruence`, `PathTransportUniqueness`, `AgdaTransferDiagnostics`, `AgdaTransferModels`, `GroupoidTransport`, `GroupoidRoutes`, `LocalUniversesBoundary` | Retained callers and negative boundaries. Their exact selected terms and observations must be recovered where promised. |
| Root `Dependent.lean`, `SquareKit/LocalUniverses`, `Examples/LocalUniverses` | Separate native Type-family Pi/Sigma and delayed-family constructions. They do not extend `TyDeriv` by import. |
| `Examples/SecondIdentity` and its algebraic two-loop semantics | Separate higher-witness observation and native-equality rejection. It does not provide a dependent higher interpretation of `Typed`. |

This inventory covers the PathTransport fragment under review. The other dependent sheaf/function fragments are separate languages, not evidence that this `Model` already supports their constructors.

## Reconstructing comprehension

[`Comprehension.lean`](../../SquareKit/Internal/PathTransport/Comprehension.lean) proves `pair_naturality` by `pair_ext`: both sides have base component `σ ∘ τ`, and their generic-variable components agree by term substitution and variable beta. `pair_unique` makes the resulting universal property explicit. Neither proof uses `base`, `fiber`, Id, reflexivity, J or `empty`.

For a commuting square `σ f = p g`, `pullbackFactor` pairs f with the generic variable pulled back along g. Its type cast is justified by that square and `subTy_comp`. Projection beta proves the first triangle; `pair_ext` proves the second triangle and uniqueness. `displayPullback` packages those proofs as Mathlib `IsPullback`, for arbitrary ambient arrows and arbitrary families.

`lift_id` and `lift_comp` use the induced context map `familyComparison` for the type equalities `A[id]=A` and `A[σ][τ]=A[σ∘τ]`. Their source contexts are generally only propositionally equal. The comparison's projection and variable laws, identity, inverse and composition equations are checked. This avoids treating a heterogeneous equation as a strictly typed equation between arrows with different domains.

[`DisplayCategory.lean`](../../SquareKit/Internal/PathTransport/DisplayCategory.lean) constructs a category with objects `(Γ,A)` and **all commuting squares** between their display maps. `comprehension` sends it to the arrow category and is fully faithful by its explicit hom inverse. `displayBase` takes the base context. The nontrivial part is `display_cartesian`: every square over `σ∘τ` factors uniquely over the chosen reindexing square with base τ. Together with the constructed pullback and fullness, this supplies the display-map comprehension category, without terminality. The factorization theorem states the cartesian property directly; no separate Mathlib fibration typeclass instance is claimed.

Fullness is relative to the chosen arrows. [`FamilySquares.equivalence`](../../SquareKit/FamilySquares.lean) independently proves that, for Type-valued families, a dependent function `∀ γ, A γ → B(f γ)` is exactly a function of dependent sums whose first projection is f. Both inverse laws and preservation of identity/composition are checked. This discharges the concrete Type comparison, including dependent codomain fibers.

For the groupoid model, `sectionsOver` identifies sections of `A[σ]` with **actual functors to the total groupoid over σ** after unfolding the existing ULift wrappers. It does not replace these functors by fiber-object functions. A stricter comparison fails: [`GroupoidComprehensionBoundary`](../../Examples/GroupoidComprehensionBoundary.lean) constructs a shear of the total groupoid of a constant C₂ family over C₂. On arrows it sends `(g,h)` to `(g,g+h)`. It commutes with the projection but sends the chosen horizontal lift `(1,0)` to `(1,1)`. Hence not every commuting square preserves the chosen splitting. A general equivalence with pseudonatural transformations of groupoid families is not proved here; it is not required to use the all-squares category, and remains a separate comparison for #318 if that presentation is selected.

## Empty contexts: three different restrictions

[`CtxDeriv.emptySubstitution`](../../SquareKit/Internal/PathTransport/EmptySubstitution.lean) constructs an actual generated substitution to `[]` for **every** context derivation. Extension uses weakening; a path uses two weakenings; a telescope uses projection; a branch uses projection of the telescope pulled back along the root. The result retains its raw substitution, semantic code and `SubDeriv`. Do not add a primitive empty substitution merely because the constructor inventory lacks one.

The original full Bool countermodel is retained unchanged. It has discrete Bool contexts, `empty=false`, and no arrow from true to false. Extensions preserve their context, so restricting to its generated component removes that particular obstruction.

[`ReachableLoops.model`](../../Examples/DependentStructureBoundary.lean) supplies a different **full `Model`**, with one Unit context and Bool endomorphisms, identity false, composition disjunction, Unit families/sections and identity extension. Pairing leaves the base arrow unchanged. Contextual J returns Unit for every admitted tail, motive and branch; its full beta and dependent substitution fields check. The interpreted empty context is already reachable and has distinct false/true endomorphisms. Thus even the *full subcategory on reachable objects* need not have a terminal empty context. This is a uniqueness obstruction, unlike the Bool model's existence obstruction.

Restricting arrows to interpretations of generated `SubDeriv` is a third construction. The loop model's extra true arrow is not asserted to be generated. `pointEmpty` checks the derived empty map in that model. This audit proves generated empty-map existence, not uniqueness of all generated arrows into empty, nor a terminality theorem for the source quotient. #315 owns that remaining question when specifying its judgment category. A solution should prove the projection invariant or give an exact generated counterexample; ambient loops alone cannot decide it.

The current relative fragment is sound without global terminality. Its supported rules do not demand a map from every ambient context, and source existence is already derived. Global terminality is therefore an optional structural capability for this fragment, required if a successor advertises a conventional terminal empty context or invokes a theorem requiring finite products. This verdict concerns the generic records. The concrete groupoid instance chooses the discrete singleton as empty, which does have unique functors into it; neither countermodel diagnoses a defect in that instance.

## Independent structural and author presentations

[`RepresentedFamilies.lean`](../../SquareKit/RepresentedFamilies.lean) specifies indexed types/terms with functorial substitution over a category C, then a representing object with a natural equivalence

```text
Hom(Δ, Γ.A) ≃ Σ(σ : Hom(Δ,Γ)), Tm(Δ,A[σ]).
```

It contains no projection, generic-variable or pairing fields. Those operations are recovered from the equivalence, and their beta/eta and pairing-naturality laws are proved. [`Representability.lean`](../../SquareKit/Internal/PathTransport/Representability.lean) constructs this presentation from the current record and proves that the recovered projection, generic section and pairing are the original ones, including the selected term. Conversely the independent presentation supplies the comprehension operations and their laws; it cannot reconstruct the old signature, distinguished context or Id/J without additional assignments. This is a representative reconstruction of the structural fragment, not an asserted equivalence of the categories of full `Model` records.

[`TypeFamilyRepresentation`](../../SquareKit/TypeFamilyRepresentation.lean) constructs the independent presentation directly from arbitrary Type families. It does not manufacture a PathTransport `base` or `fiber`. `IndexedFamilies` uses `HEq` only for metatheoretic dependent equations. This is a hom-set presentation of representability; the code does not bundle a natural transformation of total-term and type presheaves. Awodey's representable-presheaf account supplies the external comparison: representability packages comprehension, while intensional Id elimination needs additional lifting structure. The usual terminal-context assumption is separate from the relative construction used here. [Awodey, §1 and Proposition 20](https://arxiv.org/pdf/1406.3219)

For an alternative **author** representation, [`UniformOperations`](../../SquareKit/UniformOperations.lean) compares finite variable syntax with operations over all carriers, supplied with naturality under every function. `syntaxEquiv` proves that every such n-ary operation is exactly one variable: evaluate it at `Fin n` with the identity environment, then use naturality along the chosen environment. This is a proved reconstruction, not an assumed initiality field. `no_closed` and `no_equivariant_choice` reject unwarranted extensions: even selecting an element from every inhabited carrier cannot commute with every automorphism, since Bool negation has no fixed point. Merely quantifying a Lean function over all models gives no uniformity theorem.

That variable-fragment equivalence does not establish dependent syntax initiality or the memo's transport theorem. It makes controlled uniform authoring a live alternative with an explicit proof obligation. Bezem–Coquand–Dybjer–Escardó define uniform families using strict structure-preserving maps and construct initial structured CwFs for their valid generalized-algebraic signatures. Their theorem does not provide parametricity for unrestricted Lean programs. [§§3–4, Theorem 1](https://arxiv.org/pdf/2012.08370) Controlled shallow embedding is also eligible, but abstraction hiding alone is not the missing interpretation proof; the published shallow-embedding result distinguishes its checked injectivity theorem from the broader moral-correctness claim. [Kaposi–Kovács–Kraus, Theorem 2 and §8.2](https://arxiv.org/pdf/1907.07562)

The present reconstruction uses strict substitution and equality-induced context comparisons with checked composition. Full display squares allow all total maps over the base. The uniform-variable comparison uses strict maps of its selected structure (all functions). A future full-model comparison may instead be pseudo: it must specify context and type comparisons, transport term components through those type comparisons, and prove unit/composition and constructor compatibility, including J branch data. Unrelated isomorphisms cannot serve as that contract. Clairambault–Dybjer's pseudo CwF maps and coherence conditions are a source for this distinction; their LCCC biequivalence also assumes extensional identity and democracy, so it is not a license to erase current intensional witnesses. [§§3–5](https://arxiv.org/pdf/1112.3456)

## Identity and Sigma admission

The existing groupoid model constructs contextual J using equivalences of based-path contexts, lifts those equivalences through arbitrary finite tails, and proves beta and canonical dependent substitution. The dependency is visible in `pathEquivalence`, `rootTailEquivalence`, `contextualJ`, `contextualJ_beta` and `contextualJ_sub`. The primitive family B is set-valued; arbitrary semantic families are groupoid-valued; identity families are discrete groupoids of fiber arrows. Consequently first path witnesses remain observable, while nontrivial second identities are not supplied by that instance. These are different restrictions.

The requested Sigma package needs a family `Σ(A,B)` for B over Γ.A, pair/fst/snd or dependent elimination, computation equations, any advertised eta, and substitution laws using the lifted substitution in B. Elimination and the type of the second component cannot be omitted. Eta or stronger computation can constrain the same operations; they are not automatic new constructors. Root `Dependent.lean` and #292 already construct the Type specialization, including a selected value/witness pair through two substitutions. They do not interpret new generated Sigma judgments or provide the higher observation. #317 owns constructor admission after #315's reviewed boundary.

LF is not a missing author rule. Lumsdaine–Warren require full comprehension, finite products and specified dependent exponentials, plus the relevant weakly stable constructors; right splitting requires pseudo-stability of the full constructor data. Their general extension discussion excludes conclusions asserting type equality. This audit supplies the display-comprehension part for the specified arrows, not LF exponentials or the weak-model strictification theorem. [Definitions 3.1.2–3.1.3, Theorem 3.4.1 and §4.1](https://arxiv.org/pdf/1411.1736)

## Decision matrix and next experiments

| Route | Decision and reason | Required next evidence / owner |
|---|---|---|
| Add pairing/lift/pullback/fullness fields to the old model | Reject as new obligations: the checked reconstruction derives them. | Reuse `Comprehension` and `DisplayCategory`. |
| Local derived repair of existing source authoring | Investigate; the structural machinery is sound and reusable, but does not identify arbitrary fresh J presentations. | #315 compares repair with its alternative on a fixed dependent task; #107 remains paused. |
| Signature-independent structural data plus constructor packages | Adopt as the investigation boundary. `RepresentedFamilies` supports structural clients without `base`, `fiber` or J. | #315 chooses the actual judgment representation and map contract, retaining the reviewed reconstructions. It must distinguish optional empty uniqueness from derived empty-map existence. |
| Uniform semantic authoring | Investigate, with explicit preservation evidence. The variable-fragment equivalence is positive evidence; the Bool selector is a rejection test. | #315 must construct its admitted dependent operations and their interpretation, or state the exact missing translation. No arbitrary-host-function parametricity assumption. |
| Explicit independent syntax or controlled shallow syntax | Investigate as replacement candidates; current semantic-code indexing is not a mandatory endpoint. | #315 constructs substitution, conversion and interpretation for the stated fragment and compares author obligations. Full dependent initiality remains unproved here. |
| Replace intensional Id by host equality or extensional LCCC semantics | Reject for the selected higher-observation contract, while retaining useful extensional interpretations with their stated scope. | #316/#321 supply the connected higher interpretation. This audit adds none and does not duplicate their programme. |
| Local universes or right splitting | Conditional investigation, not default adoption. Existing strict models gain no missing law merely by renaming their presentation. | #318 must identify a concrete benefit, choose its actual morphisms, construct remaining hypotheses and test the needed constructor. |
| A chosen universe or another foundation | Keep eligible; no immediate adapter to old annotations is required to investigate. | Show coverage of the selected families, constructor/eliminator closure, comparisons, and retained observations before migration. |
| Internal construction of a setting from varying signature data | Independent stress case for the proposed boundary. | #319's prospective finite geometric presentation and nested classifier should work with relative comprehension. No theorem from that concurrent work is assumed here. |
| Wholesale retirement of the old source/model | Defer until capability recovery is checked. | #315/#317/#320 and the model work must provide evidence, not module-name parity. |

The next interpretation experiment should use the memo's actual dependent pair and witness, not only a pair of endpoints. It must compare repeated substitution with composition for the type, selected value, η, and `apd_η(h)`, and test both a useful first-path observation and the designated higher observation where the model supports it. The interpretation theorem must cover every admitted motive, elimination and computation rule. A deliberately lossy model remains valid for its declared observations; at least one claimed higher interpretation must retain the selected h. Exact selected data are required where the client contract asks for them.

Migration must recover the existing generated transport proof and conversion discipline, arbitrary finite dependent tails, concrete groupoid J/beta/stability, nonconstant action and path observations, two-substitution laws, and selected dependent witnesses. It must distinguish rebuilding a command from substituting a fixed command. Mathematical capability, model-builder proofs, ordinary-author obligations and host casts should be reported separately. This audit measures no author productivity. #320 owns the prospective frozen author experiment; #108's fresh theorem remains unseen and unselected.

## Statement review, failed approaches and validation

The retained cases are in [`DependentComprehension`](../../Examples/DependentComprehension.lean), [`DependentStructureBoundary`](../../Examples/DependentStructureBoundary.lean), and [`GroupoidComprehensionBoundary`](../../Examples/GroupoidComprehensionBoundary.lean).

- Pairing and pullback claims quantify over arbitrary ambient families and substitutions. The mediator is constructed from a section; uniqueness compares both components. Neither terminality nor a desired pullback field is assumed. The groupoid specialization uses the public pullback and lift theorems.
- Lift identity/composition compare arrows with their actual domains via `familyComparison`. Its inverse and composition laws establish coherence for those equality-induced comparisons, not for every possible pseudo map.
- The independent representability law recovers operations using the image of identity and the inverse equivalence. Its naturality premise is the defining natural representation condition, not an assumed pairing equation. The Type instance constructs that condition by precomposition.
- The dependent-function/square example uses `Fin(n+1)`. Increment then double sends base 3 to 8, retaining index 2; reverse order would give 7. The proof uses `equivalence_comp` and its inverse. It tests dependence and composition order, not merely equality of a definition with itself.
- The groupoid shear is a functor on the *actual Grothendieck construction*. Its projection square commutes; its chosen-lift failure is a fiber-arrow inequality in C₂. No groupoid or LF failure follows from it.
- The Bool and loop countermodels supply the unmodified full contextual-J fields. Their admitted motives are Unit families, so those fields are satisfiable and exhaustive for the instances. The first denies global existence, the second denies ambient uniqueness at a reachable object. Neither is used to refute source-generated uniqueness.
- The uniform-operation equivalence ranges over all small carriers and all functions at fixed finite arity. The generic environment recovers a variable; Bool negation refutes arbitrary equivariant selection on inhabited carriers. This is not a dependent-language completeness theorem.

Attempting a literal lift identity without transporting its domain fails at the type: `extend Γ (A[id])` and `extend Γ A` are only propositionally equal. `familyComparison` is the required correction. Equating all display squares with chosen-lift-preserving groupoid maps is mathematically false, as the shear proves. Inferring generated-empty nonuniqueness from ambient loops would also be invalid; that inference is explicitly excluded. The failed assumptions are retained as stated boundaries rather than promoted to extra fields.

Focused validation builds `Examples.DependentComprehension`, which imports every new module. The public entrypoint imports it for the full build and exhaustive axiom audit. Exact candidate validation and independent review receipts are recorded in the implementation handoff. No toolchain, audit exception, source axiom or frozen memo was changed.

The [component acceptance record](dependent-foundations-validation/reviews/314-review.md)
retains the exact reviewed candidate, both independent reports and matching
validation evidence. Final orchestration acceptance is a separate gate.

The [generated-empty follow-up](generated-empty-substitutions.md) now specifies
a closed structural arrow grammar and proves uniqueness modulo source equality
there. It also constructs a source-generated counterexample when a primitive
substitution hypothesis is admitted. Its explicit policy boundary preserves
the distinction above between ambient arrows and source-generated arrows;
the wider source-adequacy comparison remains with #326.
