# Dependent sum admission and preservation

This experiment extends the guarded contextual fragment from [#315](dependent-judgment-representation.md) with an object-language dependent sum. The selected semantic capability is a stable comprehension isomorphism between `Γ.A.B` and `Γ.Σ(A,B)`. It includes both inverse laws. Dependent elimination is derived by substitution along the inverse, so semantic eta is an explicit assumption of this capability. This construction does not claim to interpret a weaker, beta-only sum structure.

The reviewed decision is to adopt this bounded admission mechanism for the author experiment. The [component review](dependent-foundations-validation/reviews/317-review.md) records both independent axes and exact candidate acceptance. General type-theory framework formalization and higher-model adoption remain deferred. The implementation supplies direct rule soundness, semantic stability and model-map preservation, concrete native comparisons, and exact reduct recovery. The validation section separates focused development checks from final candidate acceptance.

The starting evidence is the [architecture reassessment](dependent-architecture-reassessment.md), its independent [mathematical](dependent-architecture-review/mathematical-structure.md), [implementation](dependent-architecture-review/implementation-boundaries.md), and [foundational](dependent-architecture-review/alternative-foundations.md) assessments, the [structure audit](dependent-structure-audit.md), and [#292's report](dependent-coherence-comparison.md) with its [frozen external memo](dependent-coherence-discovery/292-external-memo.md). Those assessments identify obligations; the Lean declarations linked below must supply the implementation evidence.

## Selected operations and judgments

The base already has dependent context extension, simultaneous substitutions, family and term substitution, object Id, reflexivity and contextual J. Its contextual pairing constructs a substitution into `Γ.A`; it has no family constructor `Σ(A,B)`. Existing native Type sums and delayed-family sums elsewhere in the repository therefore do not count as this source extension.

For `A` over `Γ` and `B` over `Γ.A`, the extension introduces:

```text
Σ(A,B) : Ty(Γ)
pack   : Γ.A.B → Γ.Σ(A,B)
unpack : Γ.Σ(A,B) → Γ.A.B
```

Here `Γ.A.B` means the dependent extension `(Γ.A).B`. The supplied `pack` commutes with the projections to `Γ`; `unpack ∘ pack = id` and `pack ∘ unpack = id`. `Capability` supplies these operations and laws; `Stable` extends it with stability of the sum family and naturality of `pack`. Base rule soundness needs `Capability`; the semantic reindexing results and source stability rules need `Stable`. The inverse's naturality follows by cancellation using the inverse laws. The over-base law for `unpack` follows in the same way.

The [source presentation](../../SquareKit/Internal/DependentJudgments/Sigma/Syntax.lean) uses three new operations, `sigma`, `pack`, and `unpack`. Object pair introduction is a composite: pair the supplied terms into `Γ.A.B`, compose with `pack`, and substitute the generic sum variable. Dependent elimination is the expression `d[unpack]`, where the branch `d` has type `C[pack]`. At `p : Σ(A,B)`, substitute along the section `⟨id,p⟩`. This permits a motive varying over the entire sum value.

| Rule or construction | Ordered premises | Conclusion or obligation |
| --- | --- | --- |
| Formation | `Γ ⊢ A type`; `Γ.A ⊢ B type` | `Γ ⊢ Σ(A,B) type`. |
| Pack and unpack | The same two family premises | Substitutions between the displayed dependent contexts, with their indicated direction. |
| Introduction | Formation premises; `Γ ⊢ a:A`; `Γ ⊢ b:B[⟨id,a⟩]` | `Γ ⊢ pair(a,b):Σ(A,B)`. |
| Dependent elimination | Formation premises; `Γ.Σ(A,B) ⊢ C type`; `Γ.A.B ⊢ d:C[pack]` | `Γ.Σ(A,B) ⊢ split(d):C`. |
| Computation | Elimination premises | `split(d)[pack] ≡ d` at `C[pack]`. Instantiation gives computation at `pair(a,b)`. |
| Selected eta | Formation premises | `pack ∘ unpack ≡ id`; repacking the unpacked generic sum returns it. |
| Semantic dependent uniqueness | Elimination premises; a section `e:C`; equality of its branch restriction with `d` | `e = split(d)`, proved as `Capability.split_unique`; no general source uniqueness rule is claimed. |

The elimination typing calculation is substantive: `(C[pack])[unpack] = C[pack ∘ unpack] = C`. It uses eta even before proving a uniqueness equation. Computation uses the other inverse law. The sequential source extension later admits `split(e[pack]) ≡ e`, a dependent split-eta law validated from these same semantic equations. It adds no operation and no model-side assumption. This is not a proof that every beta-only model expands to a model with judgmental eta.

Judgmental equality is the source equation judgment. Object `Id` remains a type carrying terms. Lean equality proves semantic and index equations. A presentation comparison transports terms along its specified family comparison. The selected judgmental eta is neither an object-Id witness nor an equality-reflection principle. Propositional eta would have a different contract and does not license the displayed judgmental equation.

## Dependencies and law classification

The extension's finite dependency order is: inherited structural judgments; sum formation; pack/unpack typing; their over-base and inverse equations; derived pair and split; computation and uniqueness; stability and comparisons. Family substitution and conversion are needed to state the branch and output types. The second branch binder depends on the first. Neither may be replaced by a list of unrelated untyped variables.

| Requirement | Classification | Where the work belongs |
| --- | --- | --- |
| Sum family, pack and unpack | New operations | Model capability. |
| Their inverse, over-base and stable-family/pack laws | Laws accompanying the selected new structure | Model builder, once per capability. |
| Unpack over-base and naturality | Consequences of pack laws and inverses | Shared semantic construction. |
| Pair introduction and dependent split | Derived operations over the extended signature | Shared source/semantic construction. |
| Split typing, computation, eta and uniqueness | Semantic consequences of substitution and the selected isomorphism laws | Shared construction; uniqueness adds no independent mathematical assumption. |
| Judgmental eta when compared with a weaker beta-only theory | A stronger law on unchanged operations | A separate choice of model class; no automatic expansion claim. |
| An arbitrary extra type equation | A new semantic requirement | Extension author specifies the boundary; model builder must validate the equation. |

The word *derived* in this classification describes semantic theorems and compound expressions. The source theories separately admit rules justified by those theorems. `Sigma.theory` admits pair typing, split typing and split computation; `Reindexing.theory` admits the semantic reindexing consequences; `closureTheory` admits dependent split eta. Their source facades apply these admitted rules. This implementation does not prove that every such rule is derivable in the smaller source theory before admission. Generic source soundness follows from the supplied validity proofs, without that stronger syntactic claim.

The new operations can use Id/J-generated families and terms. The inherited Id/J rules keep their interpretation when the underlying contextual model is retained. This does not prove that a Sigma capability exists on every Id/J model, or that every proposed equation involving those constructors is valid. A source derivation with a sum family in its motive still needs the actual extended interpretation.

## Primary-source framework assessment

Bauer–Haselwarter–Lumsdaine require a bijection between metavariables and object premises, respecting scope, syntactic class and generic heads (Definition 5.1). Acceptable rules derive all premise and conclusion presuppositions from their premises and have empty conclusion contexts (5.6–5.7). Acceptable theories require one symbol rule per symbol and associated congruences (5.12). Well-presented theories supply predecessor-only boundary derivations; their flattening is acceptable and well-founded (6.16–6.21). Their substitution-elimination theorem assumes substitutivity and congruity (5.22); typing uniqueness and inversion use acceptability (5.24, 5.27). These hypotheses concern their specified syntax. [*A general definition of dependent type theories*, v1](https://arxiv.org/html/2009.05539v1)

Haselwarter–Bauer's finitary rule criterion requires derivations of the metavariable context and conclusion boundary; each theory rule is checked over its predecessors in a well-founded order (2.18). Standard theories have exactly one symbol rule per symbol (2.20). Their raw deductive system includes congruence rules (2.16). Substitution is admissible in raw theories (3.8). Instantiation requires derivable instances (3.13); equality instantiation additionally requires well-formed metavariable and variable contexts (3.17). Presuppositivity likewise assumes those contexts well-formed (3.18). Economical congruence uses finitary hypotheses (3.22). Their translation between contextual and context-free presentations is internal to those specified frameworks. It is not an identification with arbitrary Horn syntax. [*Finitary type theories with and without contexts*, v1](https://arxiv.org/html/2112.00539v1)

For this example, the conventional binder presentation would have primitive symbols `Σ(A,B)`, `pair(A,B,a,b)` and `split(A,B,C,d,p)`. The argument classes and binding counts would be `(Ty0,Ty1)`, `(Ty0,Ty1,Tm0,Tm0)` and `(Ty0,Ty1,Ty1,Tm2,Tm0)`. Every object premise introduces exactly one of these metavariables. The ambient `Γ` is schematic; the framework's universal rule templates have empty conclusion context and acquire an ambient context by instantiation. The introduction boundary uses substitution to form `B(a)`; the split branch uses formation and introduction to form `C(pair(x,y))`; its conclusion uses the typing of `p` to form `C(p)`. Computation first needs both terms at that common type.

This conventional presentation explains the mathematical rule dependencies. It is not the actual Lean signature: the guarded implementation has explicit context/substitution objects and primitive `pack`/`unpack`, while pair/split are compound expressions. Its generic Horn equation has no type annotation. A full bridge would have to translate binders, contexts, all four conventional judgment forms, boundary derivations, substitution, congruence and conversion, and prove that derivability is respected. No such bridge is supplied here.

Congruence is also an obligation about dependent boundaries. Given equal first families, the second families must be compared in aligned extended contexts. Equal motives require aligned sum contexts; equal branches require the converted common motive pulled back through aligned pack maps. The local generic application congruence propagates equality of operation arguments. It does not, by itself, certify the conventional theory's typed congruence hypotheses. The local admission proofs instead establish rule validity at their guarded semantic domains.

The framework decision is to use these boundary and dependency checks as a specification discipline and prove local soundness and preservation directly. Formalizing either complete framework is deferred until a consumer needs its metatheorems and justifies the adequacy proof. Wholesale transfer of their metatheorems to this Horn encoding is rejected. This decision leaves their broader applicability open.

Lumsdaine–Warren's Theorem 3.4.1 transfers specified weakly stable structure to the split replacement of a full comprehension category satisfying LF. Their Sigma construction is in Definition 3.4.4.1 and Lemma 3.4.4.2. Section 4.1's broader extension proposal is a heuristic and excludes type-equality conclusions. Dependencies can require stability over choices of earlier structures. It therefore supplies neither the selected comprehension isomorphism nor arbitrary type equations merely from a syntax-boundary check. The present direct construction does not invoke that transfer theorem. [*The local universes model*, v2](https://arxiv.org/html/1411.1736v2)

## Substitution, comparison and rejection boundaries

For `σ:Δ→Γ`, write `σ⁺:Δ.A[σ]→Γ.A` for the inherited lift, `σ⁺⁺` for its dependent second lift, and `σΣ⁺` for the lift into the sum extension. Sum-family stability aligns the target contexts in

```text
Σ(A,B)[σ] = Σ(A[σ],B[σ⁺])
pack ∘ σ⁺⁺ = σΣ⁺ ∘ pack′
unpack ∘ σΣ⁺ = σ⁺⁺ ∘ unpack′.
```

The first two are the selected family and pack laws; cancellation derives the third. Reindexing `d[unpack]` then derives split naturality, with the branch and motive reindexed through these same maps. Repeated substitution uses the inherited lift and substitution composition laws. Merely showing equal scalar outputs would omit these dependent type alignments.

`Map` extends the inherited strict structural-map interface with sum-family and pack preservation. `Map.unpack` and `Map.split` derive preservation of the inverse and dependent eliminator, constructing the transported motive and branch. `SourceMap` extends the full contextual `ModelMap`, sharing its structural map and retaining chosen J preservation. Its constructed partial homomorphism proves preservation for every defined extended expression. Source typing supplies definedness for `Tm.interpret_map`, so ordinary authors do not prove the interpreter side condition themselves.

Transport of all assumptions through `interpret_target` requires `TypedAssumptions`: equality assumptions must have source-typed operands. `TypedEquality.map` transports a comparison with typed result operands. These restrictions retain #315's boundary: a map may lose information, and raw equality involving invalid values is not claimed to transport unconditionally. Neither theorem reflects semantic equality back into source derivability.

Native coherent comparisons between unequal family presentations have a separate scope. `Native.sigmaComparison` builds the sum-family equivalence; `comparedBranch` transports the branch under the motive comparison; `split_compare` proves the resulting dependent comparison. These are native Type theorems, not a higher-model interpretation or a claim that unequal fiber presentations are strictly equal. Raw syntax substitution (`Substitution`), substitution of derivations (`Sigma.substitute`), admitted source reindexing (`Reindexing`), and semantic stability (`Stable`) remain distinct results.

The negative semantic test is the extra type law `Σ(A,B) ≡ A`, at a singleton `A` and constantly Boolean `B`. Both sides have valid formation boundaries. A family isomorphism would map two distinct pair values into the singleton; injectivity would then equate `false` and `true`. Thus even interpreting the proposed type equation by an equivalence fails in this model. The failure concerns the designated model's expansion, not the rule's raw scoping. The separate checked `missing_dependency_rejected` case omits the second-family premise for `B`. Its variables are within the raw rule's declared scope, but assigning `B` the invalid semantic value satisfies the remaining premise and invalidates sum formation. It therefore refutes semantic admission of that missing-domain rule; it is not a parser rejection or a general scoping theorem. The preparatory omitted-motive proposal was not the implemented negative case. Neither test implements a universal admission checker.

## Responsibility and preservation scope

The mathematical contract selects which operations, laws and observations matter. It is not a Lean elaboration problem. The model builder constructs the chosen sum family and comprehension isomorphism, proves their stability, and proves the primitive comparison obligations of any model map used. The extension author supplies rules with their dependent domains and proves their validity using that capability; shared interpretation then handles derivations. The ordinary proof author supplies families, terms and typing derivations and consumes the generic theorem. That author should not repeat the capability's inverse or naturality proofs.

Tagged semantic values, index transports and host equality tests are costs of this implementation. They neither strengthen the mathematical capability nor constitute measured author effort. An implementation example can show that the theorem is reusable; a productivity claim needs the separately frozen #320 trial.

| Claim | Proved scope and evidence boundary |
| --- | --- |
| Preservation of an interpretation | `model` and `interpret` validate the constructor rules from `Capability`; `Reindexing.model` and `interpret` validate stability rules from `Stable`. `SourceMaps` derives the stated typed/defined map preservation. |
| Reduct recovery | `retain` embeds every old derivation; `reduct` recovers the old model exactly. Named `Recovery` results retain the certificate and dependent-action derivations and recover the value, certificate, action and its transported source. |
| Extension composition | `closureModel` validates an additional dependent split-eta rule over an empty extra signature. `closure_reduct`, `retain_twice` and `recover_twice` establish the two-step inclusion/reduct results. The law is semantically derived; derivability from the smaller source theory is not proved. |
| All-model expansion | No theorem that every old contextual model admits a Sigma capability. A generic constructor that takes such a capability is conditional expansion. |
| Conservativity | No theorem that every old-language equation derivable after extension was already derivable before extension. Forward embedding and equal reduct evaluation do not prove reflection of derivability. |
| Witness recovery | The named old recipes have exact evaluation recovery for every supplied model/capability and assignment. `Native.FiniteOption.recovers_selected` recovers the selected native section using the inverse motive equivalence. Neither reconstructs a witness from a lossy observation. |
| Higher adoption | Still open. Native Type sums do not supply the dependent higher interpretation required by #316 and the #321/#322 continuations. |

## Failed alternatives and decisions

Counting the old contextual package as the new object sum fails the formation/elimination requirement. Supplying a final client preservation equation as a capability field would leave the requested theorem with the caller. Reading a beta-only contract into the isomorphism model hides the eta used to type dependent split. Treating syntactic acceptability as semantic validity admits the false singleton/Boolean type equation. Applying local universes to that type equation exceeds its stated scope. These are rejected design alternatives; they are not records of failed Lean compilation unless the validation record says so.

The bounded adoption retains the base's selected Id/J witnesses and proves consequences of the new capability once. General framework formalization, universal conservativity and universal expansion are deferred rather than assumed. The [concrete coherence assessment](concrete-dependent-coherence.md) keeps #318's model-construction choice conditional. #289 owns promotion of a strictification route and the selected model's categorical proofs. Future #322 owns direct higher-groupoid families, J and a sound interpretation; #321 owns the separate cubical programme. #107 remains paused, #108 unselected and #260 inactive. This experiment does not pass the higher-model gate or preselect the fresh author task.

## Checked implementation and examples

The declarations below are in namespace `SquareKit.Internal.DependentJudgments.Sigma` unless another namespace is shown.

| Module | Construction and checked claim |
| --- | --- |
| [Capability](../../SquareKit/Internal/DependentJudgments/Sigma/Capability.lean), [Pairing](../../SquareKit/Internal/DependentJudgments/Sigma/Pairing.lean) | `split_type`, `split_beta`, `split_eta`, `split_unique`, object `pair`, and `split_pair` derive dependent elimination and its pair computation from the comprehension isomorphism. |
| [Operations](../../SquareKit/Internal/DependentJudgments/Sigma/Operations.lean), [Rules](../../SquareKit/Internal/DependentJudgments/Sigma/Rules.lean), [Theory](../../SquareKit/Internal/DependentJudgments/Sigma/Theory.lean) | Guard inversion recovers the actual dependent inputs; `rule_valid`, `model` and `interpret` validate the extended source. `eval_old`, `retain` and `reduct` preserve the old interpreter. |
| [Stability](../../SquareKit/Internal/DependentJudgments/Sigma/Stability.lean), [PairStability](../../SquareKit/Internal/DependentJudgments/Sigma/PairStability.lean) | `sumMap_id`/`sumMap_comp` keep context comparisons; `unpack_sub`, `branch_type`, `split_sub`, `split_sub_comp` and `pair_sub` derive reindexing of the dependent data. |
| [Reindexing](../../SquareKit/Internal/DependentJudgments/Sigma/Reindexing.lean), [ReindexAuthoring](../../SquareKit/Internal/DependentJudgments/Sigma/ReindexAuthoring.lean) | Stable-model validity admits sum/pack stability and the derived inverse, pair, split, branch-type and pair-second-type equations. Source authors use typing premises through the corresponding facade. |
| [Maps](../../SquareKit/Internal/DependentJudgments/Sigma/Maps.lean), [SourceMaps](../../SquareKit/Internal/DependentJudgments/Sigma/SourceMaps.lean) | `Map.split` and the source `interpret_map`/`Tm.interpret_map` derive final preservation from primitive map laws. Identity/composition and their unit/associativity equations are constructed. `Tm.pair_map`, `Tm.split_map` and `splitDerivation_target` are generic author clients. |
| [Composition](../../SquareKit/Internal/DependentJudgments/Sigma/Composition.lean), [Recovery](../../SquareKit/Internal/DependentJudgments/Sigma/Recovery.lean) | The law-only second extension and exact named old-data recovery have the scopes stated in the preceding table. |
| [Rejection](../../SquareKit/Internal/DependentJudgments/Sigma/Rejection.lean) | `collapse_boundary`, `no_collapse_equivalence`, `collapse_rejected` and `missing_dependency_rejected` distinguish valid type endpoints from a valid equation, and reject an omitted dependent input guard. |

[Native](../../SquareKit/Internal/DependentJudgments/Sigma/Native.lean) constructs `capability` and `stable` using actual dependent pairs. `bounded_split` and `bounded_beta` specialize the generic eliminator to `B(a)=Fin(a+1)` and the motive `C(a,b)=Fin(a+1)`, returning the selected `b`. The motive and second family are nonconstant. `FiniteOption` changes the context presentation by flipping Bool in `Nat × Bool`, changes the first and second finite families to Option presentations, and changes the motive. `preserves_selected` uses `split_compare`; `target_selected_some_zero` obtains the selected target value from that preservation theorem, and `recovers_selected` uses the inverse motive equivalence. `split_shift` and `pair_shift` instantiate the generic stability results at a nonidentity shift with dependent components.

[GuardedSigma](../../Examples/GuardedSigma.lean) connects the source proof to concrete selected output. `dependent_elimination_admitted` interprets the model-independent `splitDerivation`; `source_beta_selected` interprets `splitBetaDerivation` and extracts exactly the supplied `i : Fin(n+1)`. The smallest first-component case checks `n=0`. Its pair computation uses the same dependent second family. These results demonstrate theorem reuse; they do not measure independent author productivity.

[GuardedSigmaReindexing](../../Examples/GuardedSigmaReindexing.lean) uses the fixed `splitReindexDerivation` through `Reindexing.interpret`. Its `fresh_split` theorem compares the interpreted pulled eliminator with fresh reconstruction for arbitrary admitted data. `Nonidentity.fresh_shift` specializes to `A(n)=Fin(n+1)`, `B(n,a)=Fin(a.val+1)` and a dependent motive. `fresh_composite` uses shift after doubling, with samples distinguishing that order from doubling after shift. `twice_fresh` and `composite_fresh` interpret the source proofs for successive substitution and the composite of the two lifted arrows.

`Reindexing.Tm.splitSubComp` is a source derivation for two arbitrary successive substitutions. It rebuilds the sum families, motive and branch at each step, obtaining the intermediate branch typing from the admitted `branchType` equation. Congruence and transitivity compose two `Tm.splitSub` derivations. `Tm.splitSubComposite` additionally uses inherited term-substitution composition to compare that twice reconstructed split with substitution along the composite of the two sum lifts. `Tm.pairSubComp` reconstructs pair introduction twice, using `Tm.pairSecond` to type the reindexed dependent second component. Semantic `sumMap_comp` separately compares the two sum lifts with the canonical lift of the base composite and its family comparison. The source composite-of-lifts result and that semantic canonical-composite result have different conclusions.

## Statement review and validation scope

Statement review checked `B` over `Γ.A`, the motive over `Γ.Σ(A,B)`, the branch at `C[pack]`, both substitution directions, and the eta-dependent elimination type. It also checked the common structural map used by contextual J and Sigma preservation, the definedness/typed-assumption restrictions, the unequal-presentation motive transport, and exact selected witness recovery. Native constructions establish that the interfaces used by these examples are inhabited. The source equation remains separate from object Id and host equality.

Focused development builds passed for the semantic capability, stability, pairing, native comparisons, maps, base source theory, composition, rejection, recovery, source beta examples, source-map preservation and `ReindexAuthoring` including `Tm.splitSubComp`, `Tm.splitSubComposite` and `Tm.pairSubComp`. The retained `317-clean-focused-build.log` records successful compilation of `Rejection`, `Recovery`, `Composition` and `Examples.GuardedSigma`; `317-source-beta-build.log` records the selected source computation; `317-source-maps-build.log` records source-map compilation; `317-reindex-build.log` records reindexing/source-authoring compilation. The final focused build of both concrete example modules passed with 861 jobs in `317-final-focused-build.log`. It includes the nonidentity successive and composite source-substitution clients. Main declaration and axiom spot checks are recorded in `317-main-statements.log`. Earlier rejection/recovery logs include failed development attempts and are superseded by those successful builds. Semantic and source-map declaration/axiom spot checks are recorded in `317-semantics-statements.log` and `317-source-maps-statements.log`; they do not replace the exhaustive audit.

Focused builds do not certify a mutable checkout as an accepted candidate. Acceptance additionally requires the clean candidate build, exhaustive proof audit, four proof-audit regression fixtures, immediate candidate verification and independent Standards/Spec review. The coordinated implementation handoff records the exact base and candidate, commands, receipts and review outcomes; the focused-check inventory above does not replace those gates.
