# Guarded derivations and reusable interpretation

The experiment constructs model-independent source judgments for the frozen transport memo, with interpretation in any supplied full contextual model. The selected value, value-dependent certificate and `apd_η(h)` are generated from contextual J. Their substitution comparisons are generated source equations, including equality with a freshly reconstructed certificate and dependent action. Ordinary authors inherit these equations and strict-model preservation from their derivations.

The reviewed decision is to **adopt this source boundary for the constructor and independent-author experiments**. The [component review](dependent-foundations-validation/reviews/315-review.md) records both independent axes and exact candidate validation. Retirement of the existing universally annotated `Typed` API is deferred. The replacement has a checked path-sensitive groupoid interpretation as well as native Type examples, but it does not discharge the separate higher-model gate or automatically translate every old client. This report states those recovery obligations below.

## Mathematical contract and representation decision

The [prospective mathematical freeze](dependent-judgment-freeze.md), commit `0624161`, precedes representation implementation. It uses the independently specified [external memo](dependent-coherence-discovery/292-external-memo.md) and the reviewed [structure audit](dependent-structure-audit.md). The representation addendum was approved on 2026-11-05 after a checked dependent pairing specialization. That approval selected guarded derivations for investigation; it did not retroactively change the mathematical freeze.

The fragment has context extension, variables, pairing and projection, identity and composition of simultaneous substitutions, and substitution into families and sections. It admits object Id, reflexivity, and contextual J with arbitrary finite dependent tails, computation and substitution. The memo authors

```text
x,y,z : A; p,p′ : Id_A(x,y); h : Id(p,p′); q : Id_A(y,z); u : B(x)
v(p) = tr(q,tr(p,u))
η(p) : Id_B(z)(v(p),tr(p·q,u))
K(p) = Id_B(z)(v(p),tr(p·q,u))
apd_η(h) : Id_K(p′)(tr_K(h,η(p)),η(p′)).
```

The pair `(v,η)` is a contextual dependent package. There is no object-language Sigma constructor in this fragment. Issue #317 must supply an actual constructor, elimination, computation and substitution extension. `GeneratedContexts` recursively constructs an empty substitution for each generated context. Its two-extension case permits a dependent second family. This proves existence, without asserting uniqueness of generated arrows or ambient terminality.

Object identity is modeled data. Source judgmental equality is an inductively generated judgment. Lean equality checks semantic indices and proves metatheoretic laws. Presentation equivalences compare different interpretations. None of these mechanisms is an equality-reflection rule from decoded semantic equality back to source equality.

## Competing representations

| Route | Author capability | Reuse and remaining obligation | Decision |
| --- | --- | --- | --- |
| Existing `Typed` source | Generated derivations retain annotations indexed by every current model. | Existing groupoid observations remain useful; extension to another semantic interface requires corresponding annotations. | Keep existing clients during migration. |
| Fixed templates plus coherent comparisons | A command builder constructs the tail, motive and reflexive branch once; callers inherit its J substitution comparison. | Repairs that repeated command problem, but does not remove universal annotation indices from the underlying source. | Retain as a useful client abstraction, not a sufficient replacement. |
| Compatible sections of a fixed model diagram | Components satisfy the specified arrows' compatibility equations. | Restriction forgets components. It cannot manufacture an interpretation at a newly admitted model, and compatibility does not imply generatedness or source extraction. | Reject as the sole author representation; eligible as joint semantics. |
| Guarded operation syntax and derivations | Syntax-indexed context, family, term, substitution and telescope judgments; hypotheses expose dependencies. | One retained recipe is recursively interpreted at arbitrary additional supplied models and assignments. Soundness and defined-map preservation are proved. | Proposed source boundary for subsequent experiments. |

The baseline already has a checked template repair: `PathTransport.Typed.Authoring.PathCommand.rebuild` reconstructs the telescope, motive and branch, and `interpreted_rebuild` compares its generic term with the substituted term. Those interfaces still carry `CtxCode`, `TyCode`, `TmCode` and `TelCode` parameters ranging over the current models. The new `DependentJudgments.Command` retains that useful builder pattern while moving its indices to expressions and guarded source judgments. The coherent native construction supplies additional presentation evidence; it does not pretend that the old template removed its semantic indices.

The failed section route has a concrete obstruction. A diagram with one Bool carrier and no nonidentity arrows admits either selected element. Adding negation as an automorphism admits neither invariant selection. Restriction along a diagram map exists, but extension does not follow. The retained Bool symmetry theorem also rejects arbitrary classical selection as a uniform authoring discipline. A term at every model is insufficient without preservation under the specified maps.

The replacement is externally motivated by the essentially algebraic account of dependent structure: operations have domains of definition expressed by premises. Generalized algebraic theories separate specified model structure from syntax and its interpretation. Their published initiality result is not imported as a theorem about this development. The Lean construction proves recursive evaluation and soundness directly; it does not need initiality. [Bezem, Coquand, Dybjer and Escardó, §§2–4](https://arxiv.org/pdf/2012.08370)

Representability of dependent types and coherent versus strict preservation also motivate keeping comprehension data and comparison laws explicit. These are design references, not replacements for the local checked constructions. [Awodey, natural models](https://arxiv.org/abs/1406.3219), [Clairambault and Dybjer, dependent type theory and locally cartesian closed categories](https://arxiv.org/abs/1112.3456)

## Source and interpreter

`GuardedTheory.Derivation` is indexed by expressions, assumptions and a judgment, not by an entire semantic `Model`. Raw terms reuse `FinitaryTerm`, factored from the existing compositional-coalgebra tree, substitution and fold laws. `CompositionalCoalgebra.Term` and the source var/app notation expose that same core. The source-specific predicates, guarded rules and derivations are separate.

`Comprehension` and `ContextualOperations` interpret the structural and full contextual-J signatures. Contexts, families, terms, substitutions and finite telescopes are tagged semantic values. `Theory.rule_valid` proves every admitted rule from the supplied model's laws. The derived shape, pairing-composition, comprehension-eta and path-reindex rules are also proved in that model; they do not postulate transport, concatenation or certificate equations. `DerivedPaths`, `DerivedCertificates`, and the reindexing modules construct those recipes and equations from J and structural laws.

The host interpreter totalizes partial operations with `invalid`. Classical equality checks metatheoretic sorting indices and transports stored values after a successful check. Correctly sorted evaluation returns the supplied operation and selected section exactly. This requires no decidable equality or sorting procedure from an actual contextual model, and no choice constructor in the object calculus. Host noncomputability is an implementation cost of the semantic adapter.

General soundness interprets every source derivation at any model satisfying its premises. Source substitution and its evaluation law are recursive. Conversion and equality preservation follow from the generated equality rules and actual semantic laws. Evaluation depends on the retained expression, not its typing proof: two derivations of the same recipe cannot select different semantic values. No derivation-uniqueness or classifying-model theorem is needed for that statement.

The target adapter still consumes the existing full contextual `Model`. Its legacy base/fiber fields remain, although the new source operations and strict maps do not refer to them; schematic signature data are supplied by guarded assignments. Removing those fields is a separate semantic-interface migration. Their presence does not reintroduce model quantification into source judgment indices.

## Preservation and comparisons

`StructuralMap` acts on contexts, families, terms and substitutions, preserving the structural primitives and chosen Id/reflexivity. Pair preservation follows from comprehension uniqueness. The implementation recursively constructs telescope, projection, root, tail, motive and branch transport. `ModelMap` adds the primitive chosen full-J preservation law. Identity and composition are constructed and checked. The model builder establishes these primitive laws once; ordinary source authors supply no map laws.

A map may lose information and need not reflect sorting or equality. `PartialHom.eval` therefore preserves expressions whose source evaluation is defined. Source typing supplies that side condition. `TypedMaps` also transports the full hypothesis list when equality assumptions have typed, hence defined, operands. Arbitrary raw Horn equality assumptions can involve invalid terms; they are not claimed to transport automatically. General Horn soundness remains valid with separately supplied premises at each interpretation.

`GuardedJudgmentBoundaries` checks this distinction with a noninjective full map to a collapsed model. A malformed source family substitution becomes well-sorted after the map collapses its indices. This refutes unconditional raw evaluation preservation. The same module assigns two typed family variables equal decoded families in one interpretation and Empty versus Unit in another. Soundness refutes a source equality from typing premises alone. Neither information loss nor agreement in one interpretation licenses reflection.

Specified coherent comparisons have a separate concrete scope. `NativeTypeModel` constructs full contextual J by extending a dependent section along the reflexive-root equivalence, and proves substitution for arbitrary finite telescopes. `CoherentTypePresentations` supplies fiber equivalences over a context equivalence, constructs total-context and dependent-term actions, and proves identity/composition for families and telescopes. Identity types, roots, motives and branches are compared before the actual J result is proved. No input field states the final J comparison.

The concrete comparison flips Bool in `Nat × Bool`, changes `Fin(n+1)` to `Option(Fin n)`, changes two dependent tail families, and changes the motive. `CoherentGuardedJudgments` interprets the same generated command in both assignments: selected 2 in `Fin 4` maps to the specified `some 1`. These are unequal family presentations, rather than just an unchanged family reindexed along a base map.

`NativeDerivedComparisons` constructs the section squares and endpoint comparisons for transport, concatenation, selected η, and the η section varying in its first path. It then derives the comparison for `apd_η(h)` with the transported source in K retained. Its `EtaPresentation` record is builder output containing the independently constructed source and target sections and their proved comparison. Clients do not fill it with the desired result. The last proof-equality steps use subsingleton native identity fibers, so this coherent construction has Type-model scope. The generic strict-map and source substitution theorems have independent scope and apply to path-sensitive supplied models.

## Frozen memo and discriminating applications

| Checked construction | Observation or obligation |
| --- | --- |
| `DerivedPathSemantics` | Exact evaluation of the generated transport, concatenation, η and apd recipes to explicit chosen semantic J values, with constructed root and endpoint conversions. The apd source includes transport of the section's first value. |
| `MemoNormalization` | The contextual package's selected value and certificate equal the direct two-transport and η recipes. The equality preserves the selected certificate itself. |
| `MemoFreshAction` | Reindexing the varying K family and η section agrees with fresh reconstruction; consequently the selected apd and its transported source agree with fresh reconstruction. |
| `FrozenContexts` and `FrozenMemo` | Actual source contexts Γ, Δ, Θ and simultaneous σ, τ are constructed by dependent display extension. All p, p′, h, q and u binders remain typed. Values, families, certificates and dependent action compare under each map, their sequence and their composite. |
| `MemoUniformity` | The selected value, certificate and action inherit strict-map preservation from source typing, including the action and certificate after both frozen substitutions. |
| `GuardedNativeMemo` | The selected source certificate is interpreted in unequal dependent finite-family presentations; selected value 3 maps to `some 2`. The constructed varying-η/apd comparison specializes to those presentations. |
| `GuardedGroupoidMemo` | The same generated memo is interpreted in the integer-action groupoid setting with the actual frozen context. The selected transport value distinguishes 3 from 2 when the first path changes. The certificate remains the selected η recipe. |

The first assignment identifies y with x while retaining the parallel loops and their identity, and replaces q with the retained path r. The second identifies z with x and retains its loop k. `FrozenContexts` derives the component equations and retained-variable laws for these maps. They are actual object substitutions, not substitutions of external metavariable names. `FrozenMemo` then applies the generic source laws to them. In particular, fresh action comparison changes the varying certificate family and selected section together; a merely pulled-back spelling is not the endpoint of the result.

The source concatenation eliminates the right path, whereas the older semantic concatenation eliminates the left. `DerivedGroupoidSemantics` constructs their equality with groupoid composition using discrete identity fibers. This is not definitional equality of recipes, and it cannot identify selected higher certificates in an untruncated model. The new η remains its own explicit J recipe with reflexive branch. Generic evaluation and strict preservation concern that exact recipe. A migration equating it to another selected higher certificate owes a separate comparison.

`GuardedCommandComparisons` exercises the already public substituted-versus-fresh problem. `Command.fresh` builds the reindexed tail, motive and branch, and `substituted_eq_fresh` is generated from J substitution. `substituted_ne_fresh` proves the raw outer constructors differ. The concrete comparison uses the nonidentity map `(n,b) ↦ (n+1,b)` and composes the source equation with the constructed coherent J comparison, retaining code `some 1`. This discriminator neither resumes #107 nor chooses #108's theorem.

The indexed-setting case consumes the independently approved #319 result. `GuardedInternalSetting` authors a nested pair, both projection recovery equations and a two-substitution payload equation before choosing a model. Interpretation supplies actual `Fiber P` and `Fiber Q` over `Total P`; Q depends on the first generic setting. Constructed context, family and dependent-term comparisons are reused. The concrete payload is 6 at 2; reversing the two maps distinguishes 2 from 3 at 0. Settings are supplied semantics and guarded signature assignments here, not newly admitted object-language setting codes.

The higher-model interpretation gate remains open. Source Id/J derivations, the path-sensitive groupoid observation, and native proof-irrelevant equality are three different pieces of evidence. None constructs a concrete higher interpretation retaining the memo's nontrivial second-identity observation. The approved #316 source-only result and separate #321/#322 work retain that boundary.

## Ordinary author work and migration

An ordinary author supplies schematic expressions and source derivations of their context, family, term, substitution and telescope premises. A family over an extension has an explicit different guard from a family over the base. The author constructs the mathematical J motive and branch and proves the required typing. Derived transport, concatenation, certificate and dependent action are then reusable source operations. Substitution, fresh reconstruction and specified strict-map compatibility follow from their proved derivations.

The author does not supply all-model annotations, homomorphism laws, decoded branch alignments, or per-model proofs of the final comparisons. A new model builder supplies operation semantics and proves the admitted rules; a signature assignment supplies primitive data and discharges its guards. For a strict comparison the builder proves the primitive map laws. For the demonstrated coherent Type comparison the builder supplies family equivalences; total contexts, terms, branches and the final J comparison are constructed. These responsibilities differ from compressing the same manual casts into another caller record.

Three costs remain distinct: mathematical source typing belongs to the author; primitive semantic and map laws belong to the model builder; parser checks, transports and expression elaboration belong to the Lean implementation. The frozen context builder factors a general display-square lemma to avoid expanding entire nested contexts during elaboration. This changes proof organization, not the admitted laws or mathematical scope.

Source interpretation is evaluation of a retained finite tree. Inspectable syntax is already in the source derivation's indices. The experiment does not recover syntax from arbitrary semantic values or host functions, invert an interpretation, or prove either extraction round trip. Neither round trip is required by this memo client. Arbitrary compatible sections retain weaker reuse and extraction guarantees than generated derivations.

Migration obligations before retiring the old API are explicit:

- Translate existing annotated derivations with their erasures preserved, or replace named clients individually with checked generated recipes. No universal translator is claimed.
- Recover the existing full structural, conversion, Id/J and arbitrary-tail capabilities. This experiment constructs those in the new source and interprets them in the existing full models.
- Preserve named selected observations, including path-sensitive groupoid behavior. Equality between different selected recipes requires its own comparison; endpoint inhabitation is insufficient.
- Use the [admitted dependent constructor](dependent-constructor-admission.md) from #317 and complete independent ordinary-author observations in #320 before treating this as an established author interface.
- Keep the higher-model gate and its selected second-identity observation open until a concrete interpretation passes it. Native Type comparisons do not authorize retiring that requirement.

## Statement review and validation boundary

Statement review checked that source indices contain no `Model`, that all admitted rules have model soundness proofs, and that typed hypothesis transport includes definedness of equality operands. Full contextual J quantifies over arbitrary finite tails; motive and branch transport use the full reflexive inclusion. The frozen substitutions preserve the parallel paths and h rather than substituting them away. Certificate comparisons concern the chosen terms, and the apd type retains its transported source. Coherent comparison claims state their Type-family scope; groupoid recipe identification states its discrete-fiber scope.

Checked specializations accompany the abstract results: finite dependent pairing, arbitrary-tail J, unequal finite presentations, malformed-to-valid collapse, decoded-equality rejection, actual nested settings, frozen memo substitutions and path-sensitive integer actions. Shared raw-core consumers were rebuilt as a regression. The first complete candidate build exposed five old proofs whose explicit unfolding stopped at the new bind alias; their proof steps now unfold the shared recursive core, preserving their definitions and statements. Focused builds and targeted axiom inspections precede the final committed-candidate build and exhaustive proof audit required by README. The acceptance handoff records exact commits, logs and independent review results; focused success alone is not candidate acceptance.
