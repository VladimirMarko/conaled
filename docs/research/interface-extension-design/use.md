# Independent design assessment: implementation and use

Assessment of the selection brief against source commit `4819b69ca98f5d7f480b75b1a46224faadb64e32` in `/tmp/conaled-issue-704`. This is a design investigation, not implementation acceptance. Source locations below are relative to that checkout.

## Recommendation

Adopt the bounded raw transformation layer and its lawful quotient adapter, subject to checked implementation of the stated contract. Retain the existing Span interpretation route with its supplied comparisons and modifications. Use Mathlib functor categories directly for equality-lawful clients; do not require existing raw clients to migrate to them. Defer a generic displayed/category-of-structures framework until a concrete consumer needs shared machinery beyond these constructions.

The strongest retaining evidence is the existing separation in `SquareKit/CategoryMap.lean:15`: `RawMap` contains object/arrow data, while `MapLaws` separately supplies congruence and preservation. The quotient adapter at line 85 consumes the stronger source/target laws only at the boundary. Raw transformations can add comparisons between these maps without changing existing constructors or forcing raw syntax to satisfy equality laws. `Examples/CategoryMaps.lean:17` already uses semantic association of distinct code trees, and its quotient example at line 28 shows the existing boundary in use.

The strongest evidence for retaining the structured Span route is stronger than pointwise sample agreement. `SquareKit/SpanInterpretationComposition.lean:68` composes supplied strong transformations; line 91 constructs an invertible modification from the complete `Over.postComp` comparison; line 167 composes modifications by whiskering. The associativity and unit results at lines 274, 289 and 306 compare the complete modifications. `Examples/SpanInterpretationComposition.lean:13`, 27, 74 and 90 apply these results to successive interpretations, the selected apex `(3,true)`, dependent payload and reassociation.

## Builder and caller obligations

| Operation or observation | Appropriate obligation and owner |
| --- | --- |
| Transformation components | Builder supplies one target arrow per source object, indexed by the fixed endpoint `RawMap`s. No source or target category laws belong in this data. |
| Naturality | Builder proves the commuting equation modulo the chosen target `HomEquiv`, for each raw source arrow. This is a proposition; it does not supply chosen witnesses of commutation. |
| Identity and vertical composition | Library derives naturality and semantic laws from target unit/associativity/congruence assumptions. Callers should reuse those theorems, without reconstructing the relation chains. |
| Precomposition | Components and naturality are substituted along a `RawMap`. Requiring that map's `MapLaws` would exclude valid uses without helping this proof. |
| Postcomposition | The postmap's congruence and composition preservation transport naturality. Existing `MapLaws` is a suitable supplied package. No source category law is needed. Its identity field is useful for identity preservation, rather than for the naturality transport step itself. |
| Componentwise observation | Library supplies congruence and composition/whiskering laws modulo target relation. Raw record equality remains a separate, stronger observation. |
| Mathlib descent | Adapter caller supplies endpoint map laws and lawful hom quotients, just as for `RawMap.quotientFunctor`. The adapter handles representative induction and natural-transformation extensionality. |
| Selected Span comparison | Builder supplies pullback-preserving functors. The existing library derives canonical apex/action comparisons and coherence. Callers retain full slice objects, arrows, payloads and selected apex observations. |

This allocation keeps data construction usable before law proofs are available. It also lets an author choose a source relation later: transformation naturality is quantified over raw source arrows and uses only the target relation. The existing `RawMap.induced` and `inducedLaws` at `CategoryMap.lean:38` demonstrate that relations need not be fixed when the raw data is constructed.

## Established boundaries and plausible risks

No implementation defect in the proposed new module is established: `RawTransformation.lean` is absent at the inspected base. The following distinguish existing facts from implementation risks.

**Established information boundary.** Equality of descended transformations can characterize componentwise target equivalence for fixed endpoint maps. It cannot establish equality of raw components, recover the original Boolean component of the proposed `Nat × Bool` example, or recover a chosen proof-relevant commutation witness. `HomQuotient.mk_eq_iff` in `SquareKit/Category.lean` already identifies the exact hom observation. Independently, `Examples/WitnessEquivalence.lean` supplies distinct witness-valued squares with equal erasures, and `SquareKit/WitnessEquivalence.lean:17` erases witnesses to `Nonempty`. These controls justify keeping the recovery statement narrow. They do not demonstrate failure of ordinary quotient semantics at its specified observation.

**Established difference between the Span and ordinary contracts.** The Span construction records comparison isomorphisms and modification coherence in addition to object/arrow action. Its proof obligations are discharged from pullback preservation, without finite-limit preservation. The retained examples explicitly accept `second` despite `¬ PreservesFiniteLimits second`, and reject `truncation` by failure of pullback preservation (`Examples/SpanInterpretationComposition.lean`, final examples; `Examples/SpanInterpretation.lean:96`). Replacing this contract with terminal preservation or left exactness would strengthen the admission criterion and lose the existing client. Erasing selected comparison data cannot be justified by the success of the ordinary raw transformation quotient.

**Risk: unnecessary law coupling.** Placing all raw definitions inside a section with source and target law arguments can accidentally make easy operations unusable until unrelated category proofs exist. State the exported types explicitly and inspect elaborated hypotheses. Target laws for vertical composition should not turn into source laws through an overly broad helper interface.

**Risk: adapter boilerplate becomes caller work.** `RawMap.quotientFunctor` uses local `letI` category instances and wrapped objects. Its existing example restates those instances (`Examples/CategoryMaps.lean:34`). A new adapter may multiply this setup if each identity/composition theorem reconstructs it differently. Keep the existing quotient construction canonical and expose component evaluation plus identity/composition preservation lemmas. No additional quotient category or competing lawful-map bundle is needed for this slice.

**Risk: conflating operation extensions with property restrictions.** A full subcategory can restrict existing objects by a Prop while retaining their existing arrows. Supplying terminal/product operations and admitting only preserving maps changes the available data and morphism contract. `SquareKit/CartesianMap.lean` keeps comparison arrows, their inverse laws and terminal/product preservation separate. A generic property filter would not supply those arrows or establish their compatibility. The present assessment inspected that interface, but did not locate and independently assess the brief's specific terminal-preservation counterexample.

**Open usability question.** The proposed raw layer has no retained author trial yet. Shared proofs and an additive module establish a plausible maintenance benefit, but neither the code-tree example nor the NAND example measures repeated author effort. There is no evidence here for migrating the Span clients or for claiming a general productivity improvement.

## Smallest useful correction and discriminating checks

Keep the selected design's scope. Make its public boundary explicit through component evaluation and component-equivalence iff descended-equality theorems, with endpoint maps fixed. Derive identity, composition, whiskering and interchange from the primitive assumptions. Retain the existing Span statements and applications under their original hypotheses. Avoid adding comparison or reconstruction fields that merely assume the intended result.

The proposed `Nat × Bool` case distinguishes semantic laws from raw equality laws and distinguishes quotient observation from representation recovery. Reuse the independent witness-erasure controls to explain the separate proof-relevance boundary. Do not describe the raw Boolean tag as an automatically recovered coherence witness.

To distinguish genuinely weak assumptions from an API that only appears weak, inspect the exported types and, if useful, specialize the non-quotient operations to a source with NAND composition and equality relation, hence without equality category laws, mapping to the one-object additive natural-number target by projection. Natural transformation components can still be natural-number translations. Precomposition should remain available before proving any source laws; quotient descent should require the missing lawful quotient. This is a proposed discriminator, not an executed Lean proof. It can reuse the same raw operations rather than introduce another framework.

For the Span comparison, acceptance evidence should include the existing complete modification equations and their selected-apex/payload applications. A comparison that checks only the base map or only an equivalence of family object types would fail to exercise the retained contract. Existing tests already cover these observations, so reproducing the entire family development adds no evidence.

## Exposure and validation limits

I read the neutral selection brief, repository authority/domain/architecture/formal-development guidance, the relevant current source modules and applications, and prose guidance. I did not read other assessors' reports or the coordinator's research draft, contact other sessions, modify the target checkout, or spawn agents. The checkout's `HEAD` was verified as the pinned commit above.

This report relies on inspected definitions and proof bodies, plus the paper-level derivations stated here. I ran no Lean build or axiom audit and made no new formal claims in the repository. The new transformation implementation, its elaborated hypotheses, its checked examples and its resource costs remain to be assessed when available. Existing checked-source declarations are cited as source evidence; this report does not provide a fresh validation receipt.
