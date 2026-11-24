# Issue 705: implementation and use assessment

Retain the selected bridge, with explicit component lemmas and total-arrow examples as acceptance conditions. The existing sources contain the expensive mathematical inputs: arbitrary-map recovery, substitution comparisons, and invertible unit/counit modifications. Mathlib already supplies the total categories, projection, canonical cartesian lifts and recovered fibres. The remaining work belongs in a small general adapter and a specialization; callers should not acquire new coherence fields.

This assessment is independent of the other design reports. I read the selection brief and inspected the pinned project sources and Mathlib checkout. I have not compiled a probe or inspected a proposed implementation. Statements about the proposed adapter below are paper arguments, not checked Lean results.

## Existing capability and obligations

`CoherentFamilyClassification.Coherent` requires a diagram to send every arrow square with invertible right side to an isomorphism (`SquareKit/Internal/CoherentFamilyClassification.lean:18`). Maps in `Code` are arbitrary natural transformations through a full subcategory. `recovery` uses the evaluation arrow whose right side is identity; `recoveryIso` derives naturality in all maps (`:49`, `:66`). The present proposal does not need to strengthen this object condition or restrict maps.

The input condition has a mathematical role, independently of total-category packaging. `Examples/CoherentFamilyClassification.lean:81` supplies `badData`, and `badData_no_recovery` proves that an arrow view cannot be isomorphic to its target identity view. `badData_not_coherent` identifies the failed restriction condition. Keep these results as the loss control; a new abstract axiom saying recovery fails would add no evidence.

`RepresentableCoherentRecovery.lean:19–140` supplies strict indexed functors, `decoder`, `coder`, `classificationUnit` and `classificationCounit`. The decoder comparison uses `decodeReindex`, whose composition and recovery compatibility are proved in `CoherentFamilyClassification.lean:146–156`. Builders already paid these obligations. A caller of the bridge should supply only the existing `C`, `V`, context and family data, then use named total constructions.

Mathlib's `CategoryTheory/Bicategory/Grothendieck.lean:251–267` makes a total arrow from `(Δ,A)` to `(Γ,B)` consist of a substitution `σ : Δ ⟶ Γ` and a fibre arrow `A ⟶ σ*B`. No invertibility condition is imposed on that fibre arrow. `CoGrothendieck.map` (`:334`) keeps the base arrow and sends the fibre arrow through the component functor followed by the strong transformation's naturality comparison. This is precisely the map formula the contract needs. Its functor laws already establish preservation of total identities and composition.

The added capability is access to the ordinary total category and Mathlib's fibre API. It does not make the existing identity-view decoder more general or prove a recovery theorem for arbitrary indexed systems.

## Adapter size and coupling

The missing action on modifications is real in the inspected Mathlib module: it ends after `mapCompIso` and `map_comp_eq`, with no modification lift. The narrow general construction should work for two pseudofunctors on any ordinary base, without importing presheaf contexts or coherent classification.

For a modification `m : α ⟶ β`, its component at total object `(S,a)` should be the vertical inclusion of `(m.app S).app a`. In the general pseudofunctor case that inclusion includes the target pseudofunctor's inverse identity constraint. Mathlib already implements this bookkeeping in `CoGrothendieck.ι` (`FiberedCategory/Grothendieck.lean:87–94`). Naturality then follows from naturality of the component transformation and the modification equation in `Bicategory/Modification/Pseudo.lean:45–59`. An implementation that simply uses the fibre component without its identity constraint would only fit a strict specialization.

Useful public results are the component's base projection, its fibre formula, and identity/composition preservation for modifications. A functor from the category of strong transformations to the category of total functors would make isomorphism lifting reusable via `mapIso`; a direct transformation/iso adapter with those laws is also sufficient. A new general bicategory framework is unnecessary for this contract.

The classification specialization can then compose the lifted unit with `mapIdIso` and `mapCompIso`, and similarly for the counit. Export projection equalities and verticality of their components. `map_comp_forget` (`Bicategory/Grothendieck.lean:364`) already proves strict preservation of the base by both total functors. Exporting only an unqualified equivalence would conceal the over-base contract from downstream callers.

One concrete constructor risk needs attention: `CategoryTheory.Equivalence.mk` replaces its supplied unit by `adjointifyη` (`Mathlib/CategoryTheory/Equivalence.lean:313–342`). If the new public equivalence promises its unit is exactly the lift of `classificationUnit`, use the structure constructor with a triangle proof, or prove the required comparison explicitly. Calling `Equivalence.mk` alone does not establish that component formula. This is a prospective implementation risk, not a defect found in existing code.

Mathlib already provides `IsFibered (forget F)` and `HasFibers (forget F)` (`FiberedCategory/Grothendieck.lean:78`, `:138`). Its chosen fibre is `F.obj ⟨op S⟩`, and its inclusion retains every vertical map. Reuse these instances. Duplicate fibre categories or a bespoke cleavage record would add conversion work without satisfying a missing requirement.

## Cartesian arrows and composition

Mathlib's canonical lift is `(σ, 𝟙)` (`FiberedCategory/Grothendieck.lean:38–42`). Mapping it under a strong transformation gives `(σ, α.naturality σ)`, after the component functor's identity law. Therefore its comparison to the canonical target lift is an invertible vertical map. This supplies a direct and small preservation argument using `IsCartesian.of_iso_comp` (`FiberedCategory/Cartesian.lean:161`). The source and target projections are fibre categories, so ordinary and strongly cartesian arrows can be related using `FiberedCategory/Fibered.lean:101`.

Acceptance should include the claimed general preservation statement or the promised explicit lift comparison and its derived lifting property. Merely instantiating `IsFibered` twice does not relate the two fibrations. Equality of chosen lifts would be an unnecessarily strong requirement: the decoder's substitution law is an isomorphism, and that isomorphism is the vertical comparison just described.

Keep the proof of identity/composition at the total-functor level, then expose usable base/fibre equations. Reproving category laws specifically for coherent families would duplicate Mathlib and couple the bridge to the current implementation of `Code`.

## Discriminating clients

The retained examples are suitable, provided the new examples actually pass through the total functors and recovery transformations.

1. Include the existing `localData` as a total object. Its recovery at `Arrow.mk step` sends `false` to `true` (`Examples/CoherentFamilyClassification.lean:39–47`). This prevents replacing the original twisted presentation by a coded family whose recovery is trivial.
2. Include `collapse` as a vertical total arrow and recover it through the new unit naturality square. The existing proof `collapse_not_iso` (`:58`) establishes that this is a map outside a groupoid. Object recovery alone does not exercise this case.
3. Use the dependent `Fin (n+1)` family with successor and doubling substitutions. In `Examples/NonCubicalClassification.lean`, `double ≫ successor` sends `2` to `5`; the resulting fibre is `Fin 6`. Reversing the substitutions yields `Fin 7`. Assert the actual total composite's base and decoded fibre, rather than repeating only the old `decodeReindex_comp` theorem.
4. Check the cartesian-lift comparison on these substitutions and its ordered composite. Also check one noncartesian total arrow, for example a collapse into a reindexed constant terminal family, so the same map API is exercised beyond canonical lifts.
5. Retain `badData_no_recovery` and the original direct-client examples unchanged. Reference this proved loss control; it need not become an object of the coherent total category, since it fails that category's admission condition.

The current twisted example and successor/doubling example use different contexts. That is acceptable: they discriminate different failures. Requiring all phenomena in one new example would add setup cost without being necessary for the stated contract.

## Direct clients, remaining uncertainty and recommendation limits

`RepresentedLocalFamily.lean:455–591` already exposes its own equivalence, direct reindexing, a strict `toCode_reindex` theorem, and a decoder built by composition with `CoherentFamily.decoder`. These definitions need no migration. Keep the new adapter imports out of the old modules unless a concrete dependency requires them; add the new application module through the agreed aggregate import. This preserves the direct API and avoids making ordinary fibrewise users depend on total-category bookkeeping.

The generic Mathlib `map` signature uses common fibre object/hom universe parameters for source and target. The project definitions infer maxima from `C`, contexts and `V`. Compatibility looks plausible from their construction, but it has not been elaborated here. Check full inferred signatures before acceptance; do not silently lower to `Type 0` merely because all worked examples fit there.

I found no mathematical reason to reject this selected family or add caller hypotheses. The useful correction is to make the over-base component formulas, the exact unit choice, and the cartesian comparison explicit in the implementation contract. The remaining evidence is compilation, statement inspection, original-client validation, and the total-arrow examples above. No implementation cost measurements or general author-productivity advantage are established by this read-only assessment.
