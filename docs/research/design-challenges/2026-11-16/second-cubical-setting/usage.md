# Implementation and use assessment of #574

## Recommendation

Proceed with the bounded restriction construction, first as direct laws and then as a small derived interface. The construction described in the shared brief has a credible mathematical route to complete target contractible-fiber records, selected inverse homotopies and the selected code-valued square. It is stronger than retaining carrier bijections. Do not describe it as a morphism of full fibrant models, or as recomputation by independently selected Cartesian fillers.

The decisive local fact is the actual shape of `HomotopyContractible` and `HomotopyEquivalence`. A contraction is a section of a homogeneous path family over comprehension, and an equivalence is that data for a generic Sigma/path fiber. These definitions do not demand preservation of arbitrary dependent products. The package has additional Pi fields, so its exact interpretation must be stated separately.

This is a research recommendation with paper-level derivations. No Cartesian implementation, Lean proof or build was executed.

## Evidence and frozen consumers

I checked that HEAD is `fae1621cae2d44c788f65400392820d942dabccd`, with no differences in the inspected Cubical modules or the two named package/machine files against that revision. References below name declarations at that revision.

Freeze the following inputs before implementing a comparison:

1. Use `CubicalStatePackageUa.successorLine`, `successorLineIso`, and `transportedPackage = filledPackage successorLine successorLineIso oddPackage` as the actual dependent package. Its initial endpoint recovers `evenPackage`; its final endpoint recovers `oddPackage`. `CubicalStatePackageFamily.package` contains initial state, endomorphism, invariant, initial-validity proof and preservation proof. The latter fields depend on the earlier data; they are not a tuple of fixed host observations. The two proof fields are PLift propositions, not arbitrary higher proof objects. Retain the selected section, all generalized components and both endpoint presentations, not only `finalPackage_eq`.
2. Freeze `FiniteUniverseLoops.swapComposition`, including `nativeMap swap01`, `nativeEquivalence swap01`, `nativeMap swap12`, `nativeEquivalence swap12`, the exact `compositeEquivalence` consumed by `NaturalUnivalenceLaws.composition`, and `NativeUnivalence.comparisonSquare swapComposition`. The orientation is swap01 then swap12. The retained controls send 0 to 2 and, in the reversed order, 0 to 1.
3. Retain `booleanIdentityLoop`, `booleanNegationLoop` and `booleanLoops_no_twoPath`, plus the Fin3 `compositeLoops_no_twoPath` control in `Examples/FiniteUniverseLoops.lean`. Keep `CubicalFiniteStateIdentity.wrong_initial`, `wrong_transition` and `wrong_path_rejected` as the structured-state control: the wrong bijection fixes the initial state but does not preserve its transition.
4. For arbitrary family equivalences retain `E.fibers.center`, `E.fibers.contraction`, `E.selectedInverse`, `E.selectedRight` and `E.selectedLeft`. Where inverse fibers are requested, map the source-selected `selectedInverseEquivalence E FA hFA FB hFB` with its actual supplied lawful fillers. Keep the universe-selected inverse in `NaturalUnivalenceLaws.inverse` separately named; the source does not identify all such independently selected witnesses.

The relevant code is `HomotopyEquivalences.lean:116–138,161–189,298–312`, `SelectedInverse.lean:16–43,136–143`, `NativeUniverseSquares.lean:34–76`, `NaturalUnivalenceLaws.lean:185–195,253–274`, `CubicalStatePackageFamily.lean:16–108,310–340`, and the named declarations in `CubicalStatePackageUa.lean` and `FiniteUniverseLoops.lean`. `TypeFormers.PiElement` explicitly quantifies over every source substitution; this matters for the package boundary below.

## Why full fibers are derivable

Write R for restriction along the identity-on-objects inclusion C→D. For a family A over Γ, its restricted family has the same fiber at every `(n,x)`, with naturality restricted to C arrows. Thus total spaces, pairing, projections, generic elements, Sigma, and the actual components of source sections survive directly. Different source sections remain different because every object and component remains available. This is faithfulness on the source data, not fullness or reconstruction of arbitrary target sections.

Both cube categories have finite products, with n×1 represented by n+1. At `(n,x)`, an interval section is determined by its value at the generic extra coordinate over `Γ(projection)(x)`. Conversely, restrict that value along the tuple `(f,r)` to evaluate at a generalized base substitution f and interval coordinate r. The same construction in C and D gives the relative path comparison. Endpoint conditions are restrictions along the two last-coordinate faces. Naturality is substitution by `f×id`. These are the concrete maps and equations to prove; citing preservation of arbitrary exponentials would be unnecessary and unjustified.

For a genuinely interval-dependent B, state the comparison with the target family pulled back along `RΓ×I_C → R(Γ×I_D)`, induced by the canonical inclusion `I_C→R(I_D)`. This avoids silently treating these two interval contexts as equal. For homogeneous paths, it specializes to the path family of RA. Applying this twice gives the square comparison.

Now construct the target fiber through the Sigma and relative-path comparisons, transport the restricted source center into it, and transport the restricted contraction over its comprehension. This supplies a target contraction defined on every generalized target fiber element. It is a constructed target equivalence record, rather than merely an uninterpreted field containing the source record.

The selected inverse is a first projection. The right homotopy is the center's second projection. The left homotopy evaluates the contraction at `(a,refl)` and projects its first component. Consequently their preservation follows from the primitive comparisons for pairing, reindexing, Sigma projections, reflexivity and path application. They should be derived lemmas, not builder-supplied final preservation fields. The previously constructed inverse equivalence can be mapped in precisely the same way; reconstructing it afresh with Cartesian Glue/filling is a different obligation.

## Package boundary and square retention

There are two materially different package statements:

- `R(package A)` retains the exact source package elements, including their complete source Pi data. Restricting the actual `filledPackage` retains its chosen values, and restricted evaluation/readout maps retain the five fields and their proof dependencies. No general Pi comparison injectivity is required.
- A package rebuilt as Cartesian Sigma/Pi constructors on RA requires comparison maps for those constructors. Restricting a source Pi element gives a target Pi element by keeping its values at C substitutions. Its general inverse and injectivity do not follow from the construction above. Do not replace the first statement with the second without evidence for the named package.

The first statement is useful: it supplies an actual dependent family and selected filled section in the second presheaf setting, with target maps that expose its fields. It does not say that its Pi fields classify all target dependent functions. A facade can expose restricted readout/evaluation without asking package callers to understand the source Pi representation. If a native Cartesian package is promised, make it an additional scoped theorem and test that exact statement.

Similarly, the square should be compared after the two canonical interval-context inclusions. `comparisonSquare_injective` already establishes that a source two-path is determined by its whole body. The relative path isomorphisms and their iteration give the needed reflection for the translated path data. Componentwise restriction preserves selected sections. This provides a route to retaining full chosen data without an assertion about arbitrary dependent products.

For closed Boolean and Fin3 controls, C's zero cube represents the terminal context. Closed target paths and two-paths in these restricted families are therefore read at dimension zero; the path comparisons identify them with the corresponding source elements. This is stronger evidence for retaining the no-two-path controls than faithful restriction alone. Faithfulness by itself would only preserve inequality of selected terms, not rule out newly available target homotopies in an arbitrary context.

## Interface and obligation comparison

| Route | Builder obligations | Ordinary caller obligations | Assessment |
|---|---|---|---|
| Direct restriction laws | Define C, inclusion, restricted elements/families and sections; prove comprehension/Sigma equations and relative path isomorphisms with evaluation, endpoint and substitution laws | Supply the existing source family, maps, selected witnesses and sections; choose which retained output to observe | Best first implementation; small proof surface and exact dependency evidence |
| Small derived interface | Package the preceding constructed operations and coherence; derive fiber, contraction, inverse, package-view and square laws | Supply the same source inputs; obtain translated records through named operations | Useful once the direct derivation fixes the necessary laws; prevents repeated casts and endpoint alignment |
| Broad model morphism | Target fibrancy/cofibrations, chosen filling compatibility, universe/code admission, appropriate dependent constructor laws and possibly weak coherence | Often additional target admission/filler choices even for this bounded client | More capability than the present clients need; no evidence yet that its preparation or migration cost is justified |

The small interface must distinguish a primitive law from a derived final theorem. It should not ask for `preservesEquivalence`, `preservesSelectedInverse` or `preservesComparisonSquare` as unexplained assumptions when these follow from the selected primitives. Codes can be `R(smallFamilyCodes)` with restricted decoding. This is a named family of codes; neither classification of all target fibrant families nor arbitrary target univalence follows.

#446's useful method is to derive whole section squares from primitive coherent data, as documented by `GeneratedCylinderTerms.contextComparison_section` in `docs/research/signature-cylinder-comparison.md`. Its groupoid/J construction is not a ready-made cubical adapter. Preserve ordinary native callers: this experiment should add translated clients without requiring old clients to build model morphisms.

## Concerns and smallest corrections

**Established scope limit:** the target representable interval has no endpoint-preserving natural map from J=R(y_D1). At dimension one, reversal in J has endpoint values 1 then 0, whereas I_C has only 0, 1 and the variable. Naturality at the two faces contradicts every candidate. This obstructs that direction of interval identification, not the path-power comparison. Use the available map I_C→J in interval-dependent statements.

**Plausible implementation risk:** the repository aliases `Context` and `Family` directly to its fixed `Cube`, so no existing cross-base instance can simply be filled in. A bounded target presheaf module and comparisons will be necessary. Avoid a wholesale generalization of the existing fibrant library before the small experiment proves useful. Some equalities may require canonical isomorphisms and endpoint transports in Lean even when their components agree mathematically.

**Unproved extension:** source-selected filled sections restrict, but a filler for every Cartesian box has not been constructed. Likewise, mapped source composition and inversion records are not established equal to records independently recomputed by target fillers. The smallest correction is to name the mapped selected operation explicitly. If target-native recomputation becomes a requirement, ask for a coherent native comparison first; exact equality of all chosen fillers has no demonstrated consumer need here.

**Discriminating tests:** prove the relative path comparison with nonconstant base Γ and genuinely dependent B; instantiate the exact successor package and both proof fields; derive both selected inverse paths from the same E; compare `swapComposition`'s whole body and all four boundaries. Test composition by performing restriction followed by a named Cartesian substitution versus the direct composite, retaining center, contraction and square, rather than checking only maps. Do not add a pentagon or chosen triple recomputation claim absent from the source.

These tests are schedulable formal construction work, not missing premises to hide inside a record. The report does not claim #574 has a checked realization yet.

## Sources, exposure and validation limits

I inspected the shared uncommitted brief, the issue body and its #554 completion comment through read-only `gh issue view`, the pinned local declarations cited above, and the local #405/#528/#530/#532/#554 and #446 records. I read the architectural, language-direction, domain and development guidance. No tracker writes or repository edits were made.

I opened the primary publication pages for [CCHM v1](https://arxiv.org/abs/1611.02108v1) and [Angiuli–Hou–Harper CSL 2018](https://doi.org/10.4230/LIPIcs.CSL.2018.6). Their existence and differing foundations do not supply this comparison. I do not rely on an external theorem that restriction preserves Cartesian fibrancy or univalence. The derivations above are explicit mathematical arguments for the specified finite-product cube categories, requiring formal realization and review.

No current main report or another current lens report was read. A broad text search for #446 incidentally returned short snippets from the older 2026-11-15 challenge reports; this is limited historical exposure, not complete isolation from all earlier assessments. The current recommendation assesses the construction in the supplied brief. No subagents were delegated, no Lean command was run, and no build or proof-audit result is claimed.
