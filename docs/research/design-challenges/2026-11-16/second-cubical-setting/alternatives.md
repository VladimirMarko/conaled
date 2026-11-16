# Alternatives and generality assessment for #574

## Recommendation

Retain the proposed restriction construction as the first bounded semantic comparison. Its strongest feature is that it changes the presheaf base while preserving every cube component, and its native interval path comparison follows from representability. This supports a construction of target contractible-fiber records, including their selected contractions, without first constructing a full Cartesian univalent model. Do not describe that result as preservation of arbitrary target filling operations or target univalence.

Prefer direct proofs for this concrete route, then extract a small interface from the operations actually used. Independently reconstructed Cartesian fibrancy remains a credible next capability, particularly if callers must build new target equivalences and fillers. Its value is not diminished by the lack of an existing adapter. A broad model-morphism interface is premature for this experiment because it adds universe, filling and product commitments that the retained witness argument does not use.

This assessment concerns the construction in the shared brief, not a draft implementation or report. All mathematical comparisons below are paper arguments, not new checked Lean results.

## Why the interval comparison works

Write `i : C → D` for the inclusion, `I_D = y_D(1)`, `I_C = y_C(1)` and `R = i*`. Both cube categories have products given by adding coordinates. Yoneda gives natural bijections

`(R(X^I_D))(n) ≅ X(n+1) ≅ ((RX)^I_C)(n)`.

For a Cartesian substitution `f : m → n`, the action on both sides is `X(i(f × id_1))`. Endpoint evaluation is `X(id_n × ε)`. Thus the comparison respects precisely the substitutions and faces needed for paths. Iteration gives the same statement at `n+2` for squares. This is a representable-power result; it does not require general exponential preservation.

The dependent comparison needs one explicit domain adjustment. There is a natural endpoint-preserving inclusion `κ : I_C → R I_D`. For `B` over `Γ × I_D`, its target family is `(id_RΓ × κ)* RB`, over `RΓ × I_C`. A source relative path over `x ∈ Γ(n)` is determined by its value in that family at `(Γ(projection)(x), lastVariable)` in dimension `n+1`. Conversely, extend that value using the pairing `(f,r) : m → n+1`. This constructs the inverse comparison, with endpoint conditions checked at the two faces. For homogeneous paths this applies to the pullback of the original family along the interval projection.

The local implementation represents paths as natural dependent functions with endpoint equations (`Paths.lean:9–31`), rather than directly as shifted cubes. That changes the Lean proof burden, not the mathematical argument. The future implementation must prove the evaluation/reconstruction inverse laws and naturality, rather than cite Yoneda while leaving the local `PiElement` representation unrelated.

The source `HomotopyContractible` has only `center` and `contraction`, where the latter is a homogeneous path over the total family (`HomotopyEquivalences.lean:116–120`). `HomotopyEquivalence` packages contractibility of the generic-target Sigma/path fiber (`:298–300`). Restriction of comprehension, Sigma, the generic term and the relative path comparison therefore constructs the corresponding target record. It is more than storing an opaque source witness: the mapped contraction is an actual target native path with the required generic endpoint.

`SelectedInverse.lean:16–44` then projects the exact center and contraction to obtain the selected map and its right/left recovery paths. No new primitive inverse-preservation field is necessary. Map the already constructed inverse-equivalence record in the same way. Rebuilding that record using independently selected target fillers is a separate comparison problem.

## The obstruction is valid and narrow

An endpoint-preserving natural map `J = R I_D → I_C` cannot exist. Apply it in dimension one to the source reversal `¬i`. Naturality at the two endpoint substitutions would force its image to have endpoints `(1,0)`. The three Cartesian interval elements in dimension one are `0`, `1`, and `i`, whose endpoint pairs are `(0,0)`, `(1,1)`, and `(0,1)`. None qualifies. The reversal and its equations are actual De Morgan cube operations in `Dimensions.lean`.

This excludes an interval retraction of the required kind. It does not exclude the inclusion `κ`, the dimension-shift path comparison, or homotopy inverses on fibrant target families. In particular, a theorem asserting that all Cartesian paths admit a reversal would fail for the arbitrary presheaf `I_C`: its generic edge has no reversed edge. A target-wide reverse operation therefore requires additional hypotheses; it cannot be derived from bare Cartesian presheaf structure. On the restricted image, source reversal can still be mapped through the path comparison. This distinction is useful for preventing a bounded preservation interface from silently becoming a structure on all target presheaves.

## Package, square and separation obligations

`Examples/CubicalStatePackageFamily.lean:16–85` constructs its package using Sigma and genuine Pi families for the operation, invariant and preservation proof. Two target objects must be distinguished:

* `R(package_D A)`, whose components retain the complete source package data;
* a package rebuilt with target Pi constructors over `RA`.

Restriction alone gives the first. The canonical product comparison to the second comes from restricting the admissible substitutions of a dependent function. It is not licensed as an isomorphism or an injection by the interval-power argument. The smallest useful scope is to retain the first object and its actual `filledPackage` section, while exposing target evaluation and all five fields. If the rebuilt target package is advertised, prove its comparison and the promised recovery separately. For constant/discretely presented carriers, inspect the existing presentation-based recovery proofs before adding a general Pi hypothesis.

For witness separation, restriction on maps and sections is faithful because every object and every generalized element remains present. Distinct source sections cannot become equal merely by dropping naturality equations. For native paths and two-paths, combine that fact with the explicit path isomorphisms. For the code-valued public square, use the twice-evaluated body and the square boundary laws in `NativeUniverseSquares.lean:34–85`. Recovering the original square via its dimension `n+2` generic value prevents loss of source dimension evaluations. No arbitrary dependent-product comparison injectivity claim is needed.

Keep Bool transposition versus reflexivity as inequality of the retained path sections, not a claim that no native two-path exists. Keep the Fin3 control at its actual contract: the wrong presentation fixes the initial state but fails transition preservation (`Examples/CubicalFiniteStateIdentity.lean:95–105`). The expected result is not merely equal initial observations. Freeze concrete source sections, equivalence records and the public square before formal implementation; the brief identifies the consumers but does not itself supply all instantiated inputs.

## Alternatives and their costs

| Route | What it can supply | Additional obligations for #574 |
|---|---|---|
| Restriction with native `I_C` paths | New presheaf base, retained components, derived relative paths and selected witness records | Construct the local path isomorphisms, package comparison scope, and square/composition tests |
| Cartesian fibrant reconstruction | Target-native operations and new target families, equivalences and universe constructions | Select a precise Kan/cofibration structure and decoder; construct a comparison to these source choices and all retained observations |
| Restriction using `J` as interval | Direct retention of the source interval algebra | Does not test replacement by the Cartesian represented interval; conflates two different target interval choices if presented as the current candidate |
| Realization/singular constructions | Another higher semantic setting with independent geometric meaning | Supply dependent-family, code and selected-witness comparisons; ordinary homotopy-type equivalence does not identify chosen square bodies |
| Ordinary groupoid or bijection observations | Useful discrete/composition controls | Cannot be assumed to retain this full higher witness fragment; would need a new argument and may weaken the requested observations |

The Cartesian model manuscript explicitly uses diagonal cofibrations and different generating filling problems. Its treatment of equality cofibrations and Glue, particularly §2.4 and §2.11, explains why source filling cannot simply be renamed: its Glue construction uses a diagonal equality to retain the specified value. The model also supports interpretation over several cube bases under its stated internal assumptions. Thus rebuilding around those capabilities is a substantive alternative, not a syntax repair. It still supplies no comparison with this repository's selected choices by itself. [Angiuli et al., *Syntax and Models of Cartesian Cubical Type Theory*](https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf).

The CSL 2018 theory supplies a different computational presentation, with fibrant and non-fibrant fragments and a cubical partial-equivalence-relation semantics. It is evidence that Cartesian dimensions support univalence, not evidence that this restriction functor preserves a chosen universe. Its operational commitments are unnecessary for the current request, which asks for no evaluator. [Angiuli–Hou–Harper, CSL 2018](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2018.6).

CCHM §§8.1–8.3 distinguish ordinary presheaf families from families with chosen uniform composition. Its semantic path presentation uses a fresh dimension, supporting the dimension-shift calculation above. None of those results identifies an arbitrary target composition choice with the image of a source one. [CCHM v1](https://arxiv.org/html/1611.02108v1).

## Equality and interface choice

Exact equality after specified canonical identifications is appropriate for the mapped source center, contraction and square: it records which data were retained. Strict equality with an independently recomputed target filler is unnecessary unless a retained client uses that equation. A specified native comparison may suffice for recomputation, but its orientation, endpoints, reindexing and composition must be supplied. A mere assertion that the two results are homotopic does not preserve a selected comparison-square body. Comparing two chosen squares can require a higher relative witness, so weakening equality moves an obligation; it does not erase it. The bare target presheaf category supplies no automatic fillers for that obligation.

A small reusable interface should expose context/family/term action, substitution/comprehension comparison, Sigma comparison and relative interval-path comparison with evaluation and endpoint compatibility. Codes and their restricted decoder belong to the selected fragment. Derive generic fiber, contractibility, equivalence, selected inverse projections and iterated square preservation. Introduce an extra filling law only for a promised recomputation operation, not as a prerequisite for mapping an existing filled section. Retain direct client APIs so callers supply their package or equivalence, rather than recreate the semantic comparisons.

The primitive-to-generated approach of #446 is relevant methodology. Its ordinary-groupoid comparison does not directly prove any of these cubical laws. Requiring a broad CwF/universe morphism now would obscure the distinction between preserving selected source outputs and supporting arbitrary target reconstruction.

## Discriminating checks and limits

1. Construct the relative path isomorphism in the actual `PiElement` encoding, including a nonconstant base and both endpoints. Check it under a diagonal and a nonidentity context substitution.
2. Recover two iterated path bodies from their generic `n+2` evaluations. Verify all four public square faces and composition of context substitutions with retained full witness records.
3. Map the exact dependent `filledPackage` section and read all fields. If a rebuilt target package is included, state and prove its separate recovery contract.
4. Test a target path operation on `I_C` itself to reject accidental unrestricted reversal/fibrancy claims. For reconstructed fibrant families, supply the required native comparison rather than importing this rejection as a general impossibility claim.
5. If two interpretation stages are selected, compare their composite with direct interpretation using the canonical product/path comparisons. Do not require a source pentagon or chosen triple recomputation law absent from the frozen source contract.

I inspected local files at HEAD `fae1621cae2d44c788f65400392820d942dabccd`, the live #574 issue and its #554 comment, and #446. I read the shared brief and the named local source/research evidence, without reading the proposed report or other agents' assessments. External evidence was read from CCHM HTML, the Cartesian manuscript PDF text and the CSL publication page; the CSL PDF fetch failed, so no detailed CSL proof inspection is claimed. I ran no Lean builds, formal experiments or model construction, and made no repository or tracker edits. There is no observed implementation defect to report. The unresolved items are construction and scope obligations, with Cartesian reconstruction and broader transport still owned by #574/#235 until explicitly reassigned.
