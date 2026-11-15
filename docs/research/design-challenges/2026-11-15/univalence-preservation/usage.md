# Implementation and use assessment for #532

Recommendation: select a bounded observation comparison from closed constant-code native universe loops to host permutations, paired with the existing whole-package comparison for the discrete proof-family fragment. Extend that comparison with a checked rejection of interpreting those loops solely as host equality proofs while preserving their transport. Deliver this as a restricted result, not a witness-preserving interpretation of the native universe. Keep the exact selected native equivalences, inverse homotopies and comparison squares available through the direct route. A broader model-morphism interface has no concrete second builder yet.

This recommendation preserves the required observations in the investigation and identifies where the proposed target cannot promise the full contract. If #532 requires all selected witnesses to move to the target, this route is a negative result for that requirement, with a positive bounded observation result beside it. It must not be called full preservation merely because its host outputs are useful.

## Evidence and independence

Inspected the pinned source tree `/tmp/conaled-wave-20261115/integration`, candidate `188110171d05f6345b6f3833cc959a1a7e414845`, the supplied requirements and brief, architectural guidance, language direction, glossary, ADR index and relevant relations/audit decisions. Source paths below are relative to that tree. Read the reports for #420/#528/#530/#531, preservation inventory, #405 cubical judgment comparison, #446 selected generated comparisons, and #490/#492 evidence comparisons. No other lens report or conclusion was read. No prior implementation involvement is present in this agent's supplied context. No Lean command or external source verification was run. Existing declarations are inspected evidence; proposed additions below are not checked proofs. All recommendations concern the bounded task, not production #489 adoption.

## The actual route and its clients

`Examples/FiniteUniverseLoops.lean:21–46` defines `lowerTransport`, `observedMap`, `observedEquivalence`, and `loopPermutation`. The route starts from a closed section of `paths (code S) (code S)`. It lowers the actual native transport, conjugates with the constant decoder isomorphism, obtains the inverse from the native contractible-fiber witness, and reads closed sections as host values. `DiscreteEquivalences.lean:21–79` implements this last step; `closedSection_eq` uses naturality to the zero-dimensional cube, not a supposition that every native path is host equality.

This is a genuine change in semantic setting at a bounded boundary: native code paths and their transport become arrows of the host permutation group on S; native two-paths become host equalities of those arrows. It is neither restriction along a context substitution nor merely the Fin 3/Phase carrier renaming. It is also not a supplied interpretation of all contexts, universes and type constructors. Naming the bounded source and target is necessary to avoid overstating the result.

The implemented client already supplies decisive observations:

- `loopPermutation_apply` identifies the result with actual transported inputs.
- `permutationMap` recovers the full native transport map from the host permutation.
- `twoPath_iff_permutation` characterizes existence of a native two-path, not equality or recovery of an arbitrary chosen two-path body.
- `loopPermutation_ua`, `loopPermutation_refl`, and `loopPermutation_concat` give ua, identity and the stated ua-input composition cases.
- `booleanLoops_no_twoPath` separates identity from negation, and `compositeLoops_no_twoPath` separates the two orders of Fin 3 swaps.

For the whole package, `Examples/CubicalStructuredState.lean:191–229` accepts the original map f and original `HomotopyEquivalence f`. It derives `admittedIso`, `admittedCarrier`, the exact `uaCode f E` line and its presentation, then returns `uaStructureIdentity`. At lines 301–329, `sourcePackage_eq`, `targetPackage_eq` and `transported_recovery` recover source, conjugated target, and the whole selected filled section. The target `StatePackage` includes selected state, operation, invariant and both proof fields (`Examples/CubicalStateTransport.lean:10–28`). This is a useful package square into ordinary host mathematics, not just a point observation.

The fixed-line restriction matters. `readOut_injective` uses readouts at every generalized point, including Pi values at nonidentity substitutions. `section_initial_injective` then uses the supplied constant presentation. The resulting recovery does not justify replacing arbitrary dependent native functions with their zero-dimensional evaluations. It also does not compare arbitrary carrier lines or recover their selected equivalence witnesses from a host `Equiv`.

## Preservation inventory for this route

| Input | Retained by bounded host comparison | Boundary |
|---|---|---|
| Universe codes and El | Constant code S is observed as S using the existing decoder isomorphism | No target classifier for arbitrary native universe codes, no general El preservation theorem |
| Native paths | Closed universe loops map to permutations; two-path existence corresponds to permutation equality | No general path-family map, no recovery of each selected two-path |
| Used Sigma/Pi | Whole discrete state package survives via `readOut`, `pullPackage`, and section recovery | No preservation of arbitrary dependent Sigma/Pi; all generalized points are needed for the injectivity proof |
| Chosen fillers | The package's actual selected output is recovered in the discrete presented fragment | No equality of universal and constructor fillers and no general filler regularity |
| Equivalences | Actual transport map and its inverse function can be observed as host `Equiv` | Native contractible-fiber witnesses are used but not reconstructed as complete chosen records |
| ua | `loopPermutation_ua` recovers supplied permutation; original E is retained in the native package line | No all-code ua preservation map into an independently constructed target univalent universe |
| Transport | Pointwise permutation action agrees with actual transport; package target equals full conjugation | This is a host semantic equation, not source conversion or runtime behavior |
| Comparison squares | Chosen native square implies equality of target permutations by `twoPath_permutation` | Selected square body is not represented by its resulting Prop proof; no faithful square interpretation proved |

The strongest reason to retain the current native design is exactly that it has stronger observations than this target. `NativeUniverseSquares.comparisonSquare_injective` identifies full two-paths at fixed endpoints from their bodies. `NaturalUnivalenceLaws.composition` at line 185 names the actual `compositeEquivalence`, and lines 229–272 prove recomputation of entire selected bodies under substitution. Those laws are valuable regression tests. They are not consequences of the closed permutation classification, and discarding them would weaken #528.

## Builder and caller work

Direct route-specific laws have the lowest justified setup cost. The builder reuses actual lowering, decoder conjugation, discrete equivalence extraction and package recovery. The caller supplies a closed loop or original f/E and complete package. No caller should rebuild fiber contractions, decide replacement equivalence witnesses, or prove generic universe preservation. Existing `uaStructureIdentity` already absorbs this work for its admitted fragment.

A small interface becomes useful if another target independently implements the same client. It should expose the target observations and the exact transport and package squares it needs. A recovery/reflection capability must be separate from forward observation preservation. Avoid a record whose fields simply demand every desired theorem: it would move the same proof burden to each builder without reusing the construction. Derive selected-input permutation composition from transport observations; do not ask builders for both if one follows from the other.

A broad model-morphism package would need context/family interpretation, coherent comprehension and substitution, universe decoding, path interpretation, the used Sigma/Pi operations, and compatibility of chosen filling and equivalence constructions. Many of these cannot even be stated for the present restricted permutation target as an all-context interpretation. This is an applicability failure, not evidence that a future general interface is mathematically wrong. There is no measured implementation-time comparison here, and no claim that the broad option cannot eventually reduce author effort.

#446 offers a constructive precedent, not a ready cubical adapter. `GeneratedCylinderPrimitive.normalizedPrimitiveComparison_fiber` recovers selected primitive components; `GeneratedCylinderTerms.contextComparison_section` derives the whole-section square from primitive compatible data. Its supported generated groupoid language does not provide a native cubical universe/filler interpretation. Reusing its approach means deriving downstream laws from concrete primitive compatibility; importing the record alone does not discharge #532.

#405 records the missing connection translation when moving to a Cartesian dimension grammar. This makes a De Morgan-to-Cartesian presentation experiment a larger builder task than changing a functor name: the used connections, chosen Kan structure and judgments need their own justification. #490/#492 likewise distinguish transported witnesses and semantic equality from checked artifact formats and foundation morphisms. Their nondependent decoder examples do not supply this missing cubical adapter.

## Smallest new checked experiment

Proposed, not executed:

1. Package the existing closed permutation observation and whole-package target equation as explicitly bounded route-specific comparison theorems. Include the identity/negation and Fin 3 order cases. For the package use the original f/E, then test both the correct finite machine and `wrong_path_rejected`; preserve both proof fields and the invariant, not just the numeric observer.
2. Strengthen composition from ua representatives to arbitrary closed p and q if the existing transport composition lemmas support it. Check inverse observation against the *selected* inverse construction. Do not infer equality of inverse homotopies from equality of inverse functions. This tests useful new composition capability rather than merely renaming #531 declarations.
3. State and prove a negative contract: there is no map from closed Boolean loops into an arbitrary subsingleton target P together with a target action `P → Bool → Bool` whose action at every loop agrees with `loopPermutation`. Apply equality of the images to input true; identity and negation give true and false. Specializing P to a host equality proof type rejects a transport-preserving interpretation through proof-irrelevant equality. The target action compatibility is the explicit failed hypothesis. This does not reject host permutations, which are not subsingleton.
4. Apply `twoPath_permutation` to the *actual* public identity/inverse/composition comparisons. State that it forgets the body, while retain `comparisonSquare_injective` and exact native body recomputation as unchanged native controls. Do not claim noninjectivity of this square observation without two unequal square bodies: the source files inspected do not supply that counterexample.

The negative theorem is more useful than saying preservation needs a contract: it identifies a target shape that cannot support the required Boolean action, and provides a precise alternative, retaining permutations as target arrows. It does not alone complete the whole package experiment or establish all-context functoriality.

## Established limitations, risks and next evidence

Established: existing substitution laws do not change setting; the permutation route retains component classification rather than chosen two-path recovery; the package correspondence is fixed-equivalence and restricted to discrete proof families; native comparison bodies carry more specified data than endpoint equations. Full selected witness preservation is not currently delivered by this route.

Risk: a generic preservation record could either demand an unusable all-model structure from the restricted target, or hide witness loss behind equality in Prop. Another risk is making the successful Fin 3/Phase carrier change stand in for the missing semantic interpretation. Neither is a defect in the existing APIs.

Missing evidence: checked arbitrary-loop composition and selected-inverse observation laws for the proposed route; an explicit Lean separating theorem for subsingleton-target actions; a whole-package client tied to that same bounded comparison presentation; an independently constructed witness-retaining target for broader adoption. The selected inverse and full composite record must remain explicit source data while this work is done. The triple diagram supplies no chosen recomputation law or pentagon to transport. None of these steps needs arbitrary-family inverse #554 for its constant universe-admitted source.

After the bounded experiment, #235 should retain the broader obligation: construct one genuinely different cubical or higher-semantic target with its chosen data, and compare its builder burden against the direct route on these same clients. The discriminating test is recovery or faithfully represented comparison of the actual selected square body and full equivalence witness. A target that only reproduces Boolean outputs passes the bounded observation test but fails to establish that stronger capability.
