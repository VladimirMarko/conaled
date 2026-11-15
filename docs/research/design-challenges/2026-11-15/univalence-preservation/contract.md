# Contract and foundations assessment for #532

Source inspected: `188110171d05f6345b6f3833cc959a1a7e414845`, at `/tmp/conaled-wave-20261115/integration`. This is an independent initial assessment. I read the shared brief and full issue requirements, the architectural and language direction, glossary, ADR 0002, the preservation inventory, the four requested univalence reports, and the relevant declarations described below. I did not read another lens report, contact another session, modify the candidate, run Lean, or use external technical claims requiring a new literature search. Source inspection is evidence about declarations, not a new successful check.

## Recommendation

Select a bounded comparison from native closed constant-code loops to host permutations, paired with a precise rejection of interpreting those universe loops as host equality loops. Treat this as a restricted semantic comparison and an obstruction result. The target is ordinary host algebra of bijections and proof-bearing state packages, with permutations as arrows. It is a genuine change of semantic setting for the named observations: native cubical paths and transport become host bijections, actions, and equality of actions. It is neither context substitution nor a relabeling of a cubical carrier.

Keep the full native equivalence records, inverse homotopies, and comparison squares directly available on the source side. The target does not recover all of those witnesses. State this restriction prominently; do not call the permutation observation a witness-preserving interpretation of the entire cubical theory. A restricted/negative #532 result can meet the issue's alternative acceptance route if it proves the failed hypothesis on the actual Boolean client and records the remaining full-witness interpretation task.

The first new checked experiment should be a transport square and a no-factorization theorem, not a general model-morphism record. Use the structured-package comparison as a second positive observation of the same bounded target, rather than reducing packages to their initial state or transition outputs.

## Strongest retention evidence

`Examples/FiniteUniverseLoops.lean:19–43` defines `loopPermutation` from the actual selected universal transport and its actual contractible-fiber witness. `loopPermutation_apply` is the precise evaluation square; `permutationMap` recovers the whole native transport map from that permutation, for this closed constant fragment. This is considerably stronger than a hand-selected Boolean observation.

`twoPath_iff_permutation` at line 83 says exactly that existence of a native two-path agrees with host equality of the permutations. `loopPermutation_ua` at line 91 supplies every permutation, and `booleanLoops_no_twoPath` at line 141 separates identity from negation using transport of true. The classification does not identify native loop terms by host equality. It also does not establish equality of independently selected two-path bodies.

The package target is justified by more than proof erasure. `Examples/CubicalStructuredState.lean:15` proves `readOut_injective` from all generalized-point readouts, including dependent function values at nonidentity substitutions. `observe_injective` and `section_initial_injective` at lines 46 and 58 recover sections in the specified constant-presentation fragment. `uaStructureIdentity` at line 223 compares actual structured path sections over the line constructed using the supplied `f` and supplied `E` with `Preserves (admittedCarrier f E) p q`. `targetPackage_eq` and `transported_recovery` at lines 315 and 326 retain the complete package and actual selected package filling. This is sufficient evidence to retain the native APIs unchanged and reuse their host package boundary.

The hypothesis supporting exact package recovery is the discrete presentation, not a general collapse of native identity. The native proof fibers are PLift propositions, and the injectivity proof recovers dependent function data. A new package with higher proof-relevant witnesses would require a new argument.

## Concrete route and preservation inventory

Use the following target fragment, initially without constructing a general category of models:

* A named constant code for a host carrier S is observed as S.
* A closed native loop p at that code is observed as `loopPermutation p : S ≃ S`.
* A native two-path is observed as equality of those permutations, using `twoPath_permutation`.
* A discrete structured package is observed as the entire `StatePackage S`, and a structured path over an admitted equivalence is observed through `uaStructureIdentity` as the specified whole-package preservation contract.

A one-object groupoid with arrows `Equiv.Perm S` is a mathematically valid target packaging of the loop observations. That packaging has not been constructed or checked here. The already inspected declarations suffice to describe the comparison without assuming a universal groupoid model of cubical type theory.

| Source capability | What this target retains | What is not established |
|---|---|---|
| Universe codes and El | Named constant-code carrier and its actual transport action through decoder/raising adapters | No map of the entire universe of codes, no universal decoder interpretation, no resizing |
| Native paths | Closed constant-code loops become permutations; native two-path existence is reflected and preserved by permutation equality | No host equality between carriers as the interpretation of these loops; no recovery of chosen higher-path bodies |
| Used Sigma/Pi | Full admitted state package and fixed-equivalence preservation relation, using existing iterated Sigma/Pi implementation and injectivity | No arbitrary dependent sum/product preservation, no arbitrary varying-family interpretation |
| Chosen fillers | Their resulting transport maps and admitted package sections have the stated observations and recovery | No target chosen Kan filler or operationwise filler-preservation theorem |
| Equivalences | Host bijection derived from actual selected native contraction | No recovery of the entire native contractible-fiber record from a host `Equiv` |
| ua | `loopPermutation_ua` recovers the supplied permutation exactly | No interpretation of all native ua codes or source conversion rules |
| Transport | Exact host equality of the observed output with permutation application | No unconditional equality of selected native fillers or regularity |
| Selected composite record | Its map action can be observed; native record remains supplied to native comparison | No target reconstruction of all fiber contractions |
| Selected inverse/homotopies | Discrete inverse action and host inverse equations can be derived from native homotopies | Native homotopy bodies are not retained as target data |
| Identity/inverse/composition squares | Their images give host equalities of the specified permutation actions | Host equality proofs cannot serve as faithful encodings of complete native two-path bodies without an additional theorem |

Do not infer that because source equivalence witnesses are natively proposition-like, their records are host equal. `EquivalencePaths.ofHomotopy` deliberately uses native proposition structure rather than host proof irrelevance on contraction data. Similarly `NativeUniverseSquares.comparisonSquare_injective` concerns equality of the complete square body at fixed endpoints, not equality of observed permutations.

## Decisive experiment

Positive square, already almost present: for each closed loop p and s : S, observe the actual `pathToMap p` at `nativeInput s` and prove that it equals `loopPermutation p s`. The existing `loopPermutation_apply` states this exactly. Add a bounded route API only if it helps consume this equation with the negative control and the package comparison.

Negative square, proposed and not run: let B be the closed native Boolean loop type, let p₀ be `booleanIdentityLoop`, and p₁ be `booleanNegationLoop`. Suppose an erasure `erase : B → Q` satisfies `erase p₀ = erase p₁`. Then there is no `act : Q → Bool → Bool` satisfying

`act (erase p) b = loopPermutation p b`

for every p and b. Substitute p₀, p₁ and true; use `loopPermutation_refl`, `loopPermutation_ua`, and `true ≠ false`. This is an exact failed hypothesis, with no appeal to generic skepticism about erasure.

Specialize Q to a host equality loop `C = C`. Lean's proof irrelevance gives `erase p₀ = erase p₁` for every such erasure. Thus interpreting the universe paths as host equality loops cannot preserve their Boolean transport action. The observation obstruction is stronger and clearer than merely noting that host equality proofs are subsingleton. A target set of permutations does not suffer this obstruction: being set-valued is not itself the defect. Collapsing the two observed loops is the defect.

Retain a package rejection alongside it. `Examples/CubicalFiniteStateIdentity.lean` already rejects the wrong presentation that fixes the chosen point but sends the transition to the wrong state. Use the full `Preserves` contract and `wrong_path_rejected`; an observer of only the initial state would pass this faulty map. The positive whole-package square is `targetPackage_eq` with all fields of `StatePackage`, not merely the ready-state observation.

These experiments establish a useful boundary: the permutation target retains the Boolean distinction and complete specified discrete package observations; the host-equality-loop target cannot retain even the Boolean transport action. They do not establish a target retaining arbitrary selected contraction data and square bodies.

## Laws derived versus laws still owed

Derived from inspected constructors:

* Host inverse laws for constant-family equivalences follow from the actual fiber center and native contraction, through `DiscreteEquivalences.leftInverse/rightInverse` and discrete-path rigidity. They should not be new caller fields.
* `HomotopyEquivalence.discreteIso` derives the isomorphism for path-discrete admitted carriers; its forward map is exactly f. `admittedLine` still uses the original E. Do not replace E with `ofIso` in order to ease target construction.
* Identity transport observation follows from `reflexiveTransportComparison`, without strict filler regularity.
* Equality of permutation actions under native two-paths follows from `transportTwoPath`, the constant observation map, and discrete rigidity.
* Exact package recovery follows from the stated section injectivity and original filler endpoint law. It is not an extra axiom about all packages.

Still owed for a broader bounded groupoid comparison:

* `loopPermutation_concat` currently quantifies over loops of the form `equivalencePath e` and `equivalencePath d`, not arbitrary closed p and q. A general composition theorem is plausible from actual dependent transport composition and observation; it must be proved before claiming a functor on all closed loops.
* General reversal/inverse observation must refer to the actual selected inverse from compositional univalence. Comparing only `Equiv.symm` of an independently supplied bijection would miss the selection requirement.
* Reflection currently concerns existence of a native two-path, not recovery of a selected two-path. A full-witness target needs an explicit interpretation of the latter.
* A genuine change of cubical presentation needs preservation of the interval/face operations, the relevant dependent constructors, and chosen filling before deriving preservation of constructed ua. Context-substitution equations do not discharge these new obligations.

The triple diagram supplies its existing two-path and boundary laws. No chosen recomputation naturality or pentagon should be inherited by the proposed route.

## Interface comparison

Direct route-specific laws are the smallest useful option. They name exactly the closed-loop action and full package observations, expose the rejecting host-equality target, and keep the native APIs usable. Their main limitation is scope, which can be stated and checked.

A small preservation interface becomes justified if a second concrete route consumes the same law. It should describe the action on the relevant indexed data and the observation square, with separate reflection fields where needed. It should not demand all chosen native witnesses from targets intended only to preserve permutation actions. Conversely, an interface containing only the action square cannot advertise preservation of full equivalence records.

A broader model-morphism package could provide genuine constructor-level transport and thereby derive preservation for whole constructions. It requires a concrete target and laws for the operations used. No inspected constructor establishes those laws for a new cubical presentation. Introducing fields named `preserves_ua` and `preserves_univalence` would merely move the goal to builders unless the construction derives them from smaller structural premises.

The #446 result is useful discipline: its selected context and family comparisons derive section and counit squares from primitive coherent data, and distinguish reflection hypotheses from preservation. Its generated groupoid/J contract is not a map of these cubical universes. #405 explicitly leaves chosen Kan preservation open under cube-category restriction. #490/#492 distinguish judgment preservation and witness adequacy from validity or host checking. None supplies the missing cubical interpretation.

## Concerns, missing evidence, and next step

Established limitations are the absent target interpretation of selected Kan fillers and higher witness bodies, the restricted quantifiers of the current concatenation theorem, and the incompatibility of collapsed Boolean loops with the specified action square. The last claim is a paper proof here, proposed for checking; its source separation theorem is already present.

A plausible risk is that packaging the finite permutation classifier as a model morphism obscures these limitations. Another is asserting target witness equality because its equality proofs are propositions. This does not prove that the source selected witnesses are equal. Neither risk is an established defect in the current native implementation.

The smallest next step is to check the negative factorization theorem and positive action/package squares, then generalize composition and the actual selected inverse action for the closed constant-code fragment. Retain full native witnesses as explicit untransported source data. Schedule a distinct full-witness comparison task only after selecting a target capable of expressing those witnesses. A De Morgan-to-Cartesian restriction experiment is a candidate, but would require proof of the relevant chosen filling transport, not a presumed consequence of precomposition.

This report proposes no new kernel axioms, strict regularity, arbitrary-family inverse, production evidence interface, source conversion preservation, execution claim, or higher coherence claim. No parent-preferred route was disclosed to this lens. The conclusions are based on pinned local declarations and the shared task constraints; no experiment or independent acceptance run is represented as completed.
