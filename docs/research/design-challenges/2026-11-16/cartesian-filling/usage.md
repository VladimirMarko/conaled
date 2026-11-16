# Implementation and use assessment of #600

Retain the presented-discrete construction as the smallest useful implementation. Retain the nerve and Q construction as a bounded research extension, subject to the explicit coherence and representation adapters below. Do not mark the selected-square requirement complete from equality after Q alone. The frozen #574 target is RU, and its retained square contains the original code-valued body. The proposed nerve equality lives in a different target and does not yet connect an independently recomputed square to that retained body.

This is a contract gap, not a counterexample to the nerve filler or a proof that the stronger comparison is impossible. The strongest evidence for the proposal is that its package application uses an actual globally discrete presentation of the exact admitted ua line, and its transport triangle can use an existing dependent square-lifting operation with the needed input sections.

## Evidence and exposure

I inspected source using `git show` at `4c81050dd2844c39bcfc551426f1e1cdbe3bcac1`. All source locations below refer to that revision, not concurrent #599 edits. I read the neutral brief, proposal, transport addendum, repository architecture/domain/environment guidance, the design-challenge instructions, the counterexample/scope guidance, and the relevant existing definitions. I had no previous involvement in this investigation and did not read other reviewers' reports or `contract.md`. I used the no-ai-slop skill for this report. No external manuscript was independently inspected; no external theorem is needed for my conclusions.

Inspected input SHA-256 hashes:

- `challenge-brief.md`: `f962444ec1f6c85652979a4572ebe3ff6ffee0e145e53c5123f6b082e5244f67`
- `proposal.md`: `86bb2558a0ed55255ce17a14e57a7aed18e2e0f9310030d5ce7312fedbdfc76b`
- `transport-addendum.md`: `07923de8cf70b059ff665864de8505be6775613cd2160ea230f2b58aae2fe0a5`

The evidence here is source inspection and paper derivation. I compiled no new Lean claim, ran no build/audit, and performed no executable finite experiment. Existing declarations below are inspected Lean source, not declarations revalidated during this review.

## Exact consumers and the minimal useful construction

The package is genuinely dependent. `Examples/CubicalStatePackageFamily.lean:16–25` builds the carrier, endomorphism and predicate data using Sigma/Pi; `:62–63` uses `PLift p` for proof fibers. `pullData` at `:171` supplies generalized function values at every substitution, `pullPreserves` at `:213` uses the Pi reindex isomorphism, and `pullPackage` at `:222` assembles the whole value. `package_ext` at `:156` removes proof-field ambiguity only after the dependent data agree. The proposal's five-field count matches the actual structure; some source comments saying “six-field” are stale comments, not an extra field.

The exact carrier line is `CubicalStructuredState.admittedLine` at `Examples/CubicalStructuredState.lean:207`; its natural presentation is `admittedPresentation` at `:213`. It uses the supplied equivalence record E through `uaPresentation` (`:169`), so replacing E by a convenient canonical witness is unnecessary. `filling_recovery` at `:75` proves whole-section equality from the initial boundary; `transported_recovery` at `:326` applies it to the exact `filledPackage`. This is stronger and more useful support than the endpoint observation theorem alone.

The concrete Fin3/Phase client fixes `presentation`, `machine` and `nativeEquivalence` at `Examples/CubicalFiniteStateIdentity.lean:19`, `:25`, and `:53`. The machine's invariant is `n ≠ 2`; `machineTransported_eq` at `:73` identifies its complete endpoint package. The acceptance cases should retain ready-valid/failed-invalid (`:81`) and rejection of `wrongPresentation` (`:88–115`), alongside next-state observation 1 (`:77`). These distinguish a package theorem from preservation of its initial point or a bare carrier bijection.

The smallest implementation therefore needs:

1. A Cartesian interval and diagonal-aware filling signature, with arbitrary source r and target s and agreement on r=s.
2. A constructor taking a natural presentation `A ≅ ΔS` and deriving its chosen all-box filler, lawfulness, uniqueness and substitution laws. The presentation is useful input; the final comparison theorem must not be another required input field.
3. A specialized natural package presentation and inverse to the target Pi comparison for this fragment. At a generalized argument over f:y→x, use the carrier presentation to pull that argument back uniquely to x; Pi naturality then reduces its value to identity evaluation. Prove that this agrees with the canonical forward restriction comparison, including abstraction/application and the proof dependency casts.
4. A theorem equating the image of the actual `transported` section with independent target filling. Use source `transported_recovery`, preservation of `pullPackage`, and target filler uniqueness. Add the endpoint presentation equations from `CubicalStructuredState.lean:261` and `admittedPresentation_one` to identify the Fin3/Phase endpoints.

This construction serves both the finite client and the existing even/odd specialization (`CubicalFiniteStateIdentity.lean:117–126`). It should not require a finite classifier: `StatePackage S` includes Prop-valued fields, and the proposal correctly permits arbitrary discrete sets for the package.

## Full equivalence records need a derived uniqueness adapter

`HomotopyEquivalence` contains actual contractibility data, not a Prop certificate. `SquareKit/Internal/Cubical/HomotopyEquivalences.lean:116–119` stores a center and a Type-valued native contraction; the equivalence structure is at `:298`. `DiscreteEquivalences.closedEquiv` (`DiscreteEquivalences.lean:67–75`) explicitly classifies observations rather than full witnesses. `PathDiscrete` (`:84–95`) only states equality of path endpoints. Neither declaration by itself proves equality of path bodies or complete equivalence records.

The proposal has a sound route to the stronger conclusion for presented constant endpoint families: prove that every generic fiber element of a bijection is unique, and that the homogeneous path family in such a fiber is pointwise subsingleton. Extensionality then gives uniqueness of centers and contractions, including all generalized arguments. This is an outstanding derived lemma, not a defect in the mathematical idea. Do not replace it with proof irrelevance for `HomotopyEquivalence`.

Apply it to the exact `compositeEquivalence` (`CompositionalUnivalence.lean:151–157`), which is E.comp D using three selected decoder fillers. Apply it separately to the universe-selected inverse (`:206–230`) and the center-selected inverse from #554. The former is transport along reversed ua, with its own `pathToEquivalence`; it is not defined as the inverse extracted from E's center. The two maps can coincide in this discrete fragment, and then their whole records and homotopies can be compared by the derived uniqueness result. First align the underlying families/maps using the restriction/path/fiber adapters; a bare equality between records in different presentations is ill-typed.

## All-box and coherence checks

The discrete filler argument works on arbitrary subcontexts, including a diagonal tube: after applying e, the entire section is constant in the newly added interval coordinate. Agreement at the graph r forces agreement throughout the tube. This also gives source=target for equal interval terms on a subobject, not only for literally identical expressions. Its usefulness does not depend on a source lift of the target box.

For the nerve formula I found no contradiction in the required diagonal, repeated-variable or varying-r cases. At each vertex (v,z), w_v(r_v) is identity even when r varies with v. Thus the source graph has arrows B_vw, not merely correct objects. The formula `w_w ∘ B_vw ∘ w_v⁻¹` satisfies the functor equations by cancellation. A substitution duplicates/selects vertices, and every membership test uses the pulled-back subobject, so its cases agree with precomposition.

The subtle all-vertices case is not a failure of this construction. For example, over an interval the subobject `(x=0) ∨ (x=1)` contains every closed vertex without containing the generic interval cube. One must not infer a generic tube element from this. Instead, the filler is an actual functor on the vertex groupoid by the formula above. To prove agreement on a tube cube indexed by h:m→n, use the actual tube functor at h and compare its objects and arrows; each of its vertices belongs to φ, and functoriality plus source agreement determines precisely the formula's arrows. Vertex objects alone would not suffice, but vertex objects together with every arrow do. The same reasoning applies to diagonal subobjects and their intersections.

The transport addendum identifies a real source tool. `DependentTransportComposition.lean:373` constructs `squareLift` while preserving the two specified side sections; `:385–400` returns the upper transport comparison, and `:407–430` supplies whole-lift/upper-body reindexing. For the proposed conditional square, take s as the outer lifting coordinate and t as the inner path coordinate. At s=0 the conditional equals canonical(v,a)(t), and at s=1 canonical(v,w)(t); at t=0 it is v, and at t=1 it is canonical(a,w)(s). Thus the library's “left/right/bottom/top” convention is met by taking its inner path coordinate to be t and outer lifting coordinate to be s: left v, right a→w, bottom v→a, top v→w. The forward bottom section and forward right section supply exactly the inputs required by `squareComparison`.

The remaining work is explicit and plausible: endpoint casts, `pathToMap_along`, decoder reindexing, lowering/raising, and conversion of the resulting path to equality in the discrete endpoint family. `CompositionalUnivalence.lean:169–194` already demonstrates use of `pathToMap_along` to relabel transport comparisons. `NativeUnivalenceComparison.lean:29–36` retains complete chosen endpoint equivalences in its ua comparison. These support the proposed approach; they do not constitute an implemented Q functor or a checked Q composition law.

One representation detail must be fixed in the theorem statement: Q's object is the closed-element set of a decoded vertex code. For `code (Fin 3)` this is canonically isomorphic to Fin3, not definitionally the same object of the finite-set groupoid. Either recompute the target square on those actual Q objects, or conjugate via the specified decoder/closed-section equivalences. Otherwise the advertised literal equality to a square on the object Fin3 has mismatched endpoints. The same adapters should state the universe levels and finiteness witnesses without silently resizing lifted decoded fibers.

## What the square comparison does and does not establish

`FiniteUniverseLoops.swapComposition` (`Examples/FiniteUniverseLoops.lean:188–190`) fixes the actual natural composition comparison for swap01 then swap12. Its whole-body substitution theorem is at `:197–202`. `NativeUniverseSquares.comparisonSquare` (`:34`) has an injectivity theorem at `:43`; the four faces are at `:56–75`. The accepted report fixes RU as target (`docs/research/second-cubical-witness-preservation.md:203–207`) and retains this exact body, not an arbitrary square with its endpoints (`:235–244`).

After the proposed Q coherence proofs, Q maps that actual body to a nerve functor. Boundary determination in the nerve then proves equality to the independently recomputed nerve square, with orientation and substitution. This is a real whole-target-element theorem, stronger than checking 0 maps to 2. It also preserves Boolean identity/negation separation and Fin3 order, matching `FiniteUniverseLoops.lean:140–148` and `:164–183`.

However, Q observes objects and transport arrows, so its boundary determination cannot establish injectivity on source code-valued bodies. No inverse to Q, decoder comparison back to RU, or relative three-path in RU is supplied. Consequently it does not yet discharge recomputation of the retained #574 square in RU. The proposal itself acknowledges this. The defect would be calling the nerve equality completion of the unchanged stronger contract; the nerve equality as a separately named bounded result is legitimate.

A discriminating next theorem is to type the desired comparison before building more interfaces: supply a target recomputed square in RU, or a specified classifier/decoder map from the nerve to RU, and construct a native comparison with the retained square that fixes all four faces. Then prove its reindexing law and identify its exact endpoint squares. Failure to derive this from the nerve alone is an open construction obligation, not an impossibility theorem. Conversely, if adoption explicitly selects the Q-image contract, state that change and keep faithful source-body retention under #599 as a separate capability. Do not silently substitute it for the retained-square contract.

## Recommended sequence

Implement the presented-discrete filler and package comparison first, with the exact Fin3/Phase proof fields and wrong-presentation negative control. Derive generic-fiber/path uniqueness and compare both selected inverse recipes and the exact composite record. Develop the nerve/tuple decoder and Q as a separate bounded construction, proving the graph, tube, diagonal, substitution and triangle laws before publishing their selected-square equation. Keep the RU-relative-square/classifier construction as an explicit unresolved deliverable or concrete successor; the finite nerve does not classify arbitrary Cartesian fibrant families or supply arbitrary target ua beyond its decoded local systems.

None of these steps needs a final-result field on a public interface. They need constructors and reusable derived comparison lemmas. Formal adoption still requires EDD, independent Standards/Spec review and the applicable full build/audit; this assessment supplies paper-level support and a scoped implementation order, not those acceptance results.
