# Contract and foundations assessment

Retain the presented-discrete filler and the finite-groupoid nerve as useful bounded constructions. The proposed Q coherence has a credible concrete derivation using the existing dependent-square theorem. Do not describe this as completion of the retained-square comparison in #574: the supplied equation lives after Q, whereas #574 retains and recovers the full code-valued body in RU. This is a scope change requiring an explicit additional contract or a further comparison construction, not a demonstrated mathematical defect in the nerve.

## Evidence and scope

I inspected the frozen proposal, addendum, brief, and committed source at `4c81050dd2844c39bcfc551426f1e1cdbe3bcac1`. I had no prior involvement and read no other reviewer report. The source inspections below use that commit, not concurrent working-tree edits. The review used direct mathematical arguments and source inspection; no Lean proof, finite computation, or project build was run. Existing declarations are evidence for reusable source operations, not kernel validation of the new construction.

SHA-256 inputs:

- proposal.md: `86bb2558a0ed55255ce17a14e57a7aed18e2e0f9310030d5ce7312fedbdfc76b`
- transport-addendum.md: `07923de8cf70b059ff665864de8505be6775613cd2160ea230f2b58aae2fe0a5`
- challenge-brief.md: `f962444ec1f6c85652979a4572ebe3ff6ffee0e145e53c5123f6b082e5244f67`

## All-box filling

The presented-discrete construction is sound at its stated hypothesis of an actual natural isomorphism A ≅ ΔS. For any generalized y, an element over the added interval has the same ΔS coordinate as its restriction to the graph of r. This determines the proposed filler and proves its agreement with an arbitrary tube, including tubes with no source lift. The argument applies over a subcontext φ as well as a representable. The source=target condition is therefore local on the equality subobject r=s, not merely a computation for syntactically identical expressions.

The specialized package argument also has the right hypothesis. A natural isomorphism to a constant carrier supplies inverse reindexing on each generalized argument. Thus identity evaluation determines the generalized Pi function, and the inverse reconstructs it. This is much stronger than path-discreteness alone. The proof-bearing fields must still be included recursively in this isomorphism; proof irrelevance only identifies proofs after their dependent types are identified. Nothing in this argument justifies a general inverse to #574's Pi comparison.

The nerve construction is an actual presheaf: precomposition by a vertex function sends functors between indiscrete vertex groupoids to functors, and respects identities and composition. The proposed filler assigns objects and every arrow, with the arrow formula satisfying the functor equations by cancellation. It is not an arbitrary collection of vertices being presumed to extend.

The delicate tube check works. Suppose a substitution f selects a cube on which φ holds. Every vertex f(v) then lies in φ. On that cube all proposed vertical arrows w come from T. For any two vertices, tube functoriality and agreement with B at the source graph imply

    T((v,z),(w,z')) = w_w(z') ∘ B(v,w) ∘ w_v(z)⁻¹.

This proves equality of the entire restricted functor with T. It does not require φ to hold globally whenever it holds at all vertices. For example, φ=(x=0)∨(x=1) contains all vertices of the interval but excludes its generic element. The construction still legitimately specifies the missing cross-arrow using B and the tube vertical arrows. For φ=(x=y), pullback along variable duplication makes the whole tube available; its vertices and arrows agree by the same calculation. Under arbitrary substitution, membership is membership in the pulled-back subobject, so the branch choice commutes with reindexing. At z=r_v, each w is identity, even if r_v differs between vertices. Restriction to the source graph is therefore B on arrows too.

The decoder filler is likewise determined: for each output vertex use p's arrow from a source-graph vertex and the corresponding base value. Compatibility of the base tuple makes the result independent of the source vertex used. Compatibility of p makes it a tuple; tube agreement follows from the same transport equation. These are credible all-target-box constructions, not constructions conditional on a source lift. They require the stated external decidability/classical reasoning for branch selection; they do not establish a constructive algorithm or a classifier of all Kan families.

## Q coherence

The conditional expression has the required De Morgan identities by distributivity and absorption. Its values at s=0 and s=1 are p and q, respectively, and its value when p=q is p without using excluded middle for the interval. For

    H(s,t)=conditional(s,canonical(v,a)(t),canonical(v,w)(t)),

its t=0 face is v, s=0 face is canonical(v,a), s=1 face is canonical(v,w), and t=1 face is canonical(a,w). This orientation gives transport(v,w)=transport(a,w)∘transport(v,a).

The addendum identifies a sufficient existing operation, not merely a suggestive theorem name. `SquareKit/Internal/Cubical/DependentTransportComposition.lean:365–399` takes a family over the square, its lawful filling, two specified vertical sections, and a dependent bottom path. `squareLift` builds the dependent square; `squareComparison` compares upper-edge transport with the specified right endpoint. Taking the bottom and right forward sections exactly as the addendum prescribes produces the required comparison. `PathDiscrete.ofIso` at `DiscreteEquivalences.lean:91` then turns it into equality at the discrete endpoint. The same construction with constant side sections proves invariance under replacing a dimension path by another with the same vertex endpoints. This supplies Q's substitution law; it does not assume a path-composition theorem for the Cartesian cube category.

The remaining work here is proof assembly: pullback casts, conversion between chosen transport and `pathToMap`, extensionality on closed sections, and compatibility of the chosen endpoint presentations. It is an unproved implementation obligation, not an identified obstruction. The existing `squareLift_reindex` and `squareTop_body_reindex` support naturality, but do not already state Q's theorem. Also, `DiscreteEquivalences.closedEquiv` explicitly classifies section observations rather than native witnesses. Full record uniqueness needs the separate argument that generic fibers and their path bodies are singleton; citing `closedEquiv` alone would be insufficient.

## Selected square and decoder contract

The exact consumer is `Examples/FiniteUniverseLoops.lean:188–202`: `swapComposition` is the actual `NaturalUnivalenceLaws.composition`, with the selected equivalence records, and its reindex theorem concerns the entire `comparisonSquare` body. The frozen #574 report explicitly puts its image in RU, uses κ² to retain interiors, and recovers the original comparison using inverse comparisons and `comparisonSquare_injective`.

Q applied to that exact body can indeed equal an independently constructed whole nerve square once Q's laws and the four boundary identifications are proved. An indiscrete-groupoid functor on four vertices is determined by a compatible connected boundary diagram. This gives an equality of full target bodies, not merely a numeric observation. It preserves the stated Boolean and noncommuting Fin3 controls. This is the strongest positive evidence for the candidate.

However, Q's output contains only vertex codes and transport bijections. Boundary determination in the nerve proves nothing about injectivity of Q or equality between code-valued squares in RU. The proposal supplies neither a return map N(FinSetIso)→RU nor a specified comparison between its decoded tuple family and the restricted source decoder on every cube in Q's domain. Finite discrete vertex fibers do not by themselves assert that source interior elements are uniquely determined by vertex data. Thus the phrase “whole-square equality” must always name its ambient presheaf.

No relative three-path in RU follows from the current equation. Nor is such a three-path shown impossible. If the intended #600 square obligation is the #574 retained RU body compared with a recomputed RU body, this part remains open. If a separate contract explicitly chooses N(FinSetIso) as the observation, the proposed equality meets that weaker observation contract after its proof obligations are completed. Keeping #599's faithful restriction alongside Q preserves access to the old witness but does not connect it to independent recomputation in RU.

## Smallest useful correction and discriminating checks

Publish or implement the discrete all-box construction first, including full uniqueness of endpoint fiber records and the actual five-field package. Retain the nerve as a second bounded result, with the theorem explicitly typed as an equality in N(FinSetIso), and describe Q as a comparison of codes and transport observations until a decoder comparison is supplied. Do not add final preservation assertions as interface fields when these can be derived.

For Q, a useful first formal check is the triangle transport equation for arbitrary cube u and arbitrary vertices v,a,w, followed by naturality under a noncanonical De Morgan substitution. Closed Fin3 arithmetic alone cannot exercise this obligation. For the filler, check φ=(x=y), r=x, s=y and duplicate-variable substitution; also check the endpoint union φ=(x=0)∨(x=1), which tests the distinction between vertex and generic membership.

For the stronger square obligation, write the desired statement with both sides typed in RU and four fixed faces before starting implementation. The current proposal cannot even supply the recomputed side of that statement. The smallest concrete successor is to construct a decoder/classifier comparison for the nerve presentation and use it to state a relative comparison on the exact `swapComposition`. Whether that bounded comparison is easier than a more general classifier is unresolved; the current filler and Q arguments do not settle it.
