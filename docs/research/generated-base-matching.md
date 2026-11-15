# Base-binder matching

The base-binder step identifies actual relative matching with the primitive
quotient matching groupoid, uniformly over every independently supplied
matching context datum. It introduces no global extension or effectivity
premise. The generated evaluation comparison and the full simultaneous
context/type induction are separate consumers of this identification.

[`CechMatchingComprehensionConstant`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionConstant.lean)
constructs constant coefficient restriction data from two strict diagrams.
Given their total restriction coherence, `categoryIso` identifies each relative
fiber with the coefficient diagram's independent matching groupoid.
`familyIso` makes these identifications natural on every base matching arrow.
The forward functor takes exactly the local fiber object and the fiber
component of the selected overlap and local arrows. Reconstruction combines
those data with the supplied base datum. Both functor composites equal the
identity, so the comparison is a strict isomorphism of categories, not merely
a correspondence between isomorphism classes.

[`SmoothQuotientGeneratedBaseMatching`](../../SquareKit/SmoothQuotientGeneratedBaseMatching.lean)
specializes this construction to `relativeFamilyData a hΓ (.base hΓ) A`.
`relativeFamilyData_base` uses the existing `generatedFamilyMap_base` theorem
on all six restrictions. Total coherence comes from the actual generated
relative diagram. The coefficient diagram uses precisely the existing
`AsSmall` quotient objects and parameter-restriction functors.

`basePrimitiveFamilyIso` identifies this actual relative family with the
constant family of `AsSmall` primitive Čech matching data. It composes the
constant-family comparison with the primitive matching equivalence and the
[universe-lifting bridge](../../SquareKit/Internal/PathTransport/CechMatchingAsSmall.lean).
The final `diagramIsoOfEq` reconciles the strict and universe-lifted
presentations of the Čech equations. Its generic recovery and inverse laws
avoid expanding concrete sheaf restrictions in the comparison proofs.
`DiagramComparison` bundles the resulting equivalence with recovery of its
selected local data. The concrete recovery declarations are in
[`SmoothQuotientGeneratedBaseMatchingRecovery`](../../SquareKit/SmoothQuotientGeneratedBaseMatchingRecovery.lean).

`baseComprehensionEquivalence` then identifies the constant-family total with
the actual matching groupoid of the generated context extended by a base
binder. `baseComprehensionProjection` preserves the supplied base context datum
naturally, including its arrows. This uses the general dependent comprehension
equivalence; it does not assume an equivalence for the generated extension.

The recovery statements retain the local quotient object, selected overlap and
local arrow. The presentation-change statements use heterogeneous equality
where the arrow endpoint types differ by the proved presentation equality.
The primitive comparison has literal equality of local objects after removing
the universe wrapper. Its selected overlap and local arrows agree
heterogeneously with the universe lifts of the original arrows.
No selected arrow is replaced by an equality of endpoint objects.

The checked generic consumers in
[`Examples.CechMatchingComprehension`](../../Examples/CechMatchingComprehension.lean)
recover an integer-labelled coefficient loop over any base datum, reconstruct
arbitrary coefficient matching data, and show invariance of constant
coefficients under every base arrow. The generated consumers in
[`Examples.GeneratedBaseMatching`](../../Examples/GeneratedBaseMatching.lean)
recover independently supplied primitive data and arrows, exercise naturality
on arbitrary context arrows, and use the actual base-extension equivalence.

Statement review checks the arbitrary context derivation, parameter display,
matching data and morphism quantifiers. The only coherence supplied to the
generic constant construction consists of restriction-functor equations; the
actual specialization proves those equations through the generated restriction
laws. The non-discrete loop consumer rules out collapsing coefficient paths.
The explicit universe lift changes representation and sizes, not the matching
conditions or selected arrows.

Validation: focused builds of the core and both consumer modules passed at the
pinned configuration and default proof limits (3,569 jobs for the combined
focused build). The recovery module uses the bundled comparison projections
so dependent arrow types stay aligned. Final full #445/#433 build and proof
audit remain with the coordinating orchestration; this checkpoint does not
claim that integrated acceptance or the simultaneous evaluation induction.
