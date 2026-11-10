# Selected signature comparisons through an ordinary groupoid cylinder

This is a checked construction checkpoint for #446, not completion of that
issue or of #433. The public result `SignatureCylinder.contextComparison`
constructs a natural isomorphism between the original generated context maps
from a selected primitive natural isomorphism and its compatible fiber square.
It covers all supported `CtxDeriv` constructors through the existing generated
composition and equivalence theorems.

The cylinder over `F : C ⥤ D` has objects `(c, d, i : F c ≅ d)` and arrows
inherited from `C`. Projection to `C` is fully faithful and an equivalence.
Evaluation sends an arrow `f` to `i⁻¹ ≫ F f ≫ j`. Given `η : F ≅ G`, the
endpoint inclusions choose `(c, F c, id)` and `(c, G c, η c)`. Evaluation of
the selected cylinder arrow is exactly `η c`, as proved by
`endpointIso_evaluation`.

Primitive fibers are pulled back from `C`. The evaluation fiber map is
`α c ≫ Q.map i.hom`. This gives actual strict interpretation signatures.
Their endpoint composites are proved equal to the supplied signatures.
Generated projection is an equivalence by `generatedContextMap_equivalence`;
both generated endpoint maps compose with it to identity by generated
composition and identity. The unique lifted identity supplies the selected
natural isomorphism, then evaluation maps it to the original target.

The equivalence requirement belongs only to this auxiliary projection. Neither
`F`, `G`, `α` nor `β` needs to be invertible or faithful. The checked example
uses unequal functors into `Codiscrete Bool` and a noninjective `Bool → PUnit`
fiber map. `SelectedLiftIso` proves uniqueness, identity, vertical composition,
and left whiskering for natural-isomorphism lifting through any fully faithful
functor. Those generic laws have not yet been connected to all generated
signature-comparison laws.

## Statement review and validation

The context theorem quantifies over the same generated derivation at both
original direct endpoints. Its conclusion is a selected natural isomorphism
of whole functors, so actual-arrow naturality is included. The primitive
fiber hypothesis is an equality of natural transformations, not an assumption
of generated preservation or J preservation. The cylinder fiber construction
uses that transformation's naturality. The example's unequal base functors
and noninjective fiber map establish that the input contract does not silently
require equivalence of the compared signatures.

Focused Lean checks pass for the cylinder, generated substitution/family/section,
selected contraction/counit modules and the dependent-J example. The actual
smooth base-change context and family comparisons also check against
`Descent.baseChangeComparison` and `CocycleDatum.fiberBaseChange_square`.
The generated dependency build passed (872 jobs). The focused axiom inspection
covers the public context comparison, primitive recovery, lifting composition
and example results. Full integrated fresh build, exhaustive audit and
independent review remain owned by the parent orchestration.

## Generated preservation checkpoint

`contextComparison_substitution` proves an isomorphism-valued square with the
existing strict generated substitution maps for every supported substitution.
`familyComparison` extracts a dependent family modification from the actual
comprehension comparison: its base is the selected context component and its
fiber naturality is proved using total-category naturality. It does not assume
faithfulness of the compared maps.

`contextComparison_section` uses the generated pairing substitution for the
actual term section. It therefore covers the existing contextual-J interpreter.
`generatedRootTail_square` identifies the native root/tail contractions at both
direct endpoints, including their chosen inverse functors and counits.
`contextComparison_rootTail_counit` derives the external chosen-counit square
from the root substitution square. The example specializes both results to an
existing path command with two tail binders, the second depending on the first.
These conclusions require only the primitive square; no generated contraction,
counit, or J compatibility is supplied by a caller.

## Remaining #446 work

- Connect vertical composition and horizontal whiskering of primitive squares
  to the generated comparisons, including explicit endpoint transports.
- Connect the checked smooth comparison to composed signatures and
  retain parameter identity/composition, the unchanged source wrapper,
  C4 arrows, and classical/ineffective consumers.
- Retain rejection of incoherent objectwise choices, and complete fresh
  acceptance and independent review together with #445/#447/#433.
