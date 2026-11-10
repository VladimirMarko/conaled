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

Focused Lean checks pass for the three new library modules and the example.
The generated dependency build passed (872 jobs). The focused axiom inspection
covers the public context comparison, primitive recovery, lifting composition
and example results. Full integrated fresh build, exhaustive audit and
independent review remain owned by the parent orchestration.

## Remaining #446 work

- Prove generated substitution coherence for the selected lifted components
  by faithfulness of generated projection; include root and finite-tail maps.
- Extract coherent fiber-component natural isomorphisms from comparison of
  comprehension, retaining compatibility with the selected base component.
- Prove section/term coherence, and actual contraction, selected-counit and
  compared-branch compatibility. Derive the isomorphism-valued J square.
  Existing strict J preservation is used inside generated composition, but
  this checkpoint does not itself prove the requested external J square.
- Connect vertical composition and horizontal whiskering of primitive squares
  to the generated comparisons, including explicit endpoint transports.
- Apply to `Descent.baseChangeComparison` and the deformation fiber square,
  then retain parameter identity/composition, the unchanged source wrapper,
  C4 arrows, dependent-J caller, and classical/ineffective consumers.
- Retain rejection of incoherent objectwise choices, and complete fresh
  acceptance and independent review together with #445/#447/#433.
