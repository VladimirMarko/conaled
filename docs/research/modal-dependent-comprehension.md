# Modal dependent context extension

The [#384 implementation](../../SquareKit/Internal/ModalAccess/Comprehension.lean)
extends the [#375 restricted environments](bounded-modal-access.md) with actual
dependent telescopes. Its [client](../../Examples/ModalComprehension.lean) has an
accessible Boolean `x`, followed by `i : Fin (if x then 3 else 2)`. Both cases
have inhabitants, and the fibers have different cardinalities. The selected
index is 2 when `x` is true and 1 when false. Observations retain the full
pair, not just the existence of an index.

## Constructed model and source boundary

The model specializes the existing `DependentSquares` split family model in
[Dependent.lean](../../Dependent.lean) to the accessible environment at a
specified lock word. Its operations and substitution laws are reused. Context
extension is dependent sum, projection forgets the
last component, and the newest variable returns it. Substituting into a type
precomposes its family with the same map used by term substitution. Pairing
satisfies both projection equations and uniqueness. Extension along a base map
is a constructed pullback, with its factorization and uniqueness proved.

Keys act contravariantly through #375's `Env.key`. Pulling a dependent family
back along that map gives the type of the extended context at the new locks.
`keyExtension` constructs the map between the two extensions. Its projection
square commutes, and repeated key extensions compose. It retains the dependent
component rather than selecting a replacement. No dependent right adjoint is
needed for these operations.

`Context` generates base contexts and finite dependent extensions. `Term`
generates local primitives, the newest variable and explicit substitution.
`Sub` generates identity, base maps, projections, composition and dependent
pairing. Evaluation is recursive; substitution and composition compatibility
are proved from the definitions. The term and substitution equations compare
interpretations. They do not identify the raw constructor trees.

This is a **shallow family signature with generated structural syntax**.
Types and local primitive functions are Lean families and functions over the
already restricted carrier. The implementation does not generate those
primitives from a separate dependent calculus, infer their mathematical
requirements, or prove an arbitrary MTT interpretation theorem. A primitive
cannot recover an inaccessible coordinate from the restricted carrier; the
client proves this for every function on that carrier, which is stronger than
a grammar-specific check. Introducing an unrestricted carrier as a different
base would constitute a different specification, not a way to evade this
client's typing boundary.

The pinned source remains Gratzer, Kavvos, Nuyts and Birkedal,
[*Multimodal Dependent Type Theory*, arXiv:2011.15021v2](https://arxiv.org/html/2011.15021v2).
Sections 5.1 and 7 distinguish context extension from the additional structure
needed to interpret modal type formers. The present construction supplies the
former for this restricted environment model. It does not instantiate the
paper's full model theorem. Cells remain the thin `Prop`-valued reachability
relation from #375. Parallel proof-relevant keys and a combined higher/modal
model remain outside this result, owned by #289 with architectural coordination
under #235.

## Native comparison and controls

The frozen native interface is just a Boolean and an index in its corresponding
finite type. `nativeChange` complements the Boolean and chooses the largest
index of the new fiber. Two changes recover the selected native pair. The
generated dependent substitution has that exact behavior, and the generic
substitution-composition theorem connects its sequential and composed routes.
This change intentionally selects a new index; it is not claimed to preserve
an arbitrary old index across fibers of different cardinalities. In contrast,
the key extension preserves every supplied index exactly.

The checks include:

- `fibers_not_equivalent`: the two fibers cannot be identified by an equivalence.
- `two_changes`: the entire selected dependent pair agrees with the native result.
- `key_keeps_index`: key pullback preserves every index, not only the selected one.
- `forbidden_dependency` and `forbidden_substitution`: no function or generated
  substitution can recover ordinary `y` from this restricted context.
- `reset_loses_selected`: replacing the index by zero changes the observation
  in both inhabited cases, despite retaining the Boolean.
- Exact recovery of #375's Boolean, selected identity witness and unequal-endpoint
  identity family, together with its two missing-key obstructions.

The ordinary native client acquires no modal annotations. It remains shorter
than the explicit source encoding for this example. The shared route supplies
reusable comprehension, dependent substitution and key compatibility. This is
not a measurement of agent or human productivity. The shallow primitive boundary
still asks authors to supply well-typed local functions; it does not deliver the
ambition of transporting arbitrary proofs between mathematical settings.

## Acceptance evidence

The native contract was frozen before the generated telescope implementation.
Statement review checks the actual varying fibers, satisfiable selected values,
contravariant key direction, dependent second components, and semantic rather
than syntactic equality. The committed-candidate build and exhaustive proof
audit, independent Standards/Spec review, and integration candidate hashes are
recorded by the orchestration. This report does not replace those checks.
