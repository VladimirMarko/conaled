# A checked restricted higher-family key diagram

[#426](https://github.com/VladimirMarko/conaled/issues/426) implements the
explicit diagram from the [joint comparison](joint-modal-higher-comparison.md).
The inspected baseline is `3bbf8083f94629fdedc1a438112f78d6d97a3196`.
The new modules construct the family and keys, connect the direct boundary
presentation to `TwoFamily`, and retain the selected higher observation under
restricted access. This is semantic model construction. There is no source
expression or source-proof transport claim.

The implementation uses `G : Type u` with `AddCommGroup G`; a change of base
is an `AddMonoidHom G H` between such groups. All integer multipliers are
allowed, including zero and negative integers. There is no injectivity,
surjectivity, torsion-free or decidable-equality hypothesis. Commutativity
supplies interchange in `B²G` and naturality of the family action in `BG`.
The construction does not establish the same one-object, one-arrow model for
nonabelian groups.

## Construction and observation

[Family](../../SquareKit/Internal/ModalHigher/Family.lean) uses the existing
`DoubleDelooping.Space (Multiplicative G)` as `B²G`: one object, one arrow,
and second cells labelled by `G`. Its fiber is
`LocallyDiscrete (SingleObj (Multiplicative G))`, the groupoid `BG` with
only equality cells between its arrows. The type wrappers change notation,
not the chosen observation.

`family` sends every base arrow to the identity strict functor. A second cell
`g` acts by the strict transformation whose component is the fiber arrow `g`.
The constructor proves identity, vertical composition and both whiskering laws.
`observe f g` reads the component of the **actual pulled family action**;
`observe_eq` proves that component is `f g`. The family is constant on objects
but not constant on second cells.

`baseMap f` constructs the strict higher functor induced by a homomorphism.
`key d` specializes it to `g ↦ d • g`.
[Keys](../../SquareKit/Internal/ModalHigher/Keys.lean) proves identity,
composition and commutation with arbitrary admitted base homomorphisms as
whole strict-functor equalities. These equalities include object, arrow and
second-cell maps. `pullback_comp` identifies successive pullbacks; `lift_comp`
uses the existing equality cast to compare their entire total functors.

Pulling back along `f : G →+ H` retains fiber `BH`, with action `f g`.
Pulling back the scaled `BH` family gives action `d • f g`. In particular,
base change never maps a supplied fiber arrow `a : H` to `f a` or replaces
`BH` with `BG`. A functor changing fibers would be a separate family comparison;
this construction neither needs nor identifies one with its substitution lift.
The `ℤ → ℤ × ℤ` example checks an arrow `(7, -4)` in the retained target fiber.

## Total boundary and the direct comparison

[Total](../../SquareKit/Internal/ModalHigher/Total.lean) gives the direct
presentation `BoundaryCell f a b`: a label `g : G` and equation
`a = b + f g`, with `a,b : H`. The identity label is zero, vertical and
horizontal compositions add labels, and inversion negates them. Each operation
constructs its boundary using the homomorphism laws. These are definitions
and proofs, rather than an interface asking the caller to assume the desired
comparison.

`encode` constructs a genuine `TwoFamily` total cell from this boundary.
`decode` extracts the same equation from every total cell between the stated
arrows. Both inverse equations are proved. Thus the direct presentation neither
admits an invalid boundary nor discards a second-cell label.

[Direct](../../SquareKit/Internal/ModalHigher/Direct.lean) proves direct unit,
associativity, inverse and interchange equations for the cell operations.
`totalArrow_comp` connects additive arrow composition to categorical composition;
`encode_vertical` connects vertical composition. Both whiskerings retain the
base label, while the generic total structure supplies their typed boundaries.
This is a direct presentation with checked operations and a comparison to the
existing strict total structure, not a second independent implementation of
every Mathlib bicategory field.

For `f : G →+ H` and `k : H →+ J`, the direct lift sends a cell with boundary
`a = b + k (f g)` to label `f g`, keeping the arrow labels in `J`.
`nested_lift_object`, `nested_lift_arrow` and `nested_lift_cell` identify this
operation with `TwoFamily.reindexHigher`, including equality of the complete
encoded cell. This covers `L_c : E_(dc) → E_d` by taking the multiplication
homomorphisms. The projection equation is equality of whole higher functors.
The report does not claim a separately formalized universal property for the
square as an object in a category of strict two-categories.

| Work | Direct definitions and reused proofs |
| --- | --- |
| Base and family | Existing `DoubleDelooping` gives the base laws; new `action` and `family` prove the higher family laws for every abelian group. |
| Direct total presentation | New boundary operations, inverse encode/decode, direct cell equations and composition comparisons. |
| Structured total | `TwoFamily` supplies the category and strict bicategory, including coherence and interchange. No new total bicategory instance is copied. |
| Substitution lift | `reindexHigher` supplies preservation of identities, vertical composition and both whiskerings. `reindexHigher_projection` and `reindexHigher_comp_cast` supply all-dimensional projection and composition. |
| Access policy | New product-context projection, factorization contract and rejection proofs; higher reindexing alone does not enforce this policy. |

The extra obligations were the family action, its strict laws, homomorphism
keys, explicit boundary comparisons and access factorization. This establishes
specific proof reuse. It is not a matched author trial, implementation-size
comparison or measurement of productivity. No timings are used to compare the
mathematical routes.

## Access and discriminating cases

[Access](../../SquareKit/Internal/ModalHigher/Access.lean) constructs the full
context `B²G × Disc(Bool)` using Mathlib's product bicategory. `forgetHidden`
is its strict projection. A substitution is `Allowed` precisely when it factors
through that projection as a whole strict functor. The views are projection
followed by a multiplication key; `view_key` proves the commuting triangle.

`allowed_cell_factors` derives independence from the Boolean for every selected
cell of an allowed substitution. Two assignments differing only in that Boolean
then refute hidden-coordinate recovery and a requested substitution selecting
zero or a nonzero cell according to the Boolean. These are impossibility proofs
for the stated factorization policy, not assertions of syntax completeness or
physical security.

[Examples](../../Examples/ModalHigher.lean) retains these cases:

- Inputs `1` supplied independently to locked families of scale `1,2,6` produce
  the arrows `1,2,6`. These are not three views of one full-context input.
- One full-context cell `1` gives view labels `1,3,6` at `w,v,u`, for either
  Boolean. The triangle from `v` to `u` is key `2` after view `3`.
- Reflexive input yields zero; scale `-2` on input `3` yields `-6`.
- Omitting pullback returns `1` instead of `2`; erasing the cell returns zero.
- The actual cell `1 : 2 ⇒ 0` exists in `E₂`. Its correct lift has base label
  `2`. A cell with base label `1 : 2 ⇒ 0` in `E₁` cannot exist.
- Boolean-dependent choice is rejected both for label factorization and for
  actual allowed higher substitutions.
- Pullback along the diagonal `ℤ → ℤ × ℤ` observes `(1,1)` and retains the
  independently supplied fiber arrow `(7,-4)`.

## Statement review and evidence

The initial obligation was a missing uniform connection: the existing integer
path-family example showed the action at one group, while generic `TwoFamily`
reindexing already supplied the structural laws. No theorem was weakened to
remove a failed case. Development repairs concerned dependent rewrites, type
annotations and composition notation; they do not establish mathematical
impossibility. The rejection theorems above do.

Statement review checked group hypotheses, the direction of composition, fiber
retention across different groups, both dimensions of the boundary and the
scope of access factorization. Open intermediate forms are included:
`open_square` preserves `h' + a = b + h` for arbitrary labels, and
`input_naturality` handles arbitrary fiber arrows. The homomorphism and key
constructions are uniform, rather than witnesses chosen separately per input.
External equality compares labels and functor data; the second cells themselves
remain data. No assertion identifies all parallel paths or requires maximal
witness retention in unrelated models.

Focused validation built `Examples.ModalHigher` and its import closure with
the pinned Lean environment, including a successful rerun after the interrupted
session. The scoped exhaustive audit of that import closure passed with only
`propext`, `Classical.choice` and `Quot.sound`. Source-policy, public-entrypoint
coverage and local-link checks passed. The public entrypoint imports the example
for the integrated build and exhaustive axiom audit. Required candidate acceptance and independent
Standards/Spec review remain in the enclosing implementation workflow; focused
checks alone are not recorded as full acceptance.

## Primary sources and remaining scope

The primary-source check revisited Gratzer, Kavvos, Nuyts and Birkedal,
[*Multimodal Dependent Type Theory*, v2](https://arxiv.org/pdf/2011.15021v2),
Definition 5.1 and Theorem 7.1. The former requires a strict functor from the
reversed mode theory; the latter requires MLTT natural models, size-preserving
dependent right adjoints and coherent modal data. The present diagram supplies
no such modal type formers or right adjoints, so it does not invoke that model
theorem. Its keys are semantic substitutions in the stated finite diagram.

Warren's [*The Strict ω-Groupoid Interpretation of Type Theory*](https://mawarren.net/papers/crmp1295.pdf),
§§3, 5–6 and Theorem 7.1, constructs dependent extension and the operations
needed for its soundness result. Its groupoid-valued family account motivates
the construction; the local proofs above establish only their declared finite
fragment. Neither source theorem supplies an omitted eliminator here.

General dependent J, full MTT, source interpretation and smooth/cohesive models
are not established. Connecting a source argument to this action belongs to a
separately scoped successor under #289/#36; #235 owns broader architectural
assessment. Smooth construction remains #433. Local-universes work remains
#427 and is not a prerequisite: this diagram already has explicit strict laws.
No new framework adoption, #108 preparation or universal combined scope follows.
