# Completion of represented sheaf groupoids

[Issue #727](https://github.com/VladimirMarko/conaled/issues/727) extends completion
to `SheafGroupoid.Operations` with its `Laws`. The constructor takes the object
and arrow sheaves, endpoint maps, unit, inverse and composition. A global action
presentation is unnecessary. The [design assessment](general-groupoid-completion-design/synthesis.md)
compares principal bundles with completion by cover-indexed descent data.

For `C : Type u` with `Category.{v} C`, the construction supports any Grothendieck
topology `J` and sheaves valued in `Type (max u v)`. The base category consists
of those sheaves, with the existing `SheafCover.topology` of locally surjective
singleton covers. Neither subcanonicality nor enough points is assumed.
Sheafified representables supply the sectionwise groupoids on the original
site. Groupoid objects and principal bundles lie in
`Type (max (u + 1) (v + 1))`; their hom types lie in `Type (max u v)`.
The input and output pseudofunctors therefore use the same category universes.

A bundle over `X` is a split sheaf family over `X × G.objects`. The second index
is its anchor. An arrow `m → n` acts on a point anchored at `n` to produce a point
anchored at `m`. Principality requires a unique actual connecting arrow between
any two points over the same parameter section. Local existence concerns the
total projection to `X`, allowing fibers without a global section.
All natural equivariant maps are included. Their invertibility follows from
principality and local existence.

The regular bundle at an object consists of all arrows into it. Postcomposition
constructs the unit on arrows; evaluation at the identity proves full
faithfulness. Pulling a bundle back to its total space provides the regular
local trivialization and proves singleton-cover local generation. These are
proved properties of the constructed unit.

Effective descent pulls the cover to the context containing the parameter and
anchor, then uses `SplitSheafDescent` to construct the sheaf of compatible
restriction-stage sections. The action operates on every such section and
preserves the matching equations. Principality descends by detecting an
isomorphism of ordinary sheaf displays: the tautological map from a regular
bundle to an action is locally bijective exactly when connector arrows exist
uniquely. This avoids choosing a lift of the cover. The construction descends
all compatible equivariant maps and recovers the full Mathlib descent datum.
It proves the output stack instance and, through the fully faithful unit, the
source prestack instance.

`Bundle.universalEquivalence` reuses `StackificationUniversal` on these proved
hypotheses. Its forward functor is actual precomposition with `Bundle.unit`.
The arrows of these mapping categories are modifications. `Bundle.extend`
provides the inverse functor and its unit comparison; actual input maps extend
to completed maps with identity and composition comparisons.

The principal entrypoints and their roles are:

| Module | Interface |
| --- | --- |
| `SheafGroupoidStackification` | General completion, mapping categories, extension and already-stack recovery |
| `SheafGroupoidStackificationRecovery` | Action-quotient and original dense-site comparisons, with unit and mapping comparisons |
| `SheafGroupoidAtlasPresentation` | Actual atlas groupoids and input maps, including full arrows between different lifts |
| `SheafGroupoidAtlasStackification` | Completed atlas maps, coordinate round trips and substitution comparisons |
| `SheafGroupoidAtlasComparison` | Ambient and common-refinement comparisons as invertible modifications |

The action-presentable comparison is derived after constructing the general
completion. Both directions extend the corresponding unit through its proved
universal property. Their composites recover the identity by full faithfulness
of precomposition. This yields whole-fiber equivalences under the original
action assumptions and recovers the dense-site equivalence under the original
site-comparison hypotheses. Existing direct action APIs remain available.

[The checked consumer](../../Examples/GeneralGroupoidCompletion.lean) builds the
actual pullback groupoids of `Examples.ActionMorita`'s two disk atlases and their
common refinement before applying completion. It retains four arrows between
every pair of origin lifts, including distinct lifts, and proves that a discrete
observation cannot faithfully retain them. Independently chosen smooth branch
coordinates give completed maps with an invertible round trip. A nontrivial
clutching datum is glued through the new unit and has no global input chart.
Ineffective loops remain distinct. For a previously proved already-stack
input, the equivalence's forward functor is the actual new regular-bundle unit.

This is sheaf-level, groupoid-valued completion. Smooth representability,
properness and étaleness are additional geometric claims, not hypotheses hidden
in the generic constructor. Arbitrary prestacks with nonsheaf arrows, higher
descent (#721), unrestricted balanced bibundles (#722), and the internal Myers
properness comparison (#724, under #36) remain separate obligations.
