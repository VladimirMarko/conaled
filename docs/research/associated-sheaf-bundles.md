# Associated sheaf bundles and structure-group extension

The associated display in `SheafAssociatedBundle.associated P a` is constructed
by effective sheaf descent along the torsor's locally surjective projection.
Its input is a torsor `P` and an action `a`; a quotient, local trivialization of
the answer, or global section of `P` is not an input. `quotientUniversal` identifies
all maps from its total display over the base with invariant maps from the actual
pair display. Both inverse equations and the unique-factorization theorem retain
the maps themselves.

The generic construction uses `C : Type u`, `[Category.{v} C]`, and sheaves valued
in `Type (max u v)`. This is the universe supported by the existing effective
display descent implementation. The semilinear primitives also support an
independent value universe. No enough-points, subcanonical-site, finite-group,
Hausdorff, or countability assumption enters the generic construction. The site
comparison uses the existing comparison library's common site universe and
explicit continuity and cocontinuity assumptions.

## Left actions and the order of multiplication

The quotient convention is `[g • p, g • m] = [p,m]`. The fiber difference
`fiberDifference P x p q` is the unique group element carrying `p` to `q`.
Consequently `difference p r = difference q r * difference p q`. Local
associated coordinates change by this difference acting on the fiber.

For a group-sheaf homomorphism `φ : G ⟶ H`, extension uses the action
`g • h = h * φ(g)⁻¹` on `H`. Residual left multiplication by `H` descends to an
actual torsor. The unit is `p ↦ [p,1]`; the universal map associated to a
semilinear map `u` is `[p,h] ↦ h • u(p)`. The identity comparison is
`[p,h] ↦ h • p`, and the composite comparison is
`[[p,h],k] ↦ [p,k * ψ(h)]`. Neither `φ` nor `ψ` must be invertible or surjective.
For the different action of left multiplication on `G`, the regular associated
fiber recovers `P` by `[p,m] ↦ m⁻¹ • p`.

`SemilinearMap` keeps arbitrary structure homomorphisms and every equivariant
map over them. `ActionMap` independently records the map of acted-on fibers.
Their induced associated map has identity and composition laws; it need not be
invertible. The target-map interface identifies equivariant maps from the actual
torsor total to the acted-on sheaf with sections of the associated display.
The two inverse constructions commute with compatible arrows and restriction.

## Local data and recovery

`associatedData` constructs its local objects from the supplied local torsors
and its overlap maps from the supplied transition arrows. It does not first
glue a global torsor and restrict that answer. `associatedDataOfGlobal` compares
this construction with canonical local data; `associatedDataRecovery` identifies
gluing the independently associated data with association of the recovered
torsor, naturally on all compatible arrows. `associatedDataRefinement` carries
this comparison through covering refinements and base change.

For extension, `extensionData` retains the actual local H-torsors and their
transition arrows. `extensionDataFunctor` includes every compatible local map;
`extensionDataRecovery` and `extensionDataRefinement` compare their gluing with
extension and base restriction. The underlying display equations agree with
`associatedData`, while the comparison arrows retain the H-actions.

The cocycle implementation starts with independently supplied labels. For the
library's right-translation cocycle convention, the associated transition acts
by the inverse cocycle label. `cocycleExtensionData_eq` identifies the extension
transition with right translation by the homomorphism-applied label.
`cocycleExtensionComparison` is an equivariant arrow of actual glued torsors,
not just an equality of transition formulas. Gauge labels and covering maps
remain part of the comparison.

`Site.comparisonIso` identifies association after the chosen site restriction
with restriction of the constructed associated display. Its map sends each
quotient representative to the same pair at the image stage. Local evaluation
proves it invertible using the restricted torsor cover. The forward construction
therefore needs continuity and cocontinuity, without requiring full faithfulness
or density. The extension module's `Site.comparison` retains the H-action,
all torsor arrows and the semilinear unit as well.

## Ordinary comparisons and remaining geometry

`Examples.SmoothAssociatedBundle.regularTotalIso` identifies the regular
associated display of an independently supplied ordinary discrete principal
bundle with its realized ordinary total. It preserves the actual projection.
`regularAlong_total` preserves every equivariant smooth bundle map over a
smooth base map, including the maps used for ordinary pullback comparison.
The base and total may have independent source and target dimensions across
that map. The one-point trivial fiber recovers the realized ordinary base.
These results retain the ordinary bundle's existing assumptions and add no
Hausdorff or countability premise. For an ordinary right action, the existing
`RightBundle.toLeft` adapter uses the inverse action and inverse sheet labels
(`LocalTrivialization.toLeft_sheet`). Applying the regular comparison to that
left bundle retains this convention; extension along an arbitrary group
homomorphism is supplied separately by the sheaf construction above.

General nonfree discrete fibers require an ordinary associated-space
construction from local products and transition maps, an atlas on the glued
space, and comparison of its realized display with `associated`. Principal
bundle reconstruction alone cannot supply this result: an action with
stabilizers need not give a principal total.
[#676](https://github.com/VladimirMarko/conaled/issues/676) owns the future
discrete-fiber construction: take a discrete acted-on set, build the ordinary
associated total over an arbitrary admitted
ordinary principal bundle, prove local product charts and projection, and
identify all realized associated maps and base changes.

[#677](https://github.com/VladimirMarko/conaled/issues/677) owns the future
positive-dimensional branch, conditional on selecting a concrete smooth action
and nontrivial bundle. Its inputs include a smooth fiber manifold and a smooth
group action;
local charts have dimension `dim(base) + dim(fiber)`. The remaining obligations
are smooth transition maps, the glued manifold and projection, the realization
comparison at arbitrary stages, and map/base-change naturality. Neither this
geometry nor general nonfree discrete-fiber representability is claimed by the
regular and one-point comparisons above.

## Elaboration costs

The generic associated quotient, restriction, family refinement and site
comparisons use default heartbeat and recursion limits. Two extension packaging
declarations, `extensionDataOfGlobal` and `extensionDataRecovery`, use local
400,000-heartbeat limits after measured failures at the default 200,000. These
settings do not change the toolchain, trust boundary or global build budget.

The concrete smooth scaling consumer exposed a different cost. Specializing
the full section comparison with explicit smooth scaling maps exhausted the
kernel budget, including a 1,600,000-heartbeat trial. Isolation retained the
concrete site, base and group while varying the maps; those cases compiled at
default limits. The final consumer stores the two maps in a checked opaque pair
with explicit proofs that they are exactly the original scalings. It retains
the full arbitrary-stage section equality and both nonidentity proofs. The
successful isolated check took 1.57 seconds at default limits. Hiding only the
torsor did not help and was not adopted. These measurements identify a concrete
normalization cost; they do not establish an optimal encoding or minimum budget.
