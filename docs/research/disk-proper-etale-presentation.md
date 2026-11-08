# The disk's external proper étale presentation

Issue [#368](https://github.com/VladimirMarko/conaled/issues/368) connects the
existing quarter-turn action and ordinary quotient chart arrows to a concrete
proper étale presentation. The construction reuses the action and its smoothness,
stabilizers, and tangent maps. It adds the external topology and smooth arrow
families missing from the [ordinary comparison](ordinary-open-quotient-comparison.md).

## Manifolds, structure maps, and properness

[`DiskPresentation`](../../Applications/Orbifolds/DiskPresentation.lean) uses
`Disk`, the existing open unit disk in ℂ, as its object manifold. Its arrow
manifold is `C4 × Disk`. C4 has its existing finite Hausdorff topology, hence is
discrete and compact. `labelCharts` gives it the zero-dimensional charts from
Mathlib; the product charts model arrows on `(Fin 0 → ℝ) × ℂ`. The disk and arrow
space have their inherited Hausdorff, second-countable smooth manifold structures.

An arrow `(g,x)` has source `x` and target `g • x`. Its inverse is
`(g⁻¹,g • x)`; its identity at x is `(1,x)`. Following `(g,x)` by `(h,g • x)`
gives `(h*g,x)`. `composableEquiv` identifies composable pairs with
`(C4 × C4) × Disk`; `compose_smooth` proves smoothness in those coordinates.
`unit_smooth` and `inverse_smooth` prove the other structure maps smooth.
`homEquiv` identifies each anchor fiber with the existing Mathlib action
category's hom type. `ofHom_ident`, `ofHom_comp`, and `ofHom_inverse` connect
these operations to that groupoid's categorical laws.

`sourceChart g` restricts source to the open component `{g} × Disk`, with
inverse `x ↦ (g,x)`. `targetChart g` composes it with the diffeomorphism
`rotation g`, using the existing `disk_action_smooth` for both g and g⁻¹.
These actual partial diffeomorphisms prove `source_etale` and `target_etale`.
The use of a zero-dimensional label model leaves the real dimension at two.

`anchor_proper` concerns the actual map `(g,x) ↦ (x,g • x)`. Properness means
Mathlib's `IsProperMap`: continuity together with the cluster-point lifting
condition, called Bourbaki properness in the
[pinned source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Maps/Proper/Basic.lean).
The anchor is continuous by the proved smoothness of source and target.
Composing it with the first projection gives `(g,x) ↦ x`, which is proper
because C4 is compact (`isProperMap_snd_of_compactSpace`). The intermediate
space `Disk × Disk` is Hausdorff, so `isProperMap_of_comp_of_t2` proves the
anchor proper. This proof does not infer properness from finite stabilizers
and does not substitute a compact-preimage convention requiring an additional
equivalence theorem. `proper_etale` publishes the resulting conjunction.

## Exact arrow comparison

[`SmoothDiskPresentation`](../../SquareKit/SmoothDiskPresentation.lean) gives
`chartEquiv` for every ordinary principal-open domain U and smooth disk maps
m,n. Its target `Family U m n` is independently specified by a locally constant
forward label g satisfying `g(x) • m(x) = n(x)`, after the existing `diskPoints`
coordinate identification. Its source is the actual quotient chart arrow type.
Both inverse laws retain exact arrows, not isomorphism classes.

`smoothChartEquiv` further identifies those quotient arrows with **all** smooth
maps `ordinaryOpen U → C4 × Disk` having source m and target n. In one direction,
local constancy makes the discrete component smooth, and `openMap_contMDiff`
and the smooth complex coordinate identification make the disk component smooth.
In the other direction, continuity into discrete C4 recovers local constancy;
the specified source determines the second component. The construction therefore
neither assumes the desired comparison nor limits the image to constant labels.

The existing quotient convention is `m = k • n`, so its forward action label
is `k⁻¹`. `ForwardLabel` proves identity, inverse, composition, and restriction
laws for arbitrary groups and actions using the existing ordinary label laws.
In particular, arrows f then g have forward label `label g * label f`.
`chartEquiv_comp`, `chartEquiv_ident`, and `chartEquiv_inverse` preserve the
family operations. Evaluating a family yields the existing action category's
arrow; `hom_comp`, `hom_ident`, and `hom_inverse` preserve its operations.

`chartEquiv_restriction` compares the actual reindexed quotient arrow with the
restricted external arrow map, including its source coordinate. The family
restriction laws include identity, successive restriction, composition, and
inverse. Family identity, inverse, and associativity laws are proved as exact
equalities. No use of C4 commutativity enters the generic label-order argument.

## Descent and controls

`canonicalRecovery_comparison` composes the new equivalence with the existing
`canonicalArrowEquiv` and `recoveryArrowComparison`. For two admitted locally
surjective split covers of an ordinary domain and canonical data of global
chart objects, either recovery route gives the same smooth external family.
The existing object comparison and its naturality remain the ones proved in
`SmoothOrdinaryCoverRecovery`. This does not construct change-of-cover functors
on arbitrary independently supplied descent data or descent over all manifold
bases. The doubled-origin ineffective torsor and its obstruction to a global
chart remain in the imported ordinary comparison examples.

The [checked controls](../../Examples/DiskPresentation.lean) include:

- Four origin families through `chartEquiv`; the selected forward origin arrow
  has precisely its original geometric label.
- Only the identity family at each nonzero point. The quarter-turn does not fix
  the explicit half-radius point.
- Distinct origin arrows with identical anchor values. Properness does not make
  the anchor injective or replace the action groupoid by a coarse orbit space.
- The existing coefficient derivative equals the derivative of `rotation g`.
- The disconnected sign-domain arrow has labels 1 and the inverse quarter-turn.
  Its actual canonical recovery through the named refinement returns the same
  smooth family.
- Ineffective labels remain distinct in the existing ineffective representation.
- A trivial S3 action constructs actual quotient arrows for swaps 0/1 and 1/2.
  The generic forward-label law sends their composite's 0 to 2; reversed order
  sends it to 1. This detects the order error hidden by C4 commutativity.

These arrows are symmetry identifications with retained labels. They carry no
time parameter, trajectory, or claim about physical disk motion. The separate
motion and coarse-orbit constructions retain their own observation contracts.

## Statement review and boundaries

The external theorem has no caller-supplied properness or étaleness field.
All topology, charts, action smoothness, compactness, and Hausdorff hypotheses
are supplied by the concrete instance. The smooth-family equivalence quantifies
over every admitted U,m,n, including empty and disconnected domains. Its reverse
direction requires exactly smoothness and the two endpoint equations, rather
than preselected local labels. The noncommutative example checks the same public
forward-label composition law used by the disk comparison. The canonical recovery
claim is restricted to the data and arrows actually transported by that API.

This adds an external presentation theorem and an ordinary chart-arrow comparison
to the internal quotient construction. It does not identify internal finiteness
or infinitesimal properties with properness, construct a full Myers interpretation,
prove a general orbifold equivalence, or provide the separately owned joint
higher/smooth model. No performance or constructive-foundation claim follows
from these classical, noncomputable constructions. Build and exhaustive audit
receipts are recorded with the candidate review, separately from these statements.
