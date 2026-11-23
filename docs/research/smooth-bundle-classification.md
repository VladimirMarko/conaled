# Ordinary discrete principal bundles and smooth sheaf torsors

The classification in `SquareKit/SmoothBundleClassification.lean` packages the
ordinary reconstruction from #640 and all-map correspondence from #641 as an
explicit equivalence. The ordinary category retains each total manifold,
projection and action. Its arrows are all smooth equivariant maps over the base;
invertibility is proved from principality.

## Supported objects and maps

Fix `G B : Type`, a group structure and discrete topology on `G`, and a smooth
boundaryless real manifold structure on `B` with model `Space n = Fin n → ℝ`.
`SmoothPrincipalBundle.Ordinary n G B` packages a varying `Total : Type`, its
topology and smooth manifold structure with the same model, its `G` action, and
the existing `Bundle` local triviality data. Objects form `Type 1`; morphisms are
in `Type`. The codomain is the existing full `SheafTorsor.Torsor` category for
`locallyConstantGroup G` over `ManifoldRealization.object n B`.

There is no finiteness or countability hypothesis on `G`, and no compactness,
Hausdorffness, second countability, nonemptiness or global triviality hypothesis
on the base or total space. `reconstructed_t2Space` requires `T2Space B`;
`reconstructed_secondCountableTopology` requires `SecondCountableTopology B`
and `Countable G`. These are conditional consequences.

The category uses the library's left-action convention. The existing
`SmoothBundleRightAction` conversion handles conventional right actions. The
classification does not construct extension of structure group.

## Chosen recovery and chart comparisons

`Ordinary.realization` maps every ordinary bundle map through `mapEquiv`.
`Ordinary.reconstruction` uses the actual `SmoothTorsorReconstruction.Total`
and bundle for each torsor. Its map on an arrow is the unique ordinary map
whose realization is conjugation by the specified recovery arrows.
`unit` and `counit` are natural isomorphisms, and `classification` supplies the
triangle law. `unitDiffeomorph` is an actual equivariant diffeomorphism over the
base. `totalRecovery`, `totalRecovery_projection` and
`totalRecovery_equivariant` compare full sheaves at every test stage, including
all generalized group labels.

`choiceComparison` compares independently supplied ordinary realizations of
the same torsor. Its realized arrow is prescribed, with uniqueness, identity
and composition laws. `chartRealization` observes the classification on any
`ChartFamily`; `chartRealization_obj` identifies its object with the original
bundle's descended torsor transported by the actual atlas comparison.
`chartRealization_common` gives the common-refinement interpretation.
`chartChoiceComparison` has the same uniqueness and coherence laws, and
`chartChoiceComparison_of_global` identifies it with the ordinary comparison.
These are specified isomorphisms; independently selected charts and recovery
objects are not asserted to be definitionally equal.

## Actual base change

`SmoothBundleClassificationPullback.lean` uses the actual ordinary fiber product
`{z : B' × E // f z.1 = projection z.2}`, with the existing sheet-derived atlas.
Its base dimension `m` may differ from `n`. A second base change may have any
finite dimension `k`. `pullbackFunctor` acts on the actual pairs.
`pullbackIdentity` and `pullbackComposition` are natural ordinary isomorphisms;
the latter flattens nested pairs. `pullbackRealization` is natural on all bundle
maps. Its identity and composition laws include the equality transports for
`ManifoldRealization.map_id` and `map_comp`.

`reconstructionPullback` is a natural ordinary isomorphism between reconstruction
after sheaf restriction and the actual pullback of the chosen reconstructed
bundle. Its realization is specified through `pulledBackRecovery`. None of
these results assumes general transverse-pullback preservation.

## Independent targets and the associated-bundle boundary

`Ordinary.WithTarget n d G B M` adds an independently supplied smooth manifold
`M : Type` with model `Space d`, a smooth action of `G`, and an equivariant
smooth map from the total space. The action may have stabilizers or be entirely
ineffective. Morphisms are the complete existing `TargetMap` type.
`WithTarget.classification` is an equivalence with the existing full
`SheafActionQuotient.Object` category. Reconstruction derives the target map
from the supplied sheaf quotient, and `reconstructed_target_map` identifies its
whole realized arrow with the original quotient map through `totalRecovery`.
The forgetful functors commute with realization and have a specified natural
comparison for reconstruction.

Target base change uses composition with the second projection of the actual
fiber product. The comparison retains the full quotient arrow and its target,
including identity/composite transports and a natural reconstruction comparison.
This supplies ordinary target-preserving data for the implemented
[associated-sheaf construction](associated-sheaf-bundles.md). #669 constructs the
sheaf quotient and arbitrary structure-group extension, with ordinary comparisons
for regular and singleton fibers. General ordinary discrete associated spaces
remain [#676](https://github.com/VladimirMarko/conaled/issues/676); the selected
positive-dimensional geometry is the future branch
[#677](https://github.com/VladimirMarko/conaled/issues/677).

## Checked consumers

`Examples/SmoothBundleClassification.lean` connects the public equivalences to
C4 rotations, recovery of the nontrivial square cover with its no-continuous-
section obstruction, and an empty base. Successive scale-two and scale-three
maps are proved nonidentity; the composite comparison retains its actual nested
pair coordinates and full realized comparison equation. A map from `Space 2`
to `Space 1` checks independent base dimensions. The nonlinear target
`x ↦ (x, x²)` has dimension two over a one-dimensional base and is recovered
with its values intact.

`Examples/SmoothDoubleOriginManifold.lean` constructs an ordinary smooth line
with two origins by gluing two lines along their punctured domains. Its chart
inclusions are smooth open embeddings, the origins are distinct, and the
space is not Hausdorff. Classification of its ordinary identity bundle gives
a recovered total manifold diffeomorphic to that actual base and therefore
non-Hausdorff. This is an ordinary-manifold control; no identification with the
older sheaf pushout parameter is needed or claimed.

The integrated entrypoint retains the earlier finite-cover, torsor and target
consumers. Exact-candidate build, exhaustive axiom audit and independent
Standards/Spec review are recorded in the implementation's acceptance evidence.
