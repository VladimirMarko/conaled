# Restriction and algebra recovery

[Restriction.lean](../../SquareKit/Lawvere/Restriction.lean) packages the existing
restriction operation as a contravariant functor. For a fixed target category
`C : Type w` with hom universe `z`, its type is

```lean
Model.semantics C : Theory.{u,v}ᵒᵖ ⥤ Cat.{max u z, max u v w z}
```

It sends a theory to its entire model category and a theory morphism to the
restriction functor. `Model.restrict_id` and `Model.restrict_comp` are equalities
of functors, including their action on natural transformations. These laws are
strict because the current representations of functor composition and model
records reduce to the same data. No target finite-product assumption is added:
each model retains its own preservation proof. The earlier object-level API
and all Type-valued clients remain available.

## Operation maps

`Operations.Algebra.restrict` reuses carrier-indexed action restriction and
keeps each homomorphism's underlying function. Identity and composition hold
exactly. `restrict_modelFunctor` identifies the entire functor obtained by
interpreting restricted algebras with categorical model restriction.

`Recovery.coordinates_inv_restrict` proves that tuple assembly is unchanged
by an operation map. It uses preservation of variables and the universal
property of the interpreted powers, including the empty power.
`act_restrict` then compares every recovered operation.
`restrictionComparison` packages the resulting algebra isomorphisms naturally
in model maps. Its components act as the identity on the generator carrier;
`restrictionIso_id` and `restrictionIso_comp` prove identity and composition on
the whole algebra isomorphisms.

## General theory morphisms and chosen generators

For `F : Hom T U`, `F.operations` is the induced map from `T.operations` to
`U.operations`. It reuses the finite-power normalization from
[presentation universal properties](lawvere-universal-properties.md).
`F.skeletonRestrictionIso` compares the two orders of restricting to the
chosen context categories. The construction uses the shared
`Model.precomposeIso`, which transports a natural isomorphism of source
functors to a natural isomorphism of model restrictions in any target.

`Model.originalRecovery T` extends the existing `M.algebra` adapter to model
transformations. It retains exactly `M(T.generator)` as the carrier;
`originalRecovery_map_apply` identifies each map with the transformation's
component at that generator. `originalRecoveryIso` connects this adapter to
recovery on the chosen one-fold power. Thus the existing algebra/model
equivalence and the original-generator adapter remain connected without
assuming their carriers equal.

`originalRestrictionComparison` compares algebra restriction after original
recovery with recovery after categorical restriction. It is natural in all
model transformations. On a carrier element its map is exactly
`M.map F.generatorIso.inv`, as proved by
`originalRestrictionComparison_apply`. Identity and composite theory changes
preserve these comparison maps. `originalCompositeIso` compares the two
induced algebra restrictions over model inputs; `originalCompositeIso_coherence`
proves that its triangle commutes as natural isomorphisms, and
`originalCompositeIso_apply` proves that it changes no carrier elements.
These comparisons account for the chosen powers and generator isomorphisms;
they do not assert literal equality of nonskeletal recovery representations.

## Applications and scope

[LawvereRestriction.lean](../../Examples/LawvereRestriction.lean) constructs an
interpretation that sends involution to the identity and retains zero and
addition. It proves that this interpretation is not the identity operation map.
After two such restrictions, algebra recovery still returns zero and the
binary calculation `3 + 4 = 7`. Restriction and recovery also retain the
nonidentity doubling model transformation. Other checks cover full functor
composition in an arbitrary target, composed comparison isomorphisms, and the
original-generator comparison in the existing tagged nonskeletal theory.

The shared constructions derive tuple, operation and morphism compatibility
from finite-product preservation and the given generator comparison. Callers
supply no separate recovery-commutation axiom. Some concrete Lean expressions
still require an explicit `Fin 1` coordinate and scalar type; the carrier-indexed
action interface remains the simpler choice for scalar evaluation. The results
establish mathematical reuse and coherent recovery, not measured author effort.

This completes [#615](https://github.com/VladimirMarko/conaled/issues/615).
[Sums and tensors (#616)](https://github.com/VladimirMarko/conaled/issues/616)
remain a separate construction. Scalar algebra recovery concerns `Type w`;
restriction and precomposition comparisons retain arbitrary target categories.
