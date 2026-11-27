# Native sethood of whole structured path families

Issue [#700](https://github.com/VladimirMarko/conaled/issues/700) implements the
closure prerequisite selected by [#697](native-coherence-contracts.md). Both
cubical models derive native sethood of the entire family of paths between two
structured objects when the target carrier is a native set. The structure
universe itself is not assumed to be a set.

The construction uses the selected total correspondence from the source base
`7cff88a9a1f41e1e6177ec0403a4ae8f3de555d4`. It covers the existing description
grammar, including pointed endomorphisms and raw lattices. Dependent structure
descriptions and proof-relevant laws need separate arguments.

## Closure and transport

[HomotopyLevelTransport](../../SquareKit/Internal/Cubical/HomotopyLevelTransport.lean)
and its [Cartesian counterpart](../../SquareKit/Internal/Cubical/CartesianHomotopyLevelTransport.lean)
provide these steps:

1. `isEquivIsProp` introduces two generic witness sections over the double
   extension by `isEquiv f`. The first is an inhabitant at that substitution,
   so `substitutedWitnessContractible` applies even when `f` has no global
   equivalence witness. Its contraction supplies the path to the second.
2. `pathMapEquivalence` derives the equivalence on paths from contractible
   based totals. These totals are the fibers of the identity and of the
   supplied equivalence. Specializing their dependent map at the first endpoint
   gives the required path-map equivalence, with the public substitution
   isomorphisms retained.
3. `sourceIsProp` reflects proposition data through a selected inverse and
   its left recovery. `sourceIsSet` applies this to path-map equivalences.
   `targetIsSet` transports forward through the actual native equivalence.
   The original model uses its existing selected inverse equivalence. The
   Cartesian proof carries proposition data forward with contractible fibers,
   then uses `changeEndpointsProp` to transport along the two actual right
   recovery paths. This endpoint transport uses the lawful filling of the
   native proposition family over the interval.
4. `sigmaIsSet` uses the existing proposition-extension path equivalence.
   `equivIsSet` combines maps-into-a-set sethood with the complete witness
   proposition fibers. Neither step replaces native path data with host
   `Subsingleton`.

The closure declarations accept arbitrary families and lawful fillings, with
no constant presentation requirement. The Cartesian selected inverse is
currently provided by the existing native preservation module; this import
reuses that interface without moving its owner or migrating clients.

## Whole paths and recovery

[NativeStructureSethood](../../SquareKit/Internal/Cubical/NativeStructureSethood.lean)
and its [Cartesian counterpart](../../SquareKit/Internal/Cubical/CartesianNativeStructureSethood.lean)
combine complete equivalence sethood with `equivalenceFieldsIsProp`.
`wholePathsIsSet` transports the resulting sethood through `explicitMap` and
`explicitEquivalence`. The existing `explicitInverse`, `explicitLeftInverseAt`
and `explicitRightInverseAt` remain the complete recovery interface.

`wholeThreePath` takes fixed whole paths `p,q` and two already supplied terms
`H,K : Path (Path O x y) p q`. It returns a path between `H` and `K` with those
exact endpoints. It does not construct a first 2-path between arbitrary whole
paths. Constructing the finite associativity and unit boundaries is still
[#701](https://github.com/VladimirMarko/conaled/issues/701)'s obligation.

[Checked applications](../../Examples/NativeStructureSethood.lean) use actual
integer admissions from `Examples.NativeLatticeTransport` in both models.
They instantiate whole-path sethood, both complete recovery directions, and a
3-path between reflexivity and the concatenation of two reflexivities at a
selected nonidentity integer translation path. The lattice specialization
compares the existing `LatticeControl.compare` 2-path with another supplied
parallel 2-path.

The recovery control checks the entire structured equivalence as endpoint:
its map, contractible-fiber witness, and preservation fields. Equality of
forward maps is an equality of only one projection. Converting that observation
into whole-record recovery requires the native witness and preservation
arguments; the forward-map equality is not itself the complete recovery term.
No inequality of independently selected witnesses is claimed.

## Failed probes and corrections

The initial original-model path-map probe used `JA` rather than `JA.symm`
when conjugating the specialized based map. Its source did not match the
requested path family. After correcting the orientation, `rfl` still did not
prove the composite map equation because the inverse of the dependent product
substitution isomorphism is not definitionally the pointwise map. The final
proof uses `piInverseValue_map` under `congrArg (f.app y)`. Both probes concern
the equation

```lean
JA.inv ≫ Functor.whiskerLeft σ.mapElements (BasedPathMap.map f b) ≫ JB.hom =
  pathMap f a b
```

under an arbitrary native equivalence and lawful source/target fillings.
No new mathematical hypothesis was needed. An implicit `sigmaFst x` in the
dependent-total proof also left its fiber family unresolved; specifying
`(B := B')` closed that elaboration obligation.

A direct Cartesian transcription reported `Invalid field reindex` for
`(generic W).reindex ...`, and `Unknown identifier mapsFilling`. Cartesian
terms are subtypes, so the checked proof uses `Term.reindex`; its map-family
filling is the existing `piFilling` on the reindexed target. The Cartesian API
also lacks the original model's generic `selectedInverseEquivalence` helper.
The forward transport above avoids making that missing helper an assumption.
These were encoding/API differences, not evidence of mathematical nonexistence.
No resource override or new axiom was introduced.

The application probes also exposed an omitted `StructureIdentity.Native`
namespace, which made `objects`, `objectOf` and `objectsFilling` unavailable.
The resulting dependent-type errors cascaded into a default 200,000-heartbeat
failure. Correcting the namespace resolved those name errors. Actual admissions
are applied after proving the parameterized helpers.

A redundant recovery assertion attempted to check the existing complete
recovery term against an endpoint spelled through the separate `selected`
alias:

```lean
example : Term (homogeneousPath
    (StructureIdentity.Native.equivalences description
      (fromSystem admitted).fields (toSystem admitted).fields)
    (Term.map (explicitInverse description admitted.code (fromSystem admitted).fields
      admitted.code (toSystem admitted).fields) (selected admitted))
    (move admitted 0 1).native) := completeEquivalenceRecovery admitted
```

Under the same generic integer admission, this reported `maximum recursion
depth has been reached` in the original model and a 200,000-heartbeat `whnf`
timeout in the Cartesian model. A probe with
`simpa only [selected, Coded.path, fromSystem, toSystem]` was stopped without a
successful result. The retained `completeEquivalenceRecovery` instead uses
`explicitLeftInverseAt` with its exact supplied native equivalence; it does
not depend on this extra alias-normalization assertion. `completePathRecovery`
separately checks `explicitRightInverseAt` at `selected`. Both are instantiated
at actual admissions. No failure above is a separating mathematical control,
and none justifies changing the recovery contract.
