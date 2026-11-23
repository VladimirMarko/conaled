# Shared parameters for Type-family sums and products

[#518](https://github.com/VladimirMarko/conaled/issues/518) extends the bounded
[local-universe experiment](../../SquareKit/LocalUniverses.lean) with dependent
products. Both Sigma and Pi now use the same constructed input representation
and naming map. The original Sigma decoding and strict substitution proofs
remain `rfl`. Pi recovers the existing native operations and their selected
laws. This is useful shared setup for these two constructors; the native Type
implementation already had short strict laws, so this result does not show a
coherence saving over that implementation.

## Input representation and constructor existence

All contexts, parameters and fibers stay in `Type u`, as in the original
`Family` API. For `P Q : Type u` and `E : P → Type u`,
`DependentInput.Parameters E` is

```text
Σ a : P, E a → Q.
```

`representation` constructs the full equivalence

```text
(W → Parameters E) ≃ Σ a : W → P, (w : W) → E (a w) → Q.
```

Its inverse pairs the two names at each base point. Both inverse equations are
proved, with dependent pair elimination and function extensionality where
needed. `representation_natural` and `name_natural` retain both components
under an arbitrary `V → W`. The second name is an arbitrary function on the
first fiber; it is neither constant nor determined only by the first name.

`Family.dependentName A B` specializes this equivalence to `A.name` and
`fun γ x => B.name ⟨γ,x⟩`. Its projection equations expose the actual names;
`dependentName_reindex` includes reindexing B along the dependent lift.

Input representation alone does not prove a constructor exists. The separate
definitions `DependentInput.sigma E F` and `DependentInput.pi E F` construct
generic families with identity name and fibers

```text
Σ x : E v.1, F (v.2 x)       and       (x : E v.1) → F (v.2 x).
```

`Family.sigma` and `Family.pi` are their specializations along the same
`dependentName`. These definitions use native Type sums and functions; no
interface field supplies a constructor, representation inverse or stability
law. Generic abstraction and application work over any map into the parameter
context, including its identity. A body is supplied over its actual base:
there is no assumption that it extends to a body over every parameter.

## Operations, recovery and substitution

`decode_pi`, `lam_native` and `app_native` identify the result with
[`DependentSquares.piTy`, `lam` and `app`](../../Dependent.lean).
Application lands in B reindexed along the actual argument pairing.
`pi_beta` reuses native beta. `pi_eta_cwf` retains the stronger selected Type
eta statement: abstract the application of the weakened function to the
generic variable. It is not merely a pointwise observation at one argument.

`pi_reindex` is equality of family presentations, including their parameters
and names. `lam_reindex` and `app_reindex` retain the dependent result family;
`lam_twice` and `app_twice` compare two substitutions with their composite.
The existing identity and composition laws for `Family.reindex` still apply.

`piSections A B σ` reuses `displayCurry A.decode B.decode σ` to represent
sections of B over the substituted display as sections of the substituted
product. Both inverse laws and both directions of substitution naturality are
available. `piSections_apply` identifies the forward operation with the new
lambda wrapper. This recovers complete sections for arbitrary base maps,
without assuming a right adjoint as part of the input.

## Checked consumers and boundaries

[The examples](../../Examples/LocalUniverses.lean) retain the old Sigma and
transport cases and add these connections to the public results:

- The dependent tail has first fiber `Fin (n+1)` and second fiber
  `Fin (i.val+1)`. The product equals the existing native `Example.tighten`.
  After shift `n+1` and double `2*n`, its fiber is
  `(i : Fin (2*n+2)) → Fin (i.val+1)`. Both substitutions are proved
  nonidentity. Formation, whole functions and applications agree with the
  composite route. At `n=2`, every index returns its own value, and application
  at the last index returns 5, as independently calculated from `2*2+1`.
- Representation round trips accept arbitrary second-name functions. Product
  section round trips and naturality use the same two nonidentity substitutions.
- An empty first fiber gives a constructed product term even with empty output
  fibers, and every such term equals it. A Unit first fiber with Empty outputs
  has no product term. No inhabitance or choice premise hides either case.
- `PresentationFailure` still separates equal decoded types from equal family
  presentations. The unchanged
  [designated-map interpretation](../../SquareKit/Internal/DesignatedMap/Interpretations.lean)
  retains comprehension representation, naturality and unique pairing.
  [Source boundaries](../../Examples/LocalUniversesBoundary.lean) and
  [weak groupoid unit controls](../../Examples/WeakGroupoidUnit.lean) remain:
  distinct fillers, branch-fixing filler swaps, nonsplit lift composition,
  whole-functor substitution and native/generic agreement.

## Reuse and cost

The shared library work is the dependent input type, its naming equivalence
and naturality. Sigma and Pi both use it. Each constructor still supplies its
own fiber operation. Pi additionally needs abstraction/application wrappers,
native-law connections and the existing section equivalence. A recurring
caller supplies A, B, its body or function/argument, and substitutions; it
does not reprove representation inverses, beta/eta or section recovery.

The final construction introduces no explicit casts or transport repairs.
Explicit `Q`, `A` and `B` arguments resolve dependent inference at generic
application, lifted substitutions and native agreement boundaries. The first
attempt also needed dependent pair elimination after exposing the inverse
goal; these were Lean encoding repairs, not missing mathematical structure.
No declaration, module or global resource override was needed. The focused
four-target run reported 747ms for the core module, 780ms for its examples,
1.2s for the designated-map interpretation and 1.1s for the source-boundary
module, with cached dependencies. These are Lake-reported build durations,
not a controlled design comparison, runtime complexity or author-effort study.
Failed elaborations and successful logs are retained in the review evidence.

The definitions are constructive functions and the equivalences have explicit
maps. No separate executable extraction or runtime benchmark was performed.
Focused builds and elaborated statement inspection cover the listed contracts;
the exact candidate's integrated build, exhaustive audit and independent
reviews are recorded separately by the enclosing implementation workflow.

## Comparison and disposition

The accepted [#528 construction](compositional-univalence.md), at
`3953578fa05e34e5311780a1d4acd7dbd60690d5`, classifies complete equivalence
maps and contraction records, chooses identity/inverse/binary comparison laws
over a parameter context, and proves exact recomputation of their whole
comparison squares. That is a concrete chosen-witness coherence benefit.
Here the Type constructors were already strict: sharing the input naming
representation does not remove an analogous native chosen-filler obligation.
Neither result provides a general strictification theorem.

The [#649 comparison](classifier-dependent-presentations.md) retains all-map
display recovery and comprehension, with a proper-cover sheaf consumer.
Its later #655 section comparison transports dependent product operations
through classified display sections and keeps empty/varying fibers and
restriction laws. The present experiment shares its principle of deriving
recovery and operation laws from existing constructions, but has no sheafness,
descent or all-map classification claim. A Type product over an empty domain
does not establish the proper-cover sheaf laws in that comparison.

Retain this transparent shared input representation for Sigma/Pi and keep
the direct native APIs available. Do not migrate unrelated constructors on
the strength of this example. Varying-domain groupoid dependent products,
general local-universes strictification, higher identity semantics and resizing
are outside this contract. Any larger proposal still needs a selected weak
model, its arrow-level representation and constructor existence obligations,
and a concrete consumer under #289/#647; #235 retains preservation-interface
reassessment. Closed #107/#108 are unaffected. This bounded result informs
those owners without opening a new prerequisite or making a universal
productivity claim.
