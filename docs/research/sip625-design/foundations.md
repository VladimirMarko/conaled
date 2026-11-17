# Foundations assessment for #625

Recommendation: build a native structure-family interpretation over universal El and a reusable total Sigma-path theorem, then prove the semantic preservation comparison. Do not promote the existing fixed-equivalence theorem to total SIP by taking a host Sigma over its parameters. Existing native univalence supplies the necessary equivalence of bases, but the dependent comparison is additional mathematics.

This assessment checked declarations in the current source. The proof strategies below are proposed, not Lean-checked proofs. No project build or scratch proof was run.

## Existing mathematical contracts

`Presheaf.StructureIdentity.family` requires a natural isomorphism `j : A ≅ constantFamily Γ S`. Its fiber is `F.Data (A.obj x)`, but every transition is manufactured through that global presentation. `identityEquiv` classifies sections over one presented line and fixed host equivalence. Its recovery proof uses uniqueness of sections in that presentation. The Cartesian implementation similarly restricts this line. Neither defines a structure family over arbitrary universe codes or classifies arbitrary paths between total structured objects.

Both models already have their own `SmallUniverse.NativeUnivalence.univalence`, with a `HomotopyEquivalence` of the actual `pathToEquiv`. Both also expose `leftInverseAt`, retaining arbitrary native universe paths and comparison to the chosen ua. These are the right base theorems. The De Morgan `NativeUnivalenceTotals` uses `NativePathSingleton.contractible`, `HomotopyContractible.fiberwiseRetract`, and `HomotopyEquivalence.ofContractibleTotals`. Those are reusable proof principles, not yet a theorem commuting an arbitrary dependent structure field with univalence.

`LargeFamilyConstructors` supplies De Morgan small presentations and admitted Sigma/Pi/Path codes over a context in universe `u+1`, with fiber universe `u`. Its `Result` retains code, decoder isomorphism, filling and lawful filling. This directly fits native signature interpretation over the universe context. Its Pi smallness proof uses represented restrictions; no smallness of the context is assumed. Sigma fillers also exist independently in the Cartesian model (`CartesianDependentFilling`), although matching larger-context admission must be checked/implemented under #605.

## Which gaps are constructions, and which are semantic laws?

1. **Construction:** interpret `Description.carrier` by universal El, fixed types by admitted constant families, products by Sigma with a reindexed second factor, and functions by Pi with a reindexed codomain. Keep a decoder comparison and lawful filling at every constructor. This is a native family at all carrier codes, unlike applying `Transport.Data` pointwise.
2. **Construction:** form the total structured-object family `Sigma U Struct`, and its actual native path family. The carrier universe is large; do not claim the total is itself a small code in the same universe. A large family with lawful filling suffices for its path theorem.
3. **Law/theorem:** decompose native paths in `Sigma U Struct` into carrier paths plus dependent structure paths, naturally in substitutions. This must recover native path witnesses, not merely endpoint values.
4. **Law/theorem:** use each model's own univalence to change the carrier-path parameter to the native equivalence family, transporting the dependent structure-path field along the supplied native inverse homotopies. Merely substituting `ua(e)` changes the base and loses the original path unless the dependent field is transported through `leftInverseAt`.
5. **Law/theorem:** relate dependent paths over `ua(e)` to independently defined preservation of native structure data. For function descriptions this includes contravariant argument transport and native function extensionality. A correspondence defined to be the left-hand dependent path is useful infrastructure, but does not discharge semantic SIP by itself.
6. **Construction and laws:** native formulas, proposition-valued law families, dependent solution fields, and their admitted filling. Host `Formula.invariant` proves invariance of host formulas under host bijections; it supplies no native fibration over arbitrary carrier paths.

## Critical scope checks

An arbitrary host `Transport` is a functor on types and bijections. Native El transitions are restriction maps, generally not bijections. There is no justified generic construction sending such a `Transport` to a native family over all codes. Syntax-directed `Description` avoids this problem because native Sigma/Pi have the necessary restriction behavior.

`Formula.equal` currently means host equality in `Description.Data X`. Replacing it with pointwise `PLift` equality over arbitrary native carriers is not a valid automatic admission: endpoints connected by native paths need not be host equal, and filling such a family would force inappropriate discreteness. Interpret equality by native paths; require sethood where a proposition-valued law is needed, or retain higher law witnesses as data. Do not silently truncate them.

`.fixed Prop` currently means a constant host type whose elements are Lean propositions. This is adequate for recovering the old discrete relational examples, but is not a native universe of propositions. A semantic implementation must state this distinction, and its `holds` family must be constructed and shown lawful. Using constant host Prop does not make all native predicates available.

A discrete-carrier subuniverse is possible only after constructing the native subfamily, showing it is closed under path transport, providing its lawful filling, and restricting univalence through the inclusion. A host predicate on universe codes or a set of chosen constant codes alone does not supply this. Native sethood and the present `PathDiscrete` are different requirements: `PathDiscrete` collapses path endpoints to host equality under every substitution. Avoid assuming a set-valued cubical object has this stronger property.

## Practical theorem sequence

First construct native interpretation for descriptions with actual large-context admission. Exercise `.carrier`, a selected point plus unary operation, and a function whose domain itself contains functions. These ensure the interpreter handles restriction data and negative positions.

Then prove a generic total structured-path theorem for any supplied lawful native family `S` over `U`. Its right side can initially be `Sigma (native Equiv A B) (dependentPath S (ua e) s t)` with the exact selected equivalence witness. This is a genuine total internal comparison and reusable prerequisite, but its name/documentation must say it uses ua-dependent structure paths. It is not yet independent semantic isomorphism.

Next establish the native preservation family recursively and prove its fiberwise equivalence to the ua-dependent structure path. Compose with the total theorem. Native homotopy equivalence is the target conclusion; a host `Equiv` of closed sections is only a later observation in discrete cases.

Add laws by a separate proposition-family extension theorem: if an admitted law family over structures has native proposition fibers, adjoining its witness preserves SIP once both endpoints supply it. The proof must supply dependent paths of the law witnesses. This isolates the useful general theorem from host proof irrelevance and leaves room for genuinely dependent non-proposition data through ordinary Sigma.

Recover #622 by decoder comparisons at constant carriers, including the existing selected state, operation, invariant and proof fields. The old exact section-recovery theorem remains the discrete specialization, not a claim of strict recovery for arbitrary higher native paths.

Finally compare models with explicit family/constructor/path/equivalence maps. Cartesian univalence must be used in the Cartesian total theorem. Restricting a De Morgan ua gives one Cartesian path, but identifying that path with Cartesian chosen ua requires a native comparison and its dependent action. Existing `Cartesian.StructureIdentity.restrictionEquiv` proves neither this choice comparison nor general total equivalence. Composition/inverse laws should be stated as native paths where strict witness equality is unavailable.

The minimal useful implementation slice is native descriptor admission plus one total theorem for admitted native `S`, with the semantic preservation and law-family obligations kept explicit. The complete issue still includes those obligations, old-client recovery, and model comparison; this slice alone is not a basis for closing #625.
