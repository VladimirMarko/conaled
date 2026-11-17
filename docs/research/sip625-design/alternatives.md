# Alternatives assessment for #625

Recommendation: build the native grammar over the universal decoder, with a general native total-space theorem underneath it. Preserve `Transport` as the set-level specialization and comparison API. A discrete-carrier subuniverse is a mathematically legitimate alternative, but the current code does not supply its admission or univalence, so it is not an established shortcut.

This is declaration-level source inspection, not a checked new proof. No build or scratch Lean experiment was run. Proposed constructions below still require formalization.

## Why the existing transport realization does not extend directly

`Presheaf.StructureIdentity.family` builds a family from `F.Data (A.obj x)` using `F.map (j.app x).toEquiv`, where `j : A ≅ constantFamily Γ S` is one global chart. `presentation` then identifies the whole structure family with the constant family `F.Data S`. Its `identityEquiv` classifies paths over one already-selected carrier line; `uaIdentityEquiv` fixes `f` and the supplied `E` before classifying structure paths.

Dropping `j` leaves a real missing operation: a presheaf restriction `A.map f` is a function, whereas `Transport.map` accepts an equivalence. The function constructor has negative carrier occurrences, so arbitrary functions do not suffice. This is a mismatch between the available interface and presheaf restriction, not a Lean universe inconvenience.

Using native Pi solves that mismatch by retaining values at all future substitutions. `SmallPresentation.Data.FunctionValues` and `functionValues_injective` expose exactly this distinction: native function elements include restriction-indexed values. In general they are not the plain host function space between the two current fibers. A pointwise host `Description.Data` interpretation over every decoder fiber would therefore claim the wrong semantics for function fields.

## Native grammar route and existing machinery

`LargeFamilyConstructors.lean` already gives the De Morgan admission contract needed over the larger universe context:

- `SmallPresentation.Data.sigma`, `.pi`, and `.path` prove explicit smallness. Pi smallness counts cube restrictions and small arguments, not the size of the ambient universe context.
- `LargeConstructors.Result C` retains `code`, `decoding`, `filling`, and `lawful`.
- `LargeConstructors.construct` admits a native family from its small presentation and lawful filler.
- `LargeConstructors.sigma`, `.pi`, and `.path` compose the existing decoder fillers and their lawfulness proofs.

Interpret `.carrier` by the universal `liftedDecode`, `.fixed A` by an admitted constant family, products by Sigma with a reindexed second component, and functions by Pi over the reindexed output. Reindexing and decoder comparison are part of this interpreter. Comparing its closed discrete instances to `Description.Data` is a theorem, particularly for the function constructor, rather than a definitional expectation.

The existing contractible-total machinery is reusable after the admitted family exists. `NativeUnivalence.univalence` and `Cartesian.NativeUnivalence.univalence` already provide each model's own carrier equivalence. `NativePathSingleton.contractible`, `HomotopyContractible.fiberwiseRetract`, and `HomotopyEquivalence.ofContractibleTotals` provide the relevant native contraction/retract pattern. They do not themselves identify operation preservation with the dependent structure path. That identification must be proved through the grammar, or through a separately supplied structural relation whose equivalence with that path is proved.

An abstract theorem defining structure isomorphism to mean transport along `ua` followed by a dependent path can be useful infrastructure. Alone it does not recover the independently defined `Description.Preserves`, operation-intertwining equations, relational equivalence, or the state proof-field contract. Keep those comparison obligations visible.

## Laws and sethood require an explicit semantic choice

`Formula.equal` currently means host equality, `Formula.holds` evaluates a host `Prop`, and `Specification.Model` is a host subtype. Host proof irrelevance justifies the existing `Subtype.ext` proofs. These are correct set-level theorems and do not establish that arbitrary native path fields are propositions.

Over general carriers, interpreting equation laws as native identity gives potentially proof-relevant fields. To retain ordinary monoid/lattice law semantics, supply internal sethood of the carrier and derive the required proposition properties, or state a broader proof-bearing structure whose law witnesses remain data. A constant native family on host `Prop` can recover the old relation fragment, but it is not automatically the internal universe of all proposition families. The evaluation family and its admission still need construction.

The existing `PathDiscrete` says that every native path under every substitution forces host equality of its endpoints. It is not a declaration of internal sethood, and no inspected theorem identifies it with a univalent subuniverse of sets. Replacing the sethood requirement with this predicate without a comparison proof would change the contract.

## Discrete-carrier subuniverse alternative

A route based on families whose restriction maps are isomorphisms could define the structure restriction via `Transport.map`, avoiding grammar-specific native Pi initially. It would support arbitrary equivariant set-level `Transport` data, including existing specifications. To make this a native internal SIP, however, it needs all of the following proofs:

1. A substitution-stable carrier-code predicate or native subuniverse, with lawful filling and the intended closure under carrier equivalence.
2. A small native structure family over that entire subuniverse, including uniform filling across its arbitrary cubes, without choosing one global trivialization.
3. A comparison showing that the ambient carrier `ua` and all higher recovery paths remain in the subuniverse, thereby deriving its own univalence from ambient univalence.
4. A total structured-object path/isomorphism theorem retaining automorphisms and native equivalence witnesses, followed by the existing concrete preservation comparisons.

None of these follows merely from the host groupoid action `Transport.map_refl/map_trans`. A constant family on the host type of pairs `(S, F.Data S)` is a failing candidate: its native paths cannot identify distinct host carriers via an arbitrary bijection. Adding a selected global chart instead returns to the current fixed-line construction. A subuniverse of genuinely locally varying discrete carriers avoids those particular failures, but remains a new foundational construction with its own coherence and filling work. I found no existing admitted subuniverse API in the inspected cubical modules.

This alternative should remain open for broader arbitrary equivariant data. It should not displace the native grammar solely to avoid #605's constructor work; it incurs another substantial admission problem and narrows the native fragment unless that restriction is part of the stated result.

## Concrete implementation order and acceptance cases

First deliver the De Morgan native data interpreter with its admission evidence at the universal carrier context. Include a function case that consumes `LargeConstructors.pi` and a closed discrete decoding comparison, so the first slice demonstrates the missing capability. A pointed-carrier specialization of the general total theorem is a useful next calibration: carrier equivalences must actually move the selected point, and arbitrary carrier paths must be accepted. The theorem must quantify over native objects and substitutions rather than enumerate host equivalences at the terminal context.

Then derive the grammar's native preservation correspondence, add explicit law-family and sethood contracts, and recover the monoid, order, lattice and state clients. Existing `stateModelEquiv`, `state_transport`, `state_preservation`, and `statePathEquiv` in `Examples.CompositionalStructureIdentity` are useful endpoint adapters. Retain the complement rejection cases and noncommuting swaps as direction/composition checks; add native total-path recovery so these do not remain only host transport checks.

For Cartesian admission, the inspected tree has no analogue of `LargeFamilyConstructors`; the brief identifies #605 as its owner. The Cartesian completion theorem already establishes independent univalence, but the current `Cartesian.StructureIdentity` restricts a De Morgan carrier line. Extend the admitted constructors or use a separately proved realization contract, then instantiate the total theorem using Cartesian univalence. Do not claim that restriction of a selected De Morgan `ua` equals the independently selected Cartesian `ua`; state and prove the native comparison homotopy needed by clients, retaining witnesses and dependent fields.

These slices are progress toward #625. Full completion additionally requires both model instances, the law/sethood admission, native composition/inverse comparisons, and the retained client/support-lattice contract. No inspected declaration eliminates those obligations.
