# Finite native structure coherence contracts

Issue [#697](https://github.com/VladimirMarko/conaled/issues/697) selects a finite
extension of the existing supplied-witness interface. Derive native sethood of
whole structured path families, then construct associativity and unit 2-paths
and triangle/pentagon 3-paths. Keep the selected total correspondence and direct
construction interfaces. Do not add the desired final laws as caller fields.
The cross-model decoder investigation is separate.

This report pins inspected library sources to
`f0cac600a954fae4f340a9262ad732f6fbb30cc7`, with Lean `v4.35.0` and the repository's
locked dependencies. New higher-coherence declarations below are **proposed**,
not kernel-checked results. The retained integer probe checks the starting
construction in both models; it does not prove the proposed higher cells.

## Evidence and independent assessment

The [brief](native-coherence-contracts/brief.md) supplied the same acceptance
criteria and three candidate routes to these independent assessments:

- [Foundations](native-coherence-contracts/foundations.md): exact dimensions,
  complete witnesses, derivability and truncation transport.
- [Use](native-coherence-contracts/use.md): caller obligations, actual admissions,
  substitution and a finite declaration plan.
- [Alternatives](native-coherence-contracts/alternatives.md): direct path algebra,
  primary literature, and the beyond-common-host discriminator.

Each initial report was saved before its author saw another report or this
synthesis. Foundations and use used fresh threads. The host refused a third
fresh thread because of its thread limit, so the alternatives assessment reused
the earlier #633 review coordinator, with that exposure disclosed. These are
three independent task assessments, not model diversity or three new sessions.
They are separate from the subsequent Standards/Spec acceptance review.

All three support the set-target recovery route. Agreement does not establish
the missing closure lemmas. The decisive evidence is the existing complete
witness representation, proposition-valued preservation and both selected
recovery homotopies; the implementation discriminator is a checked native
whole-path sethood theorem. The alternatives report also gives a concrete
reason the initial integer cross-model candidate may remain presented. That
finding changes the cross-model successor below.

## Fixed types and the threefold comparison

Use the original [coherence API](../../SquareKit/Internal/Cubical/NativeStructureCoherence.lean)
and its [Cartesian counterpart](../../SquareKit/Internal/Cubical/CartesianNativeStructureCoherence.lean).
Let `Aᵢ = liftedDecode aᵢ`, `sᵢ` be pointed endomorphisms on `Aᵢ`,
`Xᵢ = objectOf description aᵢ sᵢ.fields`, and `O = objects description Γ`.
Write `Path X x y` for `homogeneousPath X x y`, and
`Pᵢⱼ = Path O Xᵢ Xⱼ`. Displayed inhabitants are native `Term`s.
Lawful decoded fillings are retained. Supply native sethood for every target
used by a comparison; giving it for all carriers is a sufficient finite input.

For independent `e : Equivalence s₀ s₁`, `f : Equivalence s₁ s₂`, and
`g : Equivalence s₂ s₃`, retain four complete supplied witnesses:

```text
w12 : HomotopyEquivalence (e.map ≫ f.map)
w23 : HomotopyEquivalence (f.map ≫ g.map)
wL  : HomotopyEquivalence ((e.map ≫ f.map) ≫ g.map)
wR  : HomotopyEquivalence (e.map ≫ (f.map ≫ g.map))
E12 = e.compWith f w12          E23 = f.compWith g w23
EL  = E12.compWith g wL         ER  = e.compWith E23 wR
p = Coded.path e; q = Coded.path f; r = Coded.path g
PL = Coded.path EL; PR = Coded.path ER
A : Term (Path P₀₃ PL PR)
```

`A` is the proposed selected associator, a native **2-path** in `O`. Its carrier
endpoints remain the selected `ua` paths of the actual outer map/witness pairs.
Host associativity aligns the maps; it does not equate their witnesses.
On paper, lift that map homotopy through complete equivalence records, then
through proposition-valued preservation, then apply the selected correspondence.
This first comparison needs target sethood of `A₃`.

Let `μ` denote the existing binary composition comparison, `⋆` whole-path
concatenation, `·` vertical 2-path concatenation, and `▷,◁` whiskering. Fix
parentheses as displayed:

```text
L = μ(E12,g,wL) · (μ(e,f,w12) ▷ r) : Path P₀₃ PL ((p ⋆ q) ⋆ r)
R = μ(e,E23,wR) · (p ◁ μ(f,g,w23)) : Path P₀₃ PR (p ⋆ (q ⋆ r))
α : Path P₀₃ ((p ⋆ q) ⋆ r) (p ⋆ (q ⋆ r))
compatibility : Term (Path (Path P₀₃ PL (p ⋆ (q ⋆ r))) (L · α) (A · R))
```

Compatibility is a native **3-path**. The inner `μ(e,f)` also needs sethood of
`A₂`. Whiskering and `α` need construction; host congruence of functions on
terms is not native whiskering. A direct filler-derived associator is possible
in principle. The bounded route may instead compare carrier transport maps and
recover whole paths, as the use assessment details. Preserve the independently
constructed `A` and the binary-derived route as the actual comparison endpoints.

## Why the higher comparison is expected to be derived

The proposed reusable proof has five steps:

1. Maps into a native set form a native set (`piIsSet`).
2. Complete equivalence witnesses form native proposition fibers. Derive this
   over generic inhabited substitutions from substituted witness contractibility,
   not merely for globally chosen equivalences.
3. Dependent totals over a set with proposition fibers are sets. Apply this to
   complete equivalences, then to structure equivalences using the existing
   `equivalenceFieldsIsProp`.
4. Transfer sethood along the actual selected total homotopy equivalence,
   retaining its inverse and both recovery homotopies. A strict family
   isomorphism is not supplied by the existing correspondence.
5. The resulting `Term (isSet Pᵢⱼ)` makes each fixed-endpoint 2-path family a
   native proposition. Its path constructor compares any two **already
   constructed parallel 2-paths**, producing the desired 3-path.

Steps 2–4 need reusable native lemmas in both models. The exact source anchors
and declaration plan are in the foundations/use reports. This reasoning does
not say all structured objects form a set, or supply a 2-path between arbitrary
different 1-paths. It does not turn native sethood into host proof irrelevance.
No evidence so far requires stronger mathematical hypotheses for this finite
set-target contract. Elaboration failures would still need separate diagnosis.

## Units, triangle, pentagon and substitution

Supply a complete identity witness for each `sᵢ` and construct `Iᵢ` with
reflexive point/step preservation. Write `uᵢ = Coded.path Iᵢ`. Construct
`νᵢ : Path Pᵢᵢ uᵢ (refl Xᵢ)`, path unitors
`λp : Path Pᵢⱼ (refl Xᵢ ⋆ p) p` and
`ρp : Path Pᵢⱼ (p ⋆ refl Xⱼ) p`. Selected unitors retain their supplied
composite witnesses; compare them with `((μ(I,e) · (ν ▷ p)) · λp)` and
`((μ(e,I) · (p ◁ ν)) · ρp)` by 3-paths.

The triangle compares these parallel 2-paths:

```text
α(p,refl X₁,q) · (p ◁ λq),   ρp ▷ q
  : Path P₀₂ ((p ⋆ refl X₁) ⋆ q) (p ⋆ q).
```

For four whole paths `p,q,r,t`, the five vertices and two routes are:

```text
B0 = ((p ⋆ q) ⋆ r) ⋆ t       B1 = (p ⋆ (q ⋆ r)) ⋆ t
B2 = p ⋆ ((q ⋆ r) ⋆ t)       B3 = p ⋆ (q ⋆ (r ⋆ t))
B4 = (p ⋆ q) ⋆ (r ⋆ t)
long  = ((α(p,q,r) ▷ t) · α(p,q ⋆ r,t)) · (p ◁ α(q,r,t))
short = α(p ⋆ q,r,t) · α(p,q,r ⋆ t)
pentagon : Term (Path (Path P₀₄ B0 B3) long short)
```

Both triangle and pentagon are 3-paths, with all parenthesizations fixed. For
four supplied structure equivalences, choose and retain each of the five
complete bracketed composites. A normalization route `N_T` from its selected
path to `B_T` uses binary `μ` and whiskering. Each edge is
`(N_T · edge(B_T,B_U)) · reverse N_U`. Shared vertices retain the same chosen
full witnesses on every incident edge. This gives exact selected pentagon
routes, not an implicit equality between separately supplied records.

For `σ = projection (interval Γ)`, reindex every complete witness. Fresh lawful
preservation fillers are allowed. With endpoint comparisons
`δL : Path P' (path ELσ) (reindexPath PL σ)` and similarly `δR`, compare

```text
Aσ · δR,   δL · reindex₂ A
  : Path P' (path ELσ) (reindexPath PR σ)
```

by a native 3-path. The full map/witness pair is reindexed, satisfying the
existing `path_reindexWith` premise; arbitrary new outer witnesses would need
a native witness comparison instead. Repeat for the binary-derived route.
Comparing independent selections of the resulting 3-cells would require a
4-cell and is outside this first contract.

## Checked integer starting point and rejected loss

The retained [probe](native-coherence-contracts/integer-client.lean.txt) and
[log](native-coherence-contracts/integer-client.log) use actual original and
Cartesian integer admissions. In both models they construct
`move 0 1`, `move 1 2`, `move 3 3`, both bracketed composites with separately
supplied composite-isomorphism witnesses, and the two existing outer binary
comparisons. Both maps send the initial point to 6; decoding gives 6 and the
successor sends it to 7. The probe instantiates the comparison and interval
projection with the actual admissions and rejects a native path from the
transported point back to 0. No new resource setting is used.

An initial probe stopped after three `shift_point` rewrites with an arithmetic
endpoint equality still open. Adding `rfl` closed that definitional equality;
the log retains the exact failure. This was an encoding omission, not a
mathematical obstruction. No associativity/unit/triangle/pentagon cell is
claimed checked by this probe. The successor must check those cells and append
`move 6 4`, obtaining 10 and successor 11 for all five fourfold bracketings.
Translations commute, so this client does not detect order reversal. Full
witness projections and recovery are separate acceptance obligations, not
consequences of the arithmetic test.

## Cross-model decision

The initial candidate was the actual original integer translation's selected
ua decoder line, pulled back along `intervalContextInclusion` into the Cartesian
interval context. Plain restriction has a different base. Admission needs
`SmallPresentation.Data`, actual Cartesian filling and lawfulness, then endpoint
decoder comparisons and a bridge from the older relative complete-equivalence
record to native Cartesian `HomotopyEquivalence`. Existing restriction and
higher-path isomorphisms do not supply an independent-universe comparison.

The alternatives assessment identifies a paper trivialization route: Glue face
values for strict-isomorphism boundary maps are determined by the ambient value
through the inverse. Translation and identity have such inverses. Check the
actual chart/decoder equations before asserting global triviality. A
nonconstant code is not evidence against a constant decoder presentation.
Retain this example as an explicit interoperability and presentation test.

For a genuine varying-family candidate, use the restricted universal decoder

```text
R = Cartesian.restrictFamily
      (Presheaf.SmallUniverse.liftedDecode (𝟙 Presheaf.smallFamilyCodes))
```

on the restricted original universe. On paper, actual unit and Boolean fibers
rule out one constant host: it would be bijective to both a singleton and a
two-element type. The successor must check this control. The exact unresolved
prerequisite is a lawful Cartesian filling of this family, including
variable-source diagonal boxes and uniformity under all target substitutions,
plus its restricted small presentation. Admitting this single family is
substantive; it is not a small corollary of the integer test.

The evidence-producing task returns that construction or its first precise
unresolved typed box/closure obligation with bounded probes. A later classifier
`κ` and decoder isomorphism would then permit a selected-ua comparison contract
retaining full witnesses. This branch does not block within-model coherence.
The alternatives report pins the primary literature and its hypotheses;
prospective universe-equivalence remarks do not discharge our source
cofibration or decoder obligations.

## Ordered successors and architectural limits

- [#700](https://github.com/VladimirMarko/conaled/issues/700): derive native
  whole-path sethood in both models, with complete recovery and checked integer
  and lattice specializations. This is the prerequisite discriminator.
- [#701](https://github.com/VladimirMarko/conaled/issues/701): implement the finite
  associativity, unit, triangle, pentagon and aligned substitution contracts
  above, after #700. Preserve supplied witnesses and direct clients.
- [#702](https://github.com/VladimirMarko/conaled/issues/702): independently test
  the integer Glue-line presentation and the restricted universal decoder's
  admission prerequisites for #688, with explicit success/failure evidence.

These are schedulable successors, not additions to the current execution queue.
The selected correspondence supplies full recovery and a route to truncation;
direct path operations supply reusable diagrams and can eventually address
non-set carriers. Neither presentation replaces the other. Non-set carriers,
dependent structure fields and proof-relevant laws require new arguments where
the proposition-fiber or truncation premises fail. The first contract proves
neither a strict higher category nor unrestricted coherence. Frozen trials,
existing direct interfaces and the completed ordinary #633 result stay intact.
