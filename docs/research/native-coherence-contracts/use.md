# Finite native coherence: implementation and use perspective

Source: `f0cac600a954fae4f340a9262ad732f6fbb30cc7`. This is the initial independent use report for #697. I read the task brief, issue specification, current coherence implementations, integer admissions and clients, relevant recovery, homotopy-level, restriction and classifier APIs, and #687's retained attempt report. I had no prior involvement in #687 or exposure to the other #697 perspective reports. No new Lean probe was executed. “Checked source” below means an inspected declaration at this revision, not a new compilation. All proposed declarations and paper derivations remain to be formalized.

## Recommendation

Implement a finite set-target contract in both native models. Retain `Equivalence.compWith`, complete supplied witnesses, `Coded.path`, and the selected total correspondence. Derive a native 2-path between the two threefold selected composites, and a native 3-path comparing it with the route through existing binary composition comparisons and path associativity. Include units, the triangle, the fourfold pentagon and nonidentity substitution. Prove the truncation and path operations needed for these cells; do not make the final laws fields of another caller-supplied record.

The strongest positive evidence is `EquivalencePaths.ofHomotopy`: it joins complete supplied equivalence records from a map homotopy, without identifying their contraction data by host equality. `equivalencePath` then lifts through proposition-valued preservation, and `explicitMap` produces the selected whole-path comparison. The remaining work for the 3-paths is a reusable truncation argument, plus operations for composing and whiskering native 2-paths with exact endpoints. These are mathematical constructions with missing library packaging, not evidence of an obstruction.

Keep #688 independent. Its selected integer-ua decoder line is a concrete candidate worth testing, but the current restriction APIs do not already give a Cartesian universe code for that line or a comparison with independently selected Cartesian ua. Calling it beyond common-host presentation is premature until its interior decoder and possible presentation have been inspected.

## What callers supply today

The two `NativeStructureCoherence` files define the same structure-level input: a point, an entire endomorphism, a map, its complete `HomotopyEquivalence`, a native point path, and a map homotopy expressing commutation with the endomorphism. `compWith` receives a complete witness for the composite map and returns it unchanged as `.witness`. Its point and function comparisons are composed independently of univalence. The source and target need lawful filling; neither operation assumes carrier sethood.

`Coded.composition` adds target native sethood and compares `path (e.compWith d w …)` with the actual selected concatenation `path e ⋆ path d`. Its carrier is the selected ua of `w`, by `carrier_path`; replacing `w` with a canonical strict isomorphism witness changes the contract. `wholeComparison` applies to every current recursive `Description`, although the independent pointed-endomorphism operation itself is a smaller API.

`path_reindexWith` requires equality of the full dependent pair of map and witness. It deliberately permits new point and endomorphism preservation paths, hence new lawful fillers. That equality is suitable when a supplied witness has literally been reindexed. It is too strong for arbitrary independently supplied witnesses on equal composite maps. The new associator should use `ofHomotopy`, not pass an invented witness equality to `path_reindexWith`.

The selected recovery functions have substantive endpoints:

```text
explicitRightInverseAt p : Path (wholePaths s t) (explicitMap (explicitInverse p)) p
explicitLeftInverseAt q  : Path (nativeEquivalences s t) (explicitInverse (explicitMap q)) q
```

They recover the supplied whole path and complete native equivalence, respectively. The preservation projection alone, decoded integer endpoints alone, or host equality of forward maps does not replace this contract.

## Exact threefold boundary

Write `Path X x y` for `homogeneousPath X x y`; an inhabitant is always a native `Term`. Let codes `a₀,…,a₃` over `Γ : Context.{u+1}` decode to `Aᵢ`. Let `sᵢ : PointedEndomorphism Aᵢ`, and independently supplied `e : Equivalence s₀ s₁`, `d : Equivalence s₁ s₂`, `h : Equivalence s₂ s₃` have maps `f,g,k`. Let `Oᵢ := objectOf description aᵢ sᵢ.fields`, `X := objects description Γ`, and `Pᵢⱼ := Path X Oᵢ Oⱼ`.

Take all of these witnesses as inputs:

```text
W₀₂ : HomotopyEquivalence (f ≫ g)
W₁₃ : HomotopyEquivalence (g ≫ k)
Wᴸ  : HomotopyEquivalence ((f ≫ g) ≫ k)
Wᴿ  : HomotopyEquivalence (f ≫ (g ≫ k))
```

Use the code-decoder fillers for the displayed selected contract. Explicit filler variants may remain internal until the generalized reindexing comparison needs them. Define

```text
ed := e.compWith d W₀₂
dh := d.compWith h W₁₃
L  := ed.compWith h Wᴸ
R  := e.compWith dh Wᴿ
p := Coded.path e; q := Coded.path d; r := Coded.path h
Sᴸ := Coded.path L; Sᴿ := Coded.path R
Nᴸ := (p ⋆ q) ⋆ r; Nᴿ := p ⋆ (q ⋆ r)
```

Every `S` and `N` here is a term of `P₀₃`. In particular, the carrier projections of `Sᴸ` and `Sᴿ` are precisely `ua a₀ a₃ ((f ≫ g) ≫ k) Wᴸ` and `ua a₀ a₃ (f ≫ (g ≫ k)) Wᴿ`. Host `Category.assoc` aligns the forward maps. It does not assert `Wᴸ = Wᴿ`, nor `L = R`.

The first proposed declaration has the exact result

```text
selectedAssociator e d h W₀₂ W₁₃ Wᴸ Wᴿ sA₃ : Term (Path P₀₃ Sᴸ Sᴿ).
```

Construct it by making a reflexive map homotopy after the host associativity conversion, applying `EquivalencePaths.ofHomotopy` to both supplied witnesses, lifting with `equivalencePath description … sA₃`, and mapping through the existing `explicitMap`. Only target sethood `sA₃` is needed for this direct selected-composite comparison.

To state the comparison through the binary cells, also supply `sA₂ : Term (isSet A₂)`. This is used by the inner `Coded.composition e d`; the inner `d,h` comparison uses `sA₃`. It must not be silently inferred by host proof irrelevance. Transporting sethood backward along `h` is mathematically possible, but should be an explicit reusable derivation if used to reduce the public inputs.

Let `c(e,d)` denote the existing binary comparison using the displayed witness. With vertical native 2-path composition `∙`, and whiskering `▷`, `◁`, define

```text
Bᴸ := c(ed,h) ∙ (c(e,d) ▷ r) : Path P₀₃ Sᴸ Nᴸ
Bᴿ := c(e,dh) ∙ (p ◁ c(d,h)) : Path P₀₃ Sᴿ Nᴿ
α(p,q,r) : Path P₀₃ Nᴸ Nᴿ
V := Bᴸ ∙ α(p,q,r) ∙ reverse Bᴿ : Path P₀₃ Sᴸ Sᴿ
```

Fix the parenthesization of `∙` in definitions. The proposed compatibility declaration is a native **3-path**:

```text
Term (Path (Path P₀₃ Sᴸ Sᴿ) (selectedAssociator …) V).
```

The finite contract must retain all four endpoints and all three binary-derived pieces. An assertion that the decoded composite sends `0` to `6` cannot express this boundary.

## Derivation and finite declaration plan

The following names describe proposed responsibilities, not existing declarations.

1. `isEquivIsProp`, proposition-extension sethood, and sethood transport along a native homotopy equivalence. `EquivalencePaths.substitutedWitnessContractible` already contracts any inhabited substituted equivalence-witness family; use a generic inhabitant to derive proposition data. `HomotopyLevels.piIsSet` already makes maps into a set a set. `PropositionExtension.pathEquivalence` already compares paths in a proposition extension with base paths. Together these give sethood of complete equivalences, then of native structured equivalences using `equivalenceFieldsIsProp`. Transfer it along `explicitEquivalence` to obtain `wholePathsIsSet sAⱼ : Term (isSet Pᵢⱼ)`. Establish these in both models. Sethood transfer and the assembled result are not currently provided by `wholeComparison`.
2. Native 2-path concatenation/reversal using the existing lawful path-family fillings. Introduce left and right whiskering as native family maps, with evaluated endpoint theorems. Applying host `congrArg` to a Lean function on terms is not a native whiskering implementation.
3. `selectedAssociator` with the four witness inputs above. Add a helper comparing arbitrary whole paths from a native homotopy of their carrier transport maps. This helper must use complete `pathToEquivalence` records and selected recovery, rather than retaining only maps as the final representation.
4. `concatAssoc`, `concatUnitLeft`, `concatUnitRight` for the whole paths under the stated set-target contract. One route is to compare carrier transport maps: `concatMapHomotopy` reduces transport of either bracketing to the same associative composite, while reflexive transport compares to identity. Reflect through native univalence and `wholeComparison`. This avoids adding a general all-fibrant-types associator before the selected contract can be delivered. The latter remains a useful separate generalization.
5. `selectedAssociator_composition`, unit compatibility, triangle and pentagon. Once `wholePathsIsSet` exists, `pathIsPropAt` makes each fixed-endpoint 2-path family a proposition; `HomotopyLevels.path` supplies the 3-path between the actual constructed routes. Callers supply no triangle or pentagon field.
6. Reindexing of these operations with explicit endpoint alignment. Prove the concrete interval-projection application alongside the generic declarations, using `PathData` if elaboration needs a boundary that retains its source, target and actual path.

Steps 1–2 are the reusable core. Steps 3–6 are the finite successor, including checked integer and lattice applications. A failure to elaborate a specialization within repository limits should first be isolated using arbitrary-family helpers, explicit endpoint equations and retained probes, as #687 did. It is not a reason to weaken the mathematical endpoints or add final-law assumptions.

The recovery route uses native sethood, not a constant-family presentation. The direct path route can construct associators for all lawful fibrant families, and eventually needs explicit higher fillers to supply coherence outside the set-target case. Preserve the existing independent `compWith` clients under their original assumptions whichever route is implemented. No migration of those clients to a new global law record is justified.

## Units, triangle and pentagon

For `sᵢ`, supply a complete `Iᵢ : HomotopyEquivalence (𝟙 Aᵢ)` and construct an identity structure equivalence `idWith sᵢ Iᵢ` using reflexive point and step comparisons. Its selected path `uᵢ` need not be host-equal to `refl Oᵢ`. Construct

```text
ηᵢ : Path Pᵢᵢ uᵢ (refl Oᵢ)
λ(p) : Path Pᵢⱼ ((refl Oᵢ) ⋆ p) p
ρ(p) : Path Pᵢⱼ (p ⋆ (refl Oⱼ)) p.
```

The selected left unitor starts at `path ((idWith sᵢ Iᵢ).compWith e W)` and ends at `p`; its binary route is `c(id,e) ∙ (ηᵢ ▷ p) ∙ λ(p)`. The right route is `c(e,id) ∙ (p ◁ ηⱼ) ∙ ρ(p)`. Retain the arbitrary complete composite witness `W` at each starting endpoint. Compare direct selected unitors to these routes with native 3-paths. Constructing `ηᵢ` by the set-target recovery route requires sethood of `Aᵢ`; expose this when stating selected unit compatibility.

For `p : P₀₁`, `q : P₁₂`, the triangle compares these native 2-paths, both from `(p ⋆ refl O₁) ⋆ q` to `p ⋆ q`:

```text
ρ(p) ▷ q
α(p,refl O₁,q) ∙ (p ◁ λ(q)).
```

Its result is `Term (Path (Path P₀₂ ((p ⋆ refl O₁) ⋆ q) (p ⋆ q)) route₁ route₂)`. Sethood of `P₀₂` supplies that 3-path after both routes exist. For the displayed set-target construction of `ρ(p)`, also provide sethood of `A₁`.

For `p,q,r,t` across five objects, name all five bracketings:

```text
V₀ = ((p ⋆ q) ⋆ r) ⋆ t
V₁ = (p ⋆ (q ⋆ r)) ⋆ t
V₂ = p ⋆ ((q ⋆ r) ⋆ t)
V₃ = p ⋆ (q ⋆ (r ⋆ t))
V₄ = (p ⋆ q) ⋆ (r ⋆ t).
```

The pentagon is a 3-path in `Path P₀₄ V₀ V₃`, between

```text
(α(p,q,r) ▷ t) ∙ α(p,q ⋆ r,t) ∙ (p ◁ α(q,r,t))
α(p ⋆ q,r,t) ∙ α(p,q,r ⋆ t).
```

For this construction the inner associator uses target sethood of `A₃`, and the remaining associators use `A₄`. For four independently supplied structure equivalences also construct a selected composite for each bracketing, keeping a witness at each internal node. Each selected path compares to its displayed `Vᵢ` by three existing binary composition cells and whiskering. Conjugating the five displayed edges by those comparisons produces the pentagon between selected composites; sethood again compares its two routes. If all binary cells are obtained directly from `Coded.composition`, supply sethood of `A₂,A₃,A₄`.

This is a finite coherence contract for paths between set-based structures. It does not claim host equality of 2-paths, a set of all structured objects, unrestricted coherence for non-set carriers, dependent structure descriptions, or proof-relevant law fields. In those cases the proposition-valued preservation step or the 3-path uniqueness argument may fail. Direct path operations can still exist, but this truncation proof does not justify their higher laws.

## Nonidentity substitution

Use `σ := projection (interval Γ)`, as the current public integer client does. Reindex every input witness, including `Wᴸ` and `Wᴿ`; after substitution permit new lawful fillers for the point and function operations. Let `L′,R′` denote the fresh composites, and let

```text
jL : Path P′₀₃ (path L′) (reindexPath Sᴸ σ)
jR : Path P′₀₃ (path R′) (reindexPath Sᴿ σ).
```

These are obtained by the `path_reindexWith` pattern because the full outer map/witness pair is the reindexed pair, irrespective of fresh preservation fillers. Build reindexing on 2-paths through the corresponding path-family isomorphisms and endpoint conversions. The required 3-path compares, in `Path P′₀₃ (path L′) (path R′)`,

```text
selectedAssociator of the fresh data
jL ∙ reindex₂ (selectedAssociator of the original data) ∙ reverse jR.
```

Sethood of the target after substitution is available from `reindexSet`. The comparison must not assert strict naturality of chosen fillers. Repeat the aligned comparison for the route built from `Bᴸ`, `α`, and `Bᴿ`; with these endpoints, any desired compatibility between their 3-paths lies one dimension higher and is outside the first contract. A nonempty base specialization makes the projection genuinely nonidentity; `CartesianPaths.interval_projection_not_injective` is an existing concrete check.

## Integer acceptance evidence

Use the actual `Examples.NativeLatticeTransport.{Presheaf,Cartesian}.admission ℤ`. Each calls `LargeConstructors.construct` with small presentation and lawful discrete filling; this is more than an abstract assumed universe code. The existing coherence examples use `admitted.decoding` to construct `point`, `shift`, `system`, and `move`. The Cartesian `HomotopyEquivalence.ofIso` also takes the target filling and its lawfulness.

The new threefold client is exactly

```text
e := move admitted 0 1 : system 0 ≃ system 1
d := move admitted 1 2 : system 1 ≃ system 3
h := move admitted 3 3 : system 3 ≃ system 6.
```

Supply `W₀₂,W₁₃,Wᴸ,Wᴿ` explicitly, for example from the correspondingly bracketed composites of the three translation isomorphisms. Also exercise witness composition using the existing `.comp`; these need not be host-equal witnesses. The generic theorem must quantify over all four inputs even though this discrete test can identify more data. All intermediate systems have successor as their endomorphism. Decode both final composite maps at arbitrary integer `n` to `n+6`, the final point to `6`, and the next successor point to `7`. For the fourfold test append `move admitted 6 4`, obtaining `0 → 1 → 3 → 6 → 10` and successor point `11` for all five bracketings.

Concrete acceptance tests in each model:

- Typecheck `selectedAssociator`, both `B` routes, `α`, and the 3-path with explicit endpoints. Check each selected carrier projection names the supplied outer witness.
- Typecheck the units, triangle, pentagon, all five fourfold selected composites and their binary-derived comparisons.
- Instantiate admission rather than leaving an `admitted` parameter in the final public examples. Keep a generic parameterized helper to avoid excessive specialization cost.
- Exercise `σ` with separately supplied lawful original and substituted fillers. Retain both whole paths and the 3-path, not just decoded arithmetic.
- Reject a path from the transported initial point `6` back to `0`, following `rejects_unchanged`; repeat `10 ≠ 0` for fourfold composition. This catches loss of the actual map endpoint, although commuting integer translations do not detect permutation order. Add an explicitly ordered noncommuting automorphism example only if order sensitivity becomes a claim of this successor.
- Exercise `explicitRightInverseAt` on each selected path and a concatenated path; exercise `explicitLeftInverseAt` on the complete native equivalences. Preserve the existing lattice `wholeComparison` use and all direct composition/inversion clients.

## Separate #688 candidate and missing prerequisite

Fix an original admitted integer translation `move 0 1` over a concrete inhabited base and let

```text
pDM := Presheaf.SmallUniverse.NativeUnivalence.ua a a f E
B := Presheaf.SmallUniverse.liftedDecode (codeOfPath pDM)
R := Cartesian.relativeFamily B.
```

`B` is a family over the original interval context; `R` is a family over `total (Cartesian.interval (restrict Γ))`. This relative pullback matters: plain restriction leaves the larger restricted De Morgan interval as base. `intervalInclusion` is explicitly not an interval isomorphism. `pathIso`, `homogeneousIso`, `twoPathIso`, and `threePathIso` preserve paths relative to a fixed restricted source family. None identifies the original universe with the independently constructed Cartesian universe.

To classify `R` using `Cartesian.SmallUniverse.LargeConstructors.construct`, the exact inputs are `SmallPresentation.Data R`, `Filling R`, and `Filling.Lawful`; the output includes a code and a decoder isomorphism. Restricting the source small fiber presentation is a candidate for the first input. A lawful Cartesian filling of this particular relative decoder, with its endpoint and transport comparisons, is the evidence-producing missing construction. There is no inspected theorem that globally transports arbitrary source fillings through restriction. Nor does `CartesianWitnesses.restrictEquivalence` immediately return native Cartesian `HomotopyEquivalence`: it returns the earlier `Cartesian.Equivalence` record with explicit contraction evaluations. Its inverse and entire contractions are retained and injectively recoverable, but conversion to the native record and decoder conjugation still need to be checked.

The bounded prerequisite should construct these inputs for this one `R`, classify it, align both endpoint decoders with the independently admitted Cartesian integer carrier, and compare its complete transport witness with the Cartesian witness used by independently selected ua. Retain the selected inverse, both endpoint homotopies and contraction data through the comparison. Then use native univalence to state the resulting whole-line comparison. Success requires naturality and endpoint comparisons on all generalized cubes, not only endpoint evaluation or matching `+1` on integers.

This candidate may or may not leave the common-host presentation boundary. Its endpoint carriers are explicitly presented by `ℤ`; that alone does not present the entire Glue decoder line. Conversely, a nonconstant code alone does not prove that its decoder lacks a constant presentation. Inspect `NativeUnivalenceCharts.uaValue` and the actual Glue decoder, and attempt a natural isomorphism `R ≅ constantFamily _ (ULift ℤ)` retaining its boundary identifications. If that succeeds and the comparison factors entirely through it, record the candidate as another presented case. If the comparison can be built from restriction, filling and native witness recovery without such a presentation, record exactly that broader contract. If either construction fails, preserve the precise unsolved judgment and bounded probe; do not claim a mathematical separation from a timeout.

`CartesianClassifierComparison` already gives finite tuple families a constant presentation and uses discrete complete-record presentations in its selected comparisons. Those results do not discharge the new integer Glue-line obligation. The smallest useful #688 follow-up is this classifier-and-filling prerequisite, with the presentation test as its discriminator. Within-model associativity can proceed without it.
