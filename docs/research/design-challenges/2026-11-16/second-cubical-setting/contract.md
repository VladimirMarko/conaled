# Contract and foundations assessment of #574

Retain the restriction construction as a bounded interpretation candidate. Its relative path comparison supports genuine target contractible-fiber witnesses, rather than merely carrying source records as opaque values. The strongest reason is the shape of the actual local definitions: `HomotopyContractible` is a center and a contraction section over the total family, and `HomotopyEquivalence` asks for precisely this structure on the generic Sigma/path fiber. Arbitrary dependent-product preservation is unnecessary for that argument.

This is a paper-level derivation with inspected local definitions. It is not a constructed Lean realization or completion of #574. The dependent package comparison and the promised chosen-filler contract need a more explicit scope before implementation.

## Sources and independence

I inspected local HEAD `fae1621cae2d44c788f65400392820d942dabccd`, verified by `git rev-parse HEAD`, and read #574 and its #554 comment through GitHub. The shared brief is an uncommitted input. I read neither other reviewers' reports nor the research assistant's note, and had no prior involvement in this proposal. This assessment uses the assigned contract lens; no independent model diversity is claimed. No Lean build or formal experiment was run, and no repository file was modified.

Local evidence below names declarations at that pinned revision. External sources were opened directly: [CCHM v1, §§8.1–8.3](https://arxiv.org/html/1611.02108v1), [Angiuli–Hou–Harper, CSL 2018](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2018.6), and [Syntax and Models of Cartesian Cubical Type Theory](https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf). The manuscript URL is mutable; this report does not assign it a publication version or content hash. External claims here are limited to the indicated sections, not a claim that any paper supplies this repository's comparison.

## Relative paths: an explicit construction

Use finite coordinate sets as cubes, with products given by disjoint union of coordinates. In C a map m→n is an n-tuple of constants and variables from m. In D it is an n-tuple of De Morgan expressions modulo the local congruence. Inclusion sends constants and variables to the corresponding expressions. The needed structural hypotheses are:

- The inclusion is identity on objects and respects composition, endpoints, projections, and the chosen product presentations n+1 and n+2.
- Both presheaf categories use the usual represented interval and the same universe-size discipline.
- Families are presheaves over categories of elements, with sections and total spaces as in the current source.

These assumptions can be proved from the proposed definitions; they should not become unexplained builder obligations. `Dimensions.lean` defines the quotient homs and substitution; `Presheaf.lean` defines families, sections, total spaces, projections and generic elements. CCHM §8.1 defines its cube maps using free De Morgan algebras; §8.2 gives families as presheaves over categories of elements and the ordinary presheaf dependent constructors. That supports comparison with the local mathematical presentation, not a checked identification of implementations.

Let I_D=y_D(1), I_C=y_C(1), and α:I_C→R(I_D) be inclusion of coordinate expressions. For B over Γ×I_D, its target dependent-path coefficient is

    B_C = (id_(RΓ) × α)^*(R B),

not just R B over an unchanged interval context. This pullback is essential to a correctly typed claim.

At x∈Γ(n), let π:n+1→n and v:n+1→1 denote projection and the last variable. A source path element is determined by its generic value

    b ∈ B(n+1, (Γ(π)x, v)).

Its value at any D-map f:m→n and interval expression r:m→1 is obtained by restricting b along ⟨f,r⟩:m→n+1. Conversely this formula constructs the section from b. For the target, use the same b and the same formula for Cartesian f and r. Naturality in a Cartesian map g is exactly substitution along g×id_1. Endpoint constraints on the source and target both reduce to the restrictions of b along ⟨id_n,0⟩ and ⟨id_n,1⟩. Thus the relative-path comparison is an isomorphism, natural in x, substitutions, and coefficient maps.

This is the dependent version of the Yoneda/product calculation in the brief. It applies to all families B of this form, without fibrancy. `Paths.lean` defines paths as `PiElement` sections with endpoint equations, so proving generic evaluation and reconstruction for that actual representation is the central Lean obligation. The paper argument does not permit substituting an arbitrary dependent-product isomorphism.

## Genuine fibers and exact selected data

`HomotopyEquivalences.lean:116` defines the center and contraction. Its `homotopyFiber` at line 161 is a Sigma whose second component is a homogeneous path, and its equivalence record at line 298 is contractibility of the generic-target fiber.

Restriction preserves the sets and maps of comprehension and Sigma pointwise. Combine this with the path isomorphism to identify the restriction of the source generic fiber with the target generic fiber. Map the center through this isomorphism. Map the contraction through the relative-path comparison and the fiber isomorphism, with its total-space presentation. Its endpoints become that center and the target generic element. This supplies the target record with its intended meaning: the contraction covers every generalized target fiber element, because the fiber comparison is an isomorphism. No target filler or target Pi classifier is involved.

The `selectedInverse`, `selectedRight`, and `selectedLeft` definitions in `SelectedInverse.lean:16–43` project that exact center or its contraction at `(a,refl)`. Their preservation follows from Sigma projections, path reflexivity/application, substitution and generic-element laws. Those laws should be derived and tested before adding selected-inverse preservation fields.

The separately constructed `selectedInverseEquivalence` at line 136 uses lawful source fillers. Mapping its already constructed record gives a target equivalence for the mapped selected inverse. It does not establish equality with an inverse-equivalence algorithm rerun using arbitrary Cartesian fillers. The same distinction applies to the selected composite equivalence and chosen universe comparisons. Source `selectedComparison` also uses reversal; mapping its output is valid, while its target reconstruction needs a separately provided operation on the appropriate image paths.

Restriction on sections is injective because it keeps components at every cube and every context element. The path comparison is componentwise invertible. Therefore centers and contractions remain distinguishable, and equality of translated full selected records reflects equality of the source data, up to stated presentation isomorphisms. This uses neither a general Pi comparison's injectivity nor reflection of arbitrary target structure.

## Square bodies and the interval obstruction

`NativeUniverseSquares.comparisonSquare` evaluates two interval coordinates after the explicit inner reindexing. `comparisonSquare_injective` proves retention of the whole two-path for fixed endpoints. Iterating the relative-path construction yields a target two-path with the same generic n+2 cube. Its evaluated body is the pullback of the restricted source square along the two α maps. It is not literally a section over the same domain: source restriction has domain RΓ×R(I_D)×R(I_D), while target evaluation has domain RΓ×I_C×I_C.

This smaller evaluation domain does not erase a natural source square. Evaluate at dimension n+2 with base Γ(π)x and the two last variables. All source values at arbitrary De Morgan r,s are recovered by source naturality along ⟨id_n,r,s⟩. Prove this recovery, or derive it from the iterated path isomorphism and existing injectivity, instead of asserting that any pullback of sections is faithful.

The proposed obstruction is valid. An endpoint-preserving natural q:R(I_D)→I_C would send the source reversal cube ¬v in dimension one to an element of I_C(1), whose only options are 0,1,v. Naturality at the two endpoint maps requires faces (1,0), which none has. `Dimensions.reversal` supplies the source cube. This rules out that interval map, including a representation of source reversal as target dimension syntax. It does not rule out the path comparison: that comparison exploits representability and source restriction along mixed tuples, and uses α in the opposite direction.

A useful separating test is X=I_D: the target path represented by the source reversal remains a path in R(I_D). It does not become a reversing dimension term in I_C. This prevents conflating the two interval objects.

## The dependent package is the remaining interface pressure

`Examples/CubicalStatePackageFamily.lean` builds its five-field package with Sigma and Pi: `endomorphisms`, `predicates`, and `preserves` are Pi families. Its `filledPackage` is an already chosen section derived through the source package filler; `readOut` evaluates the functions at identity arrows and retains both dependent proof fields.

Restricting that exact package family and its filled section retains all their component data. However, this alone does not identify R(package_D A) with package_C(R A) rebuilt using target Pi. The generic-fiber argument avoids general Pi, while this package-constructor claim would need a separate comparison. The canonical restriction-of-Pi map may suffice in the forward direction, together with application laws and the specific discrete proof-family comparison. Its invertibility is not established by the path argument. State explicitly whether the frozen package is the restricted source package or a target-constructed package receiving a comparison map. Do not quietly replace one by the other.

For the bounded deliverable, retain the exact restricted package and selected section, expose target readouts through the actual source component functions, and derive the forward package comparison if target constructor usability is required. Freeze one concrete `filledPackage A e s` specialization and its base change through α, not merely its theorem name. Preserve the Boolean separation and `CubicalFiniteStateIdentity.wrong_transition`/`wrong_rejected` controls. Those test observations and order; neither substitutes for the fiber and square tests above.

## Recommendation on interface size and acceptance

Direct route laws are the best first proof target: define C, inclusion, family restriction, comprehension/Sigma comparisons, and the relative-path isomorphism with generic evaluation. Prove their naturality, endpoint, application and composition laws. Derive fiber, full-witness, selected-map/homotopy, and square preservation from those facts. A small reusable interface can then expose those proved operations and coherence laws. It should not ask builders for the final univalence or selected-witness theorem that the task is meant to derive.

A broader model morphism requiring all Pi, Kan filling, universe classification and recomputation would impose obligations not needed for these retained records. It remains a separate possible design if target-native arbitrary programs become a requirement. The Cartesian model manuscript uses diagonal cofibrations and a different Kan operation (Introduction §1.3, model §3); §3.4's comparison requires a setting where the relevant cofibrations and composition structures coexist. Its existence result supplies no such structures on this restricted universe automatically. CSL 2018 also distinguishes fibrant and non-fibrant fragments and validates univalence in its fibrant fragment.

The smallest correction to the brief is to make α and every dependent base pullback explicit, state the package constructor boundary, and label selected sections separately from filler operations. Then the first discriminating implementation test is a relative dependent path with a nonconstant coefficient family, followed by a generic-fiber witness and an n+2 square-body recovery theorem. Add preservation under two composed context substitutions. These are meaningful construction tests; endpoint-only equality is insufficient.

Unresolved work belongs to #574's bounded realization: concrete target definitions, checked comparisons and consumers, formal statement review, full applicable build/audit, and acceptance review. General Cartesian filling and a target univalent universe remain unsupported here. Their absence does not invalidate the bounded witness construction, but it prevents reporting a full second univalent model or preservation of arbitrary target recomputation.
