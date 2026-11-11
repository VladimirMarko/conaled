# Local universes and a weak groupoid unit

Research for [#427](https://github.com/VladimirMarko/conaled/issues/427), under
#289 and #235. Inspected starting revision:
`3bbf8083f94629fdedc1a438112f78d6d97a3196`, 2026-11-09.

**Local universes resolve a genuine filler-choice problem in this example,
but a constructor-specific formula also resolves it.** The weak unit is the
contractible two-object groupoid. Its dependent eliminators can differ on
arrows even when they agree on objects and on the constructor. Selecting an
eliminator once over the object of all motive/branch parameters makes it
strictly stable under substitution. Alternatively, fixing lifts in each local
motive presentation gives a direct formula with the same stability. Unit is
simple enough that this direct formula requires less constructor-specific
setup. This is not evidence against local universes for other constructors.

The [finite-family comparison](local-universes-concrete-comparison.md) remains
the baseline. Here the motives have genuine automorphisms; the choice problem
is not merely nested set-pullback coordinates. All general derivations below
are paper mathematics. No new Lean model, general coherence framework, or
cubical provider is implemented.

Implementation update: [#448’s formalization](weak-groupoid-unit-formalization.md)
now proves the bounded direct and parameter constructions in Lean. The report
below preserves the original paper argument and its original validation record.

## Model, sources and exact hypotheses

Use classical set mathematics with a Grothendieck universe U, and a larger
universe containing U for the category of U-small groupoids. Contexts are
U-small groupoids, substitutions are **all functors**, and types over Γ are
isofibrations `p:E→Γ`. An isofibration lifts every arrow out of p(e) to an
arrow out of e, with the prescribed image. Terms are sections. Type morphisms
are **all commuting squares**, not only squares preserving a chosen cleavage.
Comprehension is the inclusion in the arrow category, hence fully faithful.
Chosen ordinary pullbacks supply cartesian lifts: the underlying pullback
universal property is on the full sets of functors, and pullbacks of
isofibrations are isofibrations. No splitness of those pullback choices is
assumed.

The pinned primary source is Lumsdaine–Warren,
[arXiv:1411.1736v2](https://arxiv.org/abs/1411.1736v2), revised 6 April 2015.
Definition 3.1.3's LF asks for finite products and dependent exponentials
for `Z →g Y →f X` when f is display and g is display or a product projection.
Example 4.2.5(1) identifies the canonical groupoid model structure as logical;
its fibrations are exponentiable. Thus pullback along an isofibration has a
right adjoint on the **whole slice categories**, which supplies the requested
exponentials. This is a cited mathematical theorem, not a Lean result in this
repository or a field silently assumed in a new model record.
[Source §§3.1 and 4.2](https://arxiv.org/html/1411.1736v2)

Terminal objects and finite products of groupoids are componentwise. Product
projections are isofibrations, by lifting with an identity in the other factor.
The right adjoints used for LF stay among U-small groupoids: their section and
natural-transformation data are indexed by U-small object/arrow sets. The
universe closure supplies those products and function sets. The category of
all these structures is at the larger level; there is no U-small classifier
for all of them and no internal univalent universe. We do not restrict to
finitely generated contexts or assert that such a restriction retains LF.

For the particular unit construction below, less than full LF is used:
finite products, pullbacks, and the functor groupoid `[I,V]`. Evaluation and
currying give `Fun(Γ×I,V) ≅ Fun(Γ,[I,V])`, including naturality in **every**
functor into Γ. Functor groupoids are groupoids because every component of a
natural transformation is invertible. Their objects and arrows are U-small.
These explicit objects avoid any unproved specialization of LF in the
parameter calculation. The full LF source result documents that the ambient
model also meets the general theorem's hypotheses.

The model's equality for strict stability and β is equality of functors,
meaning equality of object and arrow maps. An isomorphism between functors is
a different comparison. In a Lean formalization these equalities may require
extensionality and transport; this report does not promise definitional
reduction for every equation.

Classical choice, or supplied lifting data, selects lifts. For one fixed
isofibration only its set of lifting problems is involved. Selecting data for
all U-small presentations can be performed in the larger metatheory. This is
an explicit metatheoretic assumption, not constructive extraction of a lift
from mere existence. The finite control below supplies its choices explicitly.

## The constructor and arbitrary dependent elimination

Let I have objects 0 and 1 and exactly one arrow between every ordered pair.
Write `aᵢ:0→i`; `a₀=id`. The projection `Γ×I→Γ` is an isofibration and the
constructor is `i₀:Γ→Γ×I`, `γ↦(γ,0)`. The inclusion i₀ is an equivalence
injective on objects, but is not an isomorphism of groupoids.

The unit contract asks that for **every** isofibration `q:D→Γ×I` and functor
`d:Γ→D` with `q d=i₀`, there is a functor `j:Γ×I→D` satisfying

```text
q j = id_(Γ×I),        j i₀ = d.
```

The equations include arrow maps. There is no uniqueness or strict unit-η
requirement. This is the weak-unit dependent eliminator/β contract of
Lumsdaine–Warren §3.4.4, with the computation square written as a section.
Its weak stability quantifies over new motives and branches after each base
change; it does not require preserving a previously chosen eliminator.
[Unit definitions and lifting lemma](https://arxiv.org/html/1411.1736v2#S3.SS4.SSS4)

Here is a direct existence proof. For each object γ and i choose an arrow

```text
ℓγ,i : dγ → zγ,i,       q(ℓγ,i) = (idγ,aᵢ),       ℓγ,0 = id_(dγ).
```

Isofibration gives the i=1 lifts; choose the identity for i=0. Define j on
objects by `j(γ,i)=zγ,i`. For an arrow `(u,b):(γ,i)→(γ',i')`, define

```text
j(u,b) = ℓγ',i' ∘ d(u) ∘ ℓγ,i⁻¹.
```

Its image under q is `(u,aᵢ' ∘ aᵢ⁻¹)=(u,b)`. Identity preservation follows
by cancellation. For two composable arrows, the two adjacent middle lifts
cancel, leaving the formula for the composite because d is a functor.
At i=i'=0 the formula is d(u), proving β on both objects and arrows.
Nothing requires q or d to descend from previously selected data.

After any `σ:Δ→Γ`, the pullback of the unit/constructor is canonically
identified with `Δ×I` and its 0-inclusion. Repeating the same proof for **any
new** `q':D'→Δ×I` and `d':Δ→D'` establishes weak stability. A telescope of
finitely many isofibrations can also be treated by its composite isofibration
when a branch supplies a section of the whole telescope. This observation
uses closure under composition; it is not a proof of Frobenius Id elimination.
No Id, modal operation, or mixed constructor law is part of this unit contract.

## Two choices, and two rejected stronger claims

Take Γ terminal and the constant motive `q:I×B(C₂)→I`, with the only object
of `B(C₂)` as branch at 0. Write C₂ additively as `{0,1}`. A section functor
extending that branch is determined by `k∈C₂`, its label on `0→1`:

```text
jₖ(i)=*,       jₖ(i→i') = lᵢ'−lᵢ,       (l₀,l₁)=(0,k).
```

Both k=0 and k=1 satisfy β and functoriality. Their arrow maps differ. Thus
object-only observations or the existence of a filler do not identify a
selected filler. The two sections are naturally isomorphic relative to 0;
that does not make them equal functors.

This supplies an actual possible failure of chosen substitution stability.
Choose k=0 over terminal Γ. Over the discrete two-object Δ choose k=1 on both
components of its pulled-back motive. Both choices are valid eliminators, but
restriction along `Δ→Γ` does not carry the first chosen eliminator to the
second. Flattening raw pullback coordinates does not repair this arrow-label
mismatch. This is failure of **unconstrained choices**, not a proof that no
stable choices exist or a separation of weak stability from pseudo-stability.

There is also no selection equivariant under every automorphism of this
motive that fixes its branch. The automorphism sends an arrow label g from i
to i' to `hᵢ'+g−hᵢ`, with `(h₀,h₁)=(0,1)`. It fixes the entire fiber at 0
and interchanges j₀ and j₁, so neither filler is fixed. Naturality under all
motive automorphisms is stronger than base-substitution stability and is not
promised by local universes. A chosen universe presentation may be held fixed
under substitution without being invariant under its every automorphism.

A second rejection tests an attractive shortcut in the direct method. A
normalized cleavage may choose label 1 for the lift of `0→1`, label 0 for
`1→0`, and 0 for identities. Every chosen arrow is a valid lift. Using those
lifts directly as a functor would send the composite `0→1→0` to 1 rather
than identity 0. The conjugation formula above repairs this: once l₁=1 is
chosen, it sends **both** nonidentity arrows to label 1. Normalized lifts need
not compose; the derived section does. A split cleavage would be extra data.

## Local-universes construction, including fresh motives

A local type over Γ is `(V,p:E→V,n:Γ→V)` with p an isofibration; reindexing
only precomposes n. Use the constant code `(1,I→1,!)` for unit and write its
comprehension explicitly as `Γ×I`. Local morphisms remain all squares between
the decoded displays. Every raw type p over Γ has the presentation `(Γ,p,id)`
with the usual decoded pullback comparison. This does not equate different
presentations of the same type.

Now fix a **motive presentation** `p:E→V`. A motive over Γ×I is a naming
functor `c:Γ×I→V`, and its branch is `d:Γ→E` with `p d=c i₀`. Terms are
written as these fiber-component functors, equivalent to sections of the
chosen pullback display. The object of all such motive/branch parameters is

```text
P = [I,V] ×_(ev₀,V,p) E.
```

An object of P is `(c₀,e)` with `p(e)=c₀(0)`. An arrow is a pair `(η,h)`
where `η:c₀⇒c₁` and `h:e→e'` satisfy `p(h)=η₀`. These are strict equalities
in a pullback of groupoids, not an isocomma construction. The semantic contract
here supplies strict functors and equations; no weaker comparison has been
silently replaced by equality.

Evaluation gives `ev:P×I→V`: on objects `(c₀,e,i)↦c₀(i)` and on arrows
`((η,h),b:i→i')↦c₁(b)∘ηᵢ`. The generic motive is the pullback of p along ev,
an isofibration. Its branch sends `(c₀,e)` to e and `(η,h)` to h. Apply the
weak-unit result just proved to obtain one generic functor

```text
Jp:P×I→E,        p Jp=ev,        Jp(-,0)=projection_E.
```

Choose it once for this fixed p, independently of Γ. Currying c and pairing
with d gives the representing functor

```text
N(c,d):Γ→P,       γ↦(c(γ,-),dγ).
j!(c,d) = Jp ∘ (N(c,d)×id_I).
```

On an arrow u, the first component of N is the natural transformation with
components `c(u,idᵢ)`, and the second is d(u). Its pullback equation follows
from the branch equation on arrows. Evaluation and uncurry recover c, and
projection recovers d; conversely these determine N. These inverse equations
hold for **all** functors, not only objects or identity arrows.

For `σ:Δ→Γ`, put `cσ=c∘(σ×id_I)` and `dσ=d∘σ`. Currying gives
`N(cσ,dσ)=N(c,d)∘σ` on objects and arrows. Hence

```text
j!(cσ,dσ) = j!(c,d)∘(σ×id_I).
j!((cσ)τ,(dσ)τ) = j!(c,d)∘((σ∘τ)×id_I).
```

The same Jp supplies both sides; no eliminator is chosen again at Δ or Θ.
β follows by restricting to 0. The result lies over the actual substituted
motive because `p j!=c`. Unit formation and its constructor are constant in
the base, so they are strictly stable as well in the displayed split
presentation. Repeated substitutions compare complete section functors,
including their arrow labels.

For an arbitrary fresh local motive `(V',p':E'→V',c')` and branch d' at Δ,
use its own parameter object P' and already selected generic Jp'. No factorization
through old c or d is required. This quantifier is essential. Fixing one p
while proving its parameter theorem does not restrict subsequent users to
pullbacks of a single old motive.

## Direct stable comparator and its shared setup

There is a direct formula on the **same local presentations**, avoiding P.
For each fixed `p:E→V`, choose a normalized cleavage L: for every e and arrow
`v:p(e)→v'`, select a lift `L(e,v):e→e'`, with `L(e,id)=id`. Do not require
L to preserve composition. Given c and d as above, set

```text
ℓγ,i = L(dγ,c(idγ,aᵢ)).
jL(γ,i) = target(ℓγ,i).
jL(u,b) = ℓγ',i' ∘ d(u) ∘ ℓγ,i⁻¹.
```

The earlier conjugation proof establishes the section and β equations for
**every** such motive and branch. Reindexing replaces γ,u by σγ,σu, leaving
p and L fixed. The formulas for `jL(cσ,dσ)` and `jL(c,d)∘(σ×id)` therefore
agree on objects and arrows. Repeating with τ evaluates at σ(τθ) and σ(τv).
This derives strict stability without assuming a stable family of final
eliminators. It uses a normalized cleavage, which is strictly less input than
a split cleavage; the second rejection above explains why the formula matters.

The comparison can be exact, not just existential. Choose the generic Jp by
applying this same formula to the evaluation motive and generic branch. Then
substituting N into its object and arrow formulas gives `j!=jL`. For arbitrary
independently selected Jp, no such equality is asserted: the C₂ example
refutes it. There is a vertical natural isomorphism between any two section
extensions relative to the branch. Indeed, for extensions j and j', set
`α(γ,i)=j'(idγ,aᵢ)∘j(idγ,aᵢ)⁻¹`; naturality follows by writing every arrow
through its two 0-endpoints, and α is identity at 0. A specification observing
the selected functor still distinguishes them unless it explicitly admits
this isomorphism as its comparison.

The direct formula is not a competing strictification of the *entire*
comprehension category without local names. Both routes here share delayed
substitution. In raw arbitrary q over Γ×I, independently reselecting a cleavage
after pullback repeats the original problem. In a pre-existing split model
of functor-valued families, transport in the motive instead gives a direct
unit eliminator; that simpler input already includes coherent transport.
This report does not identify that restricted family presentation's arrows
with all commuting squares of isofibrations. The
[existing comprehension-boundary assessment](concrete-dependent-coherence.md)
explains why such an identification would need another proof.

| Obligation | Generic local-universes recipe | Direct formula on local presentations |
|---|---|---|
| Shared split presentation | Keep p fixed and substitute its name | The same requirement; not eliminated by the formula |
| Constructor-specific setup | `[I,V]`, pullback P, evaluation motive, generic branch and one generic filler | One normalized cleavage of p and conjugation formula |
| Choice | Generic filler for each p | Lifts for each p; no composition law required of those lifts |
| Arbitrary fresh motives/branches | Represent by N for their own p | Apply formula for their own p |
| Strict laws | Naturality of currying and fixed Jp | Equality of formulas after precomposition |
| Exact comparison | Holds when generic filler is built from L | Holds for the same chosen L; not for unrelated choices |
| Wider constructors | Source coherence theorem supplies a reusable recipe under its hypotheses | Another constructor needs its own formula and proof |

This compares proof obligations, not measured author productivity. For unit,
the direct formula is shorter. The generic route isolates the noncanonical
choice without requiring discovery of that formula. Neither makes selected
fillers unique, adds a univalent universe, or supplies an interpretation of the
retained cubical monodromy argument.

## Bounded implementation specification and disposition

A future implementation can formalize this constructor without building a
full homotopical model. Reuse Mathlib groupoids, functors, natural isomorphisms,
products and pullbacks where available. Keep raw lifting data separate from
its derived laws; do not put the desired stability theorem into a model field.
The bounded theorem specification is:

1. Define I and a normalized arrow-lifting datum for an arbitrary functor p
   between groupoids. Prove an isofibration supplies such data under stated
   choice, or take the actual lift datum as an input without claiming its
   construction.
2. For arbitrary Γ, c, d and their exact branch equation, construct jL. Prove
   its functor laws, `p jL=c`, β, and reindexing along arbitrary σ and τ on
   object **and arrow** maps. Lift targets remain selected data.
3. Construct `[I,V]`, P, evaluation and N. Prove both representation inverses
   and naturality on all functors. Construct Jp from the same L and prove
   `j!=jL`. A separate generic-filler input may be used to prove the generic
   stability theorem, but must not be advertised as constructing that filler.
4. Retain the C₂ two-filler distinction, the swapping motive automorphism and
   the nonsplit-cleavage rejection. Connect positive β/composition and double
   reindexing cases to the public universal theorems. Do not erase arrow maps
   to make the negative cases disappear.

These are proposed Lean obligations, not completed Lean claims. The existing
[Type-family implementation](../../SquareKit/LocalUniverses.lean) supplies a
useful naming/substitution baseline but not these groupoid constructions or LF.
Its dependent Σ/currying work is not repeated or reported as missing.

Recommendation to #289/#235: keep local universes as an optional model-builder
route. This experiment now supplies the missing nonunique-filler comparison,
while favoring the direct formula for this constructor if it is implemented.
A general framework is not justified by this one unit case. A later experiment
could test an eliminator whose fillers lack such a short formula, but should
specify its own models, motives and observations first. That is a research
recommendation, not a new scheduled project or an assertion that the harder
construction exists.

#419/#420 retain the cubical family-classifier/Glue work. #426's TwoFamily
comparison is independent. No mixed modal/higher law is needed or proved
here; adding such constructors would require their own joint weak-stability
and interaction arguments. #427 creates no project-wide foundation decision,
changes no existing constructor interface, and supplies no #108 retest theorem.

## Reproduction and evidence boundary

The source archive was acquired in the pinned development shell:

```sh
direnv exec . curl -L --fail https://arxiv.org/src/1411.1736v2 -o /tmp/lw-v2.tar
sha256sum /tmp/lw-v2.tar
```

SHA-256: `545175cf105359f0fc24201570fa892de7894ab16ecd7a6b520b98e94d03f9a0`.
The TeX source checks the LF definition, full-slice exponentiability statement,
unit rule and groupoid example without relying on noisy HTML diagrams. Its
arXiv version identity, rather than the HTML renderer's later title date, pins
the citation. The source theorem establishes the ambient LF fact; the explicit
weak-unit, parameter and direct-comparison derivations above are this report's
paper arguments. There is no new kernel-checked result or performance claim.

The following finite calculation was run with `direnv exec . python`; it
checks the rejecting examples and a finite substitution control. It does not
prove the arbitrary-groupoid or arbitrary-motive theorems.

```python
from itertools import product
sections = []
for k in (0, 1):
    lift = (0, k)
    arrow = {(i, j): (lift[j] - lift[i]) % 2
             for i, j in product((0, 1), repeat=2)}
    assert all(arrow[i, i] == 0 for i in (0, 1))
    assert all((arrow[j, h] + arrow[i, j]) % 2 == arrow[i, h]
               for i, j, h in product((0, 1), repeat=3))
    sections.append(arrow)
assert sections[0] != sections[1]
h = (0, 1)
transform = lambda a: {(i, j): (h[j] + a[i, j] - h[i]) % 2 for i, j in a}
assert transform(sections[0]) == sections[1]
assert transform(sections[1]) == sections[0]
naive = {(0, 0): 0, (1, 1): 0, (0, 1): 1, (1, 0): 0}
assert (naive[1, 0] + naive[0, 1]) % 2 != naive[0, 0]
for names in product((0, 1), repeat=2):
    for sigma in product(range(2), repeat=3):
        for tau in product(range(3), repeat=2):
            sequential = tuple(tuple(names[s] for s in sigma)[t] for t in tau)
            composite = tuple(names[sigma[t]] for t in tau)
            assert sequential == composite
print("PASS")
```

Validation checks this exact Python block, local document links and whitespace.
No Lean files, dependencies or tooling changed, so no Lean build or axiom audit
was run for this report. Independent Standards and Spec review is coordinated
by the enclosing orchestration; the paper derivation is not its own approval.
