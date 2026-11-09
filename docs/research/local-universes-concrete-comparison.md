# Local universes on finite dependent families

Research for [#424](https://github.com/VladimirMarko/conaled/issues/424), under
[#289](https://github.com/VladimirMarko/conaled/issues/289).
**Retain local universes as a model-construction option; defer a general Lean
framework and migration.** The construction below supplies full comprehension,
LF, weak dependent sums, and a strictly stable replacement in a small setting.
It removes repeated pullback-presentation comparisons. Direct indexed families
already remove those comparisons with less setup in this setting. This is a
positive coherence example, not evidence of savings for higher eliminators.

This report extends the unconstructed weak-model route in the
[#366 comparison](architecture-scaling-study/designated-map-comparison.md).
It does not reopen that report's designated-map result. The
[architecture reassessment](dependent-architecture-reassessment.md) and
[concrete coherence assessment](concrete-dependent-coherence.md) identify the
larger model-admission problem. Their older missing-higher-model descriptions
must be read with the reassessment's subsequent cubical and strict two-groupoid
results. The present experiment has no incumbent-client prerequisite.

## Source result and equality boundary

Lumsdaine–Warren, [arXiv:1411.1736v2](https://arxiv.org/abs/1411.1736v2),
revised 6 April 2015, is the version used. Its abstract page identifies the
v2 correction to pseudo-stability. The following is a paraphrase of its
[definitions and results](https://arxiv.org/html/1411.1736v2).

Theorem 3.4.1: a full comprehension category satisfying LF and possessing weakly
stable binary sums, Π, Id, Σ, zero, unit, or W-types yields the corresponding
strictly stable structure on its split replacement C!. W-types are relative
to a stable class of Π-types. Full means the comprehension functor is fully
faithful (§2.1). LF requires finite products and dependent exponentials for
`Z →g Y →f X`, with f display and g display or a product projection
(Definitions 3.1.2–3.1.3). Id uses Frobenius elimination over arbitrary finite
dependent tails (§3.4.3). Weak stability requires elimination after every
reindexing, not preservation of previously selected eliminators. Witnessed
existence, or choice, supplies selections (§2.3). Lemma 2.4.2's right-splitting
route instead requires pseudo-stability. Section 4.1 gives a heuristic for
further finitary rules, excluding additional type-equality rules. Neither UIP
nor an object-language classifier is a hypothesis of Theorem 3.4.1.

Everything proved below is a paper-level construction for finite sets.
The repository's existing Lean specialization is identified separately; this
report does not formalize the general theorem or add an axiom to the library.

## Semantic contract fixed before presentation

The chosen fragment has a terminal context, substitutions, dependent context
extension, terms as sections, and Σ with pairing, dependent elimination, and
β. For every Γ, family A over Γ, family B over Γ.A, motive C over Γ.Σ(A,B),
and branch d over Γ.A.B with values in C at the pair, elimination must return
a section of C whose restriction to pairs is d. Substitution must preserve
these operations and their result types, including two successive substitutions.
The contract does not request Π, Id, a universe, or an equality of different
type presentations. The concrete model also validates Σ eta; the argument
does not use eta as a source-language requirement.

Contexts are all finite sets and substitutions all functions. Types are all
maps of finite sets into a context, terms are sections, and comprehension
is the domain of that map. Thus there are genuinely varying fibers and empty
fibers. We use finite sets in a fixed ambient set universe, not a finite bound
on cardinality or a category containing only generated contexts. Every product,
function set and parameter object constructed below is finite. Collections of
all such objects live in the metatheory; no finite object classifies all of
them. No skeleton or chosen enumeration is needed.

Model builders encounter this contract when presenting finite dependent data
as maps rather than as an indexed family. Eventual authors can form a pair
whose second value's admissible range depends on the first, then eliminate it
into another dependent family. This tests dependent substitution without
pretending to test path-sensitive transport or nontrivial higher cells.

## A weak presentation with an actual strictness failure

Let C be FinSet and T its arrow category, with codomain projection and
comprehension the identity functor into the arrow category. A morphism is
**every** commuting square. Full faithfulness is immediate: the hom-set map
is the identity, including squares whose horizontal maps are not bijections.
For `p:E→Γ` and `σ:Δ→Γ`, choose the pullback

```text
Pσ(E) = {(δ,e) | σ(δ)=p(e)},   projection (δ,e) ↦ δ.
```

For any commuting cone `(u:W→Δ, v:W→E)`, the unique factor is
`w ↦ (u(w),v(w))`. This proves the cartesian lift property with the actual
arrows, not just with sections or bijections.

These choices do not split codomain strictly. Iterated pullback contains
`(θ,(τ(θ),e))`, while pullback along `σ∘τ` contains `(θ,e)`. The comparison
`kσ,τ(θ,(δ,e))=(θ,e)` has inverse `(θ,e)↦(θ,(τ(θ),e))`.
The unit comparison drops the redundant base coordinate. The two composites
on triple pullbacks both discard the two intermediate coordinates, so the
associativity comparison diagram commutes. These are specified bijections,
not literal identifications of the chosen sets. For singleton base and fiber
labelled by `0`, even pulling back the identity twice produces different
nested ordered pairs. This failure uses the ordinary pullback convention;
it does not deliberately choose an incoherent constructor to inflate cost.

For `q:F→E` over `p:E→Γ`, choose Σ to be `p∘q:F→Γ` and pairing the identity
on F. Every motive `r:D→F` and branch section d therefore has eliminator d,
with β an equality of maps. After σ, the iterated extension has elements
`((δ,e),z)` with `q(z)=e`, whereas the reindexed Σ has elements `(δ,z)`.
Pairing is the bijection

```text
κσ((δ,e),z) = (δ,z),    κσ⁻¹(δ,z) = ((δ,q(z)),z).
```

For **any newly supplied** motive `C'→Pσ(F)` and branch d' over the iterated
extension, the eliminator at `(δ,z)` is d' at `κσ⁻¹(δ,z)`, viewed in its
prescribed C' fiber. This supplies weak stability and computation for all
finite motives and branches, not merely the pullback of an old motive.
The chosen Σ of the reindexed inputs has domain the iterated extension,
which differs from `Pσ(F)`. Hence the raw chosen structure is not strictly
stable despite having coherent comparisons and unique eliminators. This
example does not separate weak stability from pseudo-stability: it satisfies
the stronger condition too.

## LF constructed on the whole slice hom-sets

The terminal singleton and cartesian products have their usual unique-map
and pairing properties. For arbitrary maps `g:Z→Y` and `f:Y→X`, define

```text
P = {(x,s) | x∈X, s assigns to every y∈f⁻¹(x) an element s(y)∈g⁻¹(y)}.
π(x,s)=x;       ev((x,s),y)=s(y).
```

The finite dependent product over an empty fiber is the singleton containing
the empty function; a product with an empty required factor is empty. Thus
P always exists as a finite set and `ev:P×X Y→Z` is over Y.
For **every** finite W and map `h:W→X`, the inverse functions

```text
Hom/X(W,P)  ↔  Hom/Y(W×X Y,Z)
k            ↦  ((w,y) ↦ second(k(w))(y))
(w ↦ (h(w), y ↦ ℓ(w,y)))  ↤  ℓ
```

are well typed by the respective triangle equations. Both inverse equations
hold by evaluation and function extensionality. For every `u:W'→W` with
`h'=h∘u`, currying `ℓ∘(u×id)` gives `w'↦(h'(w'), y↦ℓ(u(w'),y))`, exactly
the precomposition of the curried map with u. This proves naturality on all
slice morphisms. It covers more than LF asks: all maps are displays here,
and product projections are included. For `g:Y×V→Y` the fiber is precisely
the finite function set `f⁻¹(x)→V`, which will parameterize second-family names.
These metatheoretic dependent products do not add source-language Π.

## Local presentation, Σ, and the dependent eliminator

Write `E_A(a)` for the fiber of a finite map `E_A→V_A`. A local type is
`A=(V_A,E_A,n_A:Γ→V_A)` and decodes to the chosen pullback of E_A along n_A.
Its extension has elements `(γ,x)` with `x∈E_A(n_A γ)`. Define

```text
A[σ] = (V_A,E_A,n_A∘σ)
σ⁺(δ,x) = (σ(δ),x)
t[σ](δ) = t(σ(δ)).
```

Here a term is written by its fiber component. A map into the extension is
uniquely its base map plus such a term. Morphisms between local types are
all squares between their decoded projections; comprehension is again fully
faithful by this definition. The lift σ⁺ satisfies the pullback property.
Its identities and composites agree as maps, and local types satisfy
`A[id]=A` and `A[σ][τ]=A[σ∘τ]` by equality of naming functions. Decoding is
essentially surjective: `p:E→Γ` is represented by `(Γ,p,id)`, with decoded
projection isomorphic to p by `(γ,e)↦e`. This is not equality of presentations.
Strict here means equality in the mathematical model, using extensional
equality of functions. It does not assert that every corresponding Lean
equation would be definitional equality.

Given B over Γ.A, construct the finite parameter object and its generic fiber:

```text
VΣ = {(a,b) | a∈V_A, b:E_A(a)→V_B}
S(a,b) = {(x,y) | x∈E_A(a), y∈E_B(b(x))}
nΣ(γ) = (n_A(γ), x ↦ n_B(γ,x)).
```

VΣ exists by the product-projection case of LF just constructed. The generic
dependent sum has total set `{(s,z) | s∈VΣ, z∈S(s)}` over VΣ. It is the
composite of the generic first and second display maps, with the redundant
coordinates removed by the explicit pairing bijection. Its weak elimination
is therefore the one proved above, transported along that bijection.
The local Σ is `(VΣ,S,nΣ)` and its pair map is
`((γ,x),y)↦(γ,(x,y))`.

After σ, B's name is `n_B∘σ⁺`, so the new name is
`δ↦(n_A(σδ), x↦n_B(σδ,x))=nΣ∘σ`. VΣ and S are unchanged. Thus formation
and pairing are strictly stable, including the dependent second argument.
Using only `V_A×V_B` would be wrong: b must name B separately for every x.

The eliminator also has a parameter object; formation alone is insufficient.
Fix a local motive universe `(V_C,E_C)` and define the finite set

```text
Vel = {(s,c,d) |
  s∈VΣ,
  c:S(s)→V_C,
  d assigns each (x,y)∈S(s) an element of E_C(c(x,y))}.
```

The c coordinates use the product-projection case of LF; the d coordinates
use its display case. Form the motive over `{(s,c,d,z) | z∈S(s)}` with fiber
`E_C(c(z))`. Its generic branch assigns d(x,y), and its generic eliminator is
`j(s,c,d,z)=d(z)`. β holds by evaluating at `(x,y)`.

For any C over Γ.Σ with name `n_C(γ,z)`, and any well-typed branch d₀ on
Γ.A.B, the representing map is

```text
nel(γ) = (nΣ(γ), z ↦ n_C(γ,z), (x,y) ↦ d₀((γ,x),y)).
split(C,d₀)(γ,z) = j(nel(γ),z).
```

Its value lies in `E_C(n_C(γ,z))`, the actual motive fiber. Every finite
local motive and every branch has this representation. Substitution changes
nel to `nel∘σ`, so elimination and β are stable as well. This parameterization
does not select an eliminator separately for each Γ. In this particular model
elimination is unique anyway: the generic construction supplies no advantage
over direct case analysis. All selections have explicit formulas; no choice
principle is needed for this example.

The construction also works with a differently presented generic sum and a
specified bijection `κ_s:S(s)≅S'(s)`: pair with κ, decode with κ⁻¹, and define
the generic eliminator as `d(κ⁻¹(z))`. Keep κ fixed over VΣ. Strict substitution
then still follows because σ changes only the name. The comparison κ remains
data and is not silently replaced by equality.

## Direct construction and retained dependent data

For the same semantic contract, directly use finite indexed families
`A:Γ→FinSet`, substitution by composition, extension by dependent sum,
`Σ(A,B)(γ)={(x,y) | x∈Aγ, y∈B(γ,x)}`, and dependent case analysis
`split(C,d)(γ,(x,y))=d((γ,x),y)`. Formation, pairing, and split commute with
substitution by evaluating at σγ. Repeating with τ evaluates at σ(τθ).
No LF proof or generic eliminator parameter object is required to define this
model. Passing from raw maps to their fiber families retains the explicit
map-total-space comparison; it does not make the original raw pullbacks equal.

The local route decodes into exactly these families. For the displayed S,
the Σ decoder preserves both components. With S' it uses κ⁻¹ and carries
the motive and branch along that same comparison. The unit comparison is
identity; comparison of a composite is composite comparison, and both routes
evaluate a substituted term at σ(τθ). Thus the comparison includes terms and
dependent result types, not merely equal fiber cardinalities.

A concrete finite instance fixes `Γ={0,1,2}`, `A(n)={0,…,n}`, and
`B(n,i)={0,…,i}`. Select `w(n)=(n,n)`. Take `Δ={a,b}`, `σ(a)=1`, `σ(b)=2`,
`Θ={*}`, and `τ(*)=b`. Both routes yield `(2,2)` in
`Σ i∈{0,1,2}. {0,…,i}` after the two substitutions. The motive
`C(n,(i,j))={0,…,j}` has branch `d((n,i),j)=j`; elimination at the selected
pair yields 2 in `{0,1,2}`. Replacing the second component by 0 changes both
the chosen value and the motive's fiber to `{0}`. Such an erasure fails this
contract even though it remains a well-typed pair in the original sum.

This is a positive dependent-value control. A separate presentation control
refutes the stronger equality claim: over a singleton context, a constant
singleton family presented by `V=1` and the same family presented by `V=2`
with a fixed name decode to isomorphic fibers but have unequal parameter
objects. No decoder comparison can imply equality of those records. Hence
an extra rule demanding equality of arbitrary presentations is not validated
by this construction. Object-language Id is absent from the fragment. If
interpreted by equality of finite-set elements, its identity fibers would be
empty or singleton. That extension could not detect distinct higher cells;
this limitation must not be imported into the general coherence theorem as
a UIP assumption.

## Cost, repository evidence, and disposition

| Obligation | Raw maps with direct comparisons | Direct indexed families | Local universes |
|---|---|---|---|
| Setup | Chosen pullbacks and flattening comparisons | Families, extension, substitution | Raw comprehension, LF, local records and decoding |
| Σ construction | Composite map and pairing comparison after base change | Fiberwise pairs and case analysis | VΣ, generic sum, names, and Vel for elimination |
| Repeated substitution | Carry specified flattening bijections and their composition | Evaluate functions at the composite | Compose names; retain generic choices |
| Extension to another constructor | Construct semantics and coherent comparisons | Construct semantics and its substitution equations | Construct weak semantics and representing objects for its premises |
| This experiment's saving | Baseline presentation work is visible | Already avoids that work | Also avoids it, with more setup than indexed families |

This is a comparison of mathematical obligations, not measured developer
time or an author trial. The raw-map route even has canonical comparisons;
we found no difficult incoherent choice of filler here. Consequently this
experiment justifies neither a general savings claim nor rejection of local
universes for models where fillers have only weak stability.

At the inspected repository revision,
[SquareKit/LocalUniverses.lean](../../SquareKit/LocalUniverses.lean) already
constructs Type-family local records, comprehension, Σ, pairing, and
`displayCurry` with naturality. Its `sigma_reindex` and `pair_twice` preserve
the dependent second family. [FamilySquares](../../SquareKit/FamilySquares.lean)
identifies dependent functions with all commuting projection squares.
[Examples/LocalUniverses.lean](../../Examples/LocalUniverses.lean) retains
nonconstant dependent pairs and proves `presentation_ne` despite decoded
equality. [Dependent.lean](../../Dependent.lean) supplies the direct split
family baseline. These inspected declarations corroborate parts of the
construction; they do not constitute a Lean proof of the raw FinSet
comprehension package, its full slice LF theorem, or Vel above. No claim here
depends on a new Lean declaration.

Adopt the explicit example as evidence that the weak-comprehension route is
constructible and that presentation coherence can be isolated. Defer a general
framework: the best direct route is already simple on the selected fragment.
Reject only the shortcuts of equating decoded presentations, dropping
dependent components, or inferring a higher interpretation from finite sets.
The unconstructed packages for other models remain obligations, not
impossibility results.

A bounded formalization successor is reasonable if #289 wants a reusable
model-builder regression: extend the existing specialization with dependent
Σ elimination and its representing object, then formalize the FinSet
codomain LF hom-bijection and the explicit comparison to indexed families.
Require arbitrary motive/branch quantifiers, both inverse equations,
naturality on all slice arrows, repeated substitution, and the selected finite
pair/motive above. Keep its API experimental, with EDD statement review and
the applicable build/proof audit. Do not create a general weak-model record
merely to restate these examples. This scope needs neither migration nor a
second library client; it would provide a checked bridge that this report
currently establishes only on paper.

For a stronger follow-up, select one weak homotopical model and one fragment
with an eliminator whose chosen fillers have a real stability burden. Supply
its actual comprehension morphisms, LF representation, arbitrary-motive
weak elimination with computation, and size closure before comparing generic
selection with a direct strict choice. For Id, include every admitted finite
dependent tail, selected higher witnesses, and their comparison under
substitution. Existing direct higher implementations do not discharge these
obligations for a different weak model. Nor must an exploratory weak model
first implement an incumbent strict interface.

For a combined modal/higher setting, local universes could remove a final
substitution-coherence burden **after** the joint semantic operations exist.
This example constructs no modality, context-changing modal substitution,
interaction law, higher identity, or their joint weak stability. A successor
must specify how modal operations act on local parameter objects and generic
constructors, and prove the required mixed laws and any demanded type
equalities separately. Independently strictifying two fragments does not
construct their interaction. Assign that admission question under #289 with
#36/#235/#290 coordination; this report chooses no combined architecture.
[#107](https://github.com/VladimirMarko/conaled/issues/107)'s pause and
[#108](https://github.com/VladimirMarko/conaled/issues/108)'s independent-test
gate remain unchanged.

## Evidence and validation record

Repository inspection base and incorporated integration tip:
`d7debd4e0d510a1a5f8d18513a1fb80e69e51410`. The task specification was the
coordinator's immutable `/tmp/conaled-424-425/424-spec.md`. Only this report
is changed. The manuscript was accessed on 2026-11-09 as arXiv v2 HTML and
the versioned source archive. The HTML's generated title date differs from
the submission date; the version identity above follows arXiv's submission
history and source URL. Source archive SHA-256:
`545175cf105359f0fc24201570fa892de7894ab16ecd7a6b520b98e94d03f9a0`.
The archive was extracted outside the repository. No full-text access limit
prevented inspection; the HTML contains noisy TeX diagram expansions, so
the TeX source was used to check definitions and hypotheses.

Source acquisition, after `direnv allow .` authorized this worktree's existing
`.envrc`, used:

```sh
direnv exec . bash -c 'curl -L --fail https://arxiv.org/src/1411.1736v2 -o /tmp/conaled-424-425/lw-v2.tar && mkdir -p /tmp/conaled-424-425/lw-v2 && tar -xf /tmp/conaled-424-425/lw-v2.tar -C /tmp/conaled-424-425/lw-v2'
sha256sum /tmp/conaled-424-425/lw-v2.tar
```

The first attempt stopped because direnv had not yet authorized the isolated
worktree; retry after authorization succeeded. Validation for this Markdown-only
change checks whitespace, local link targets, and the incorporated base.
It does not rerun Lean or claim new kernel-checked mathematics. Independent
Standards and Spec review is coordinated in the enclosing implementation loop.

```sh
direnv exec . python3 /tmp/conaled-424-425/validate-424.py
direnv exec . git diff --check
direnv exec . git merge-base --is-ancestor orchestration/424-425 HEAD
direnv exec . git rev-parse HEAD orchestration/424-425
```

The Python check strips fenced and inline code before inspecting links,
verifies all seven relative file targets, balanced fences, and the prose
punctuation check. All passed; the ancestor check exited zero and the two
revisions matched the base above before committing. The initial naive link
scan misread mathematical code `t[σ](δ)` as a Markdown link; stripping code
corrected the check. This was a validation-script false positive, not a broken
document link. Self-review also checked each hom-set domain, the empty-fiber
cases, motive typing and branch quantifiers, the two inverse comparisons,
and the separation between model equality and presentation isomorphism.
