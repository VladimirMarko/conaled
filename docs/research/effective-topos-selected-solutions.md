# Selected countdown solutions in the effective topos

Research deliverable for [#347](https://github.com/VladimirMarko/conaled/issues/347),
under [#289](https://github.com/VladimirMarko/conaled/issues/289).

**Result:** the effective topos with its halting dominance supplies the
conditional SDT package from [#337's report](context-dependent-partial-computation.md)
for the specified countdown certificate. The construction below is a paper
argument, not a new Lean formalization. Its substitution theorem concerns
morphisms of that topos, not arbitrary external functions. The checked external
construction in [#346](https://github.com/VladimirMarko/conaled/issues/346)
remains a separate provider.

Adopt this mathematical route as a concrete comparison; defer implementing an
entire realizability topos for this client alone. The calculation exposes a
limitation of the experiment: each successful certificate is uniquely fixed
by its indices. This allows a reversible reduction to termination information.
It does not justify replacing ambiguous parse witnesses, alternative traces,
or higher identity witnesses by propositions.

## Source foundation and concrete choice

The primary source is van Oosten and Simpson,
[*Axioms and (counter)examples in synthetic domain theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf)
(version of record, pages 233–278). Precise facts used:

- §3, page 266: in the effective topos Eff, take
  `Σ = {p : Ω | ∃n : N, p ↔ n ∈ K}`, with K the halting set.
  This dominance satisfies Axioms 1–4, including completeness of Σ and
  `false ∈ Σ`; it is closed under N-indexed existential quantification.
- Definitions 1.1–1.2, Theorems 1.4–1.5 and Definition 1.11 supply the lift L,
  initial algebra I, final coalgebra F, and completeness as orthogonality to
  `I → F`. Theorem 1.13 constructs a selected fixed point by extension to F.
- Page 245 gives closure of complete objects under exponentials and internal
  limits. Proposition 1.31 makes completeness imply well-completeness for this
  dominance; well-completeness means completeness of L(X) (Definition 1.15).
- Theorem 3.3 rules out identifying I with the internal colimit of finite
  lifting stages. We do not make that identification.

Eff is a plausible provider because the dominance records computational
termination and admits the required lifts. Choosing classical Set with an
unrestricted partial-map classifier would fail the fixed-point requirement;
that failure is not the investigation's substitute for constructing a model.

## Independently fixed client and reversible certificate encoding

All the following calculations are our paper derivation from the stated
source foundation. Work in Eff's intuitionistic internal language. Fix an
object Γ and morphisms `enabled : Γ → 2` and `size : Γ → N`. At `(γ,k)` let

```text
Cert(γ,k) = { (v,t) : Fin(size γ + 1) × List N |
              v.val = size γ ∧ t = [k,k-1,...,0] }.
```

The successful record `c(γ,k)` is specified before a solver is chosen. The
required partial result is exactly that record when enabled and undefined
otherwise. Equality means equality of these partial records in Eff; it does
not identify distinct possible data by decree. Internally finite sequences
can be represented by length-indexed N-tuples, so no unproved list-object
extension is needed.

There is an explicit isomorphism `Cert(γ,k) ≅ 1` in the slice over Γ×N:
forget the record in one direction, and return `c(γ,k)` in the other.
The equations fixing v and t prove the second composite is identity;
the proof components are predicates in the internal logic. This is not a
choice of a record from a bare existence statement.

Consequently `L(Cert(γ,k)) ≅ Σ`, with inverse

```text
p ↦ {c(γ,k) | p}.
```

Here a partial element is a subsingleton with Σ-valued domain. This inverse
retains the actual value and trace at every index. Applying the forgetful
map without carrying this inverse would not fulfill the client contract.

Write `D = Σ^N`. The state family `XΓ = ∏k L(Cert(γ,k))` is isomorphic,
over Γ, to the constant family Γ×D. D is complete by the cited exponential
closure. The pointwise strict L-algebra on D is

```text
a(A)(k) = ∃q ∈ A, q(k),        A : L(D).
```

Membership in Σ follows from the dominance law: the existence of q is a
Σ-proposition, and conditional on it the uniquely determined q(k) is in Σ.
The unit law is substitution of a singleton. The multiplication law is
associativity of existential quantification over nested partial elements.
These prove the monad-algebra laws, without requiring the countdown endomap
to preserve bottom. The same formula transports to XΓ through the displayed
isomorphism.

Completeness of Cert alone would not generally prove completeness of its
lift. Here the explicit lift isomorphism proves it directly from Σ.
Well-completeness is also available by the source's extra closure property,
but is not an additional unverified premise in this construction.

## Slices and base change

For any Γ use the induced dominance Γ×Σ in Eff/Γ. Its lift consists of
partial elements in a single fiber; on a constant family Γ×A it is Γ×L(A).
The unit is singleton and multiplication is union, both fiberwise. These
formulas give the comparison with pullback along any internal
`σ : Δ → Γ`, including empty and Boolean subcontexts.

For completeness, the slice requirements are more than a statement about
fibers at global points. Here they can be checked uniformly. Use Γ×I and
Γ×F with the constant structure maps. Finality of Γ×F follows by the same
N-recursion on successive definedness predicates for any coalgebra over Γ.
Initiality of Γ×I follows by parameterizing initiality of I: for an algebra
`A → Γ`, give its dependent section object `∏γ Aγ` the algebra that applies
the fiber algebra to the partial evaluation at γ. The unique map out of I
transposes to Γ×I → A. Transposing any competing algebra map proves
uniqueness. The argument also applies to strict algebras with successor.
No inhabitant of Γ or global section of A is assumed.

In the slice, restriction for the constant object Γ×D is
`Γ × (D^F → D^I)`, an isomorphism because D is complete. This establishes
completeness of the whole XΓ family via its isomorphism, rather than assuming
that arbitrary complete objects remain complete under arbitrary base change.
The N-indexed product is taken along Γ×N → Γ, so its pullback comparison is
the usual dependent-product base-change isomorphism.

All comparisons for L, I, F, inclusion, successor, infinity and the state
algebra are the displayed fiberwise maps. Pulling twice or pulling along a
composite gives the same formulas under canonical pullback identifications.
The certificate inverse also commutes with substitution: it reconstructs
`c(σδ,k)` in both routes. These establish the package required by #337 for
this family, not for every family of Eff.

## Calculate the selected extension, rather than merely a fixed point

Avoid confusing the final coalgebra F with the countdown functional, called
T here. Under the reversible state encoding, T is

```text
Tγ(q)(k)   = q(k)       if enabled γ = false
Tγ(q)(0)   = true       if enabled γ = true
Tγ(q)(k+1) = q(k)       if enabled γ = true.
```

Prepending the trace under the inverse encoding is exactly the original
certificate step. In particular, enabled zero does not preserve bottom.
The functional is an internal morphism: it uses Boolean elimination,
N-recursion and evaluation, not a decision procedure for arbitrary Σ.

The source's concrete description of F is descending sequences `φ : N → Σ`.
Its successor has `(sφ)(0)=true` and `(sφ)(k+1)=φ(k)`; infinity is constantly
true. The strict algebra on I is pointwise union of a partial element of I.
Define, uniformly in γ,

```text
hγ(φ)(k) = (enabled γ = true) ∧ φ(k),       φ : I.
```

This is in Σ by Boolean case distinction. It preserves the strict algebra:
conjunction with the fixed Boolean predicate distributes over the existential
quantifier defining union. It commutes with successor and T: in the enabled
case both sides shift the sequence; in the disabled case both are constantly
false and T leaves them unchanged. Initiality therefore identifies h with
the iteration map used in Theorem 1.13.

The same formula on **all of F** is an extension of h. Completeness makes it
the selected extension, so evaluation at infinity gives

```text
fix(Tγ)(k) = (enabled γ = true).
```

Decoding gives exactly `{c(γ,k) | enabled γ = true}`. This proves the
specified graph including the disabled bottom result; the identity
fixed-point equation on that branch alone would not select bottom.
The proof uses no assertion that I is N, no external supremum formula for
I, and no assertion that arbitrary fixed points are unique.

For `σ : Δ → Γ`, substitute σδ into this formula. Both the termination
predicate and its reconstructed record become those of the reindexed client.
For `τ : Θ → Δ`, the sequential and composite formulas coincide:

```text
τ*(σ*(fix TΓ)) = (σ ∘ τ)*(fix TΓ) = fix TΘ.
```

Take Γ = 2×N, `size(b,n)=n`, `enabled(b,n)=b`,
`σ(b,m)=(b,2m)` and `τ(t)=(true,t+1)`. These are internal morphisms defined
by finite arithmetic. At t=1 and k=2 both routes reconstruct **4 : Fin 5**
and **[2,1,0]**. Changing true to false gives the empty partial record.
There is no replacement of the selected record after transport.

## Boolean restrictions and comparison with the external provider

The object 2 and Boolean negation are legitimate here. Since negation has
no fixed point by Boolean elimination, 2 cannot carry a complete strict
L-algebra to which Theorem 1.13 applies. In fact completeness of decidable
objects does not supply a strict algebra. The lifted Boolean object has an
undefined element; lifted negation fixes it, which supplies no total Boolean.
Likewise Σ is not a Boolean object whose termination predicates can all be
complemented and decided. Thus neither the internal logic nor the endomap
class silently imports arbitrary classical functions on underlying sets.

For the countdown, comparing the displayed partial graph at ordinary
numerical inputs gives exactly the denotation proved in
[IndexedPartialComputation](../../Examples/IndexedPartialComputation.lean).
That is a paper comparison of this client, not a formal equivalence between
Eff and the classical ω-cpo provider, nor an extraction theorem. The latter
provider explicitly asks for continuous maps; the SDT construction asks for
internal morphisms and complete strict algebras. A general underlying-set
map need not meet the SDT morphism requirement.

Semantic existence is also separate from adequacy and execution. The formula
proves the semantic result, including a partial result on disabled inputs.
The obvious countdown program computes the selected record on enabled inputs
and loops on disabled inputs, but this report has not supplied a language
semantics and an operational adequacy proof relating that program to Eff.
Finite fuel exhaustion still means unknown. No timing or productivity claim
follows from either semantic construction.

## Costs, remaining scope and recommendation

The one-time cost of a Lean provider is substantial: a concrete realizability
topos, its internal language and lifting, initial/final structures, and the
orthogonality theorem would need checked counterparts. The repository's
[SelectedFixedPoint](../../SquareKit/SelectedFixedPoint.lean) instead reuses
Mathlib's external ω-cpo infrastructure. This report does not replace it.

For this SDT client, recurring obligations reduce to internal constructors,
the explicit certificate isomorphism and its substitution compatibility.
The local formulas above derive the selected-solution law; it is not a field
that each client is asked to prove in advance. They reveal a reusable
parameterized extension argument, but no measured agent-authoring advantage.

**Investigate next under #289:** a result family with multiple genuinely
observable certificates, for which reconstruction from a proposition is
impossible. Fix the chosen data independently, exhibit a complete lifted
family and its slice comparisons, then calculate the selected extension and
two substitutions. Preserve the present client as a specialization. Promote
a Lean Eff provider only when that consumer justifies its setup cost; a
smaller checked abstraction for extension and base change may suffice first.
Neither #107 nor #108 is reopened or selected by this recommendation.

Validation of this deliverable consists of the source/statement audit above,
checking local code references and Markdown links, and `git diff --check`.
No Lean files changed and no new Lean-checked SDT result is claimed.
