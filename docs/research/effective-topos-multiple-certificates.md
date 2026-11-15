# Selected SDT solutions with two observable certificates

Deliverable for [#354](https://github.com/VladimirMarko/conaled/issues/354),
under [#289](https://github.com/VladimirMarko/conaled/issues/289). This extends
the [unique countdown construction](effective-topos-selected-solutions.md).

**Result:** the same effective-topos dominance supports a countdown whose
result fiber contains two distinguishable valid records. An independently
specified recurrence selects one, including its dependent finite value and
trace. The construction below is a paper proof. No new Lean theorem, evaluator
adequacy theorem, or effective-topos implementation is claimed.

The distinction from #347 is mathematical: the lifted certificate fiber is
isomorphic to `L(2)`, not to the object of termination predicates. Its
completeness needs an additional source argument. Forgetting to termination
has no inverse on this fiber.

## Source obligations

Use van Oosten and Simpson,
[*Axioms and (counter)examples in synthetic domain theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf),
version of record, pages 233–278:

| Required fact | Source location |
|---|---|
| Eff with halting dominance `Σ = {p : Ω \| ∃n, p ↔ n ∈ K}` satisfies Axioms 1–4 and N-indexed existential closure | §3, p.266 |
| Decidable objects, including `2`, are complete under the standing axioms and Axiom 3 | Paragraph following Axiom 3, p.250 |
| Completeness implies well-completeness under Axioms 1–3 and that existential closure | Proposition 1.31, p.254 |
| Well-completeness of `A` means completeness of `L(A)` | Definition 1.15, p.245 |
| Complete objects are closed under exponentials and internal limits | p.245 |
| Initial strict lift algebra with successor and extension-selected fixed points | Theorems 1.5 and 1.13, pp.241 and 244 |
| Lift and its monad structure; final coalgebra and completeness | Definitions 1.1–1.2 and 1.11, §§1.1–1.2 |

In particular `L(2)` and `D = L(2)^N` are complete. Completeness of `2`
alone would not suffice: Proposition 1.31's model-specific hypothesis is
used. All maps below are internal Eff morphisms.

## A result family independent of selection

The rest of this report derives this client's construction from those facts.
Work in the intuitionistic internal language of Eff. A context Γ supplies
`enabled : Γ → 2` and `size : Γ → N`. Write `tr(k) = [k,k-1,...,0]` and

```text
payload(n,b) = if b then n else 0, as an element of Fin(n+1).

Cert(γ,k) = { (b,v,t) : 2 × Fin(size γ+1) × List N |
                v = payload(size γ,b) ∧ t = tr(k) }.
```

Here `b` is observable data. Finite lists may equivalently be encoded as
length-indexed natural-number tuples. Both bounds in `payload` follow from
`0 < n+1` and `n < n+1`. Define

```text
decodeγk(b) = (b, payload(size γ,b), tr(k)).
encodeγk(b,v,t) = b.
```

The displayed equations give inverse maps `Cert(γ,k) ≅ 2`, uniformly in Γ
and k. The proof fields are predicates of the internal logic. No selected
value occurs in the definition of this fiber. At every index, `decode(false)`
and `decode(true)` differ on their Boolean field; this remains true when
`size γ = 0` and their finite payloads coincide.

Specify the computation separately. Let `odd(n)` be parity, defined by
natural-number recursion with `odd(0)=false` and `odd(n+1)=not(odd(n))`.
On an enabled input at counter zero, return `decodeγ0(odd(size γ))`.
At a successor, wait for the predecessor's record, complement its tag,
recompute the corresponding finite payload, and prepend the successor to
its trace. On a disabled input, recur on the same state without output.
Thus the independent successful-result specification is

```text
selected(γ,k) = decodeγk(odd(size γ+k)).
meaning(γ,k)  = { selected(γ,k) | enabled γ = true }.
```

The recurrence and specification agree by parity induction. This agreement
is a property to prove, rather than a constraint deleting the other record
from `Cert`.

## Lift, algebra, and slice data

For an object A, write `L(A)` as Σ-partial elements: subsingletons of A whose
inhabitedness predicate lies in Σ. The pointwise state family is
`XΓ(γ) = ∏k L(Cert(γ,k))`. The explicit encodings above induce an isomorphism
of objects over Γ,

```text
XΓ ≅ Γ × D,       D = ∏k L(2).
```

Only the varying payload and trace are reconstructed by this isomorphism.
The Boolean at every defined coordinate remains data in `L(2)`.

For `Q : L(D)`, define the algebra by nested union:

```text
a(Q)(k) = { b : 2 | ∃q ∈ Q, b ∈ q(k) }.
```

There is at most one q and then at most one b. Its domain belongs to Σ by
the dominance law, first for Q and then for q(k). Singleton substitution
proves the unit law; reassociation of the two bounded existential quantifiers
proves the multiplication law. This is a strict L-algebra in the source's
monad-algebra sense. The computation's enabled-zero clause is allowed to
produce output from bottom.

For any Γ take the induced dominance in `Eff/Γ`. Lift, singleton, and union
operate in one fiber, giving `LΓ(Γ×A) ≅ Γ×L(A)`. The encoding of XΓ
transports the displayed algebra to the dependent records. To justify
completeness uniformly, rather than only at global points, take the initial
and final objects `Γ×I` and `Γ×F` with the constant structure maps. Here is
the parameter argument used for these claims:

- For an algebra `A → Γ`, its dependent section object `∏γ Aγ` has an
  algebra: evaluate a partial section at γ and apply the fiber algebra.
  Initiality of I produces the section-valued fold. Transposition produces
  `Γ×I → A`. Any competing slice algebra map transposes to a competing fold,
  so it is equal. The same argument includes a successor operation.
- For a coalgebra `A → LΓ(A)`, the total object A has a coalgebra
  `A → L(A)` after forgetting its base. The final map `A → F`, paired with
  `A → Γ`, is the required slice map. The coalgebra equation holds because
  every partial successor remains in the original fiber; forgetting the
  base proves uniqueness.
- Slice restriction for the constant state D is
  `Γ×(D^F → D^I)`, an isomorphism by completeness of D. Transport along
  `XΓ ≅ Γ×D` proves completeness of the whole family.

These arguments require neither an inhabitant of Γ nor a global section of
A. They establish the used constant structures and this explicitly
trivialized family; they do not claim that every varying family is complete.

For an internal `σ : Δ → Γ`, pullback gives the same formulas with γ replaced
by σδ. In particular, certificate encoding, partial union, initial inclusion,
successor, infinity, and the algebra commute with pullback. The product over
k uses the pullback of `Γ×N → Γ`; evaluation identifies its pullback with
the corresponding product over `Δ×N`. Identity and composite comparisons
coincide under the canonical pullback identifications. This supplies the
required base-change data, including the enabled/disabled subcontexts.

## Calculate the selected extension

Use the state encoding into D. If `not_* : L(2) → L(2)` maps every defined
Boolean to its complement and keeps the domain, the functional is

```text
Tγ(q)(k)   = q(k)                          if enabled γ = false
Tγ(q)(0)   = { odd(size γ) }                if enabled γ = true
Tγ(q)(k+1) = not_*(q(k))                    if enabled γ = true.
```

This is an internal morphism built from evaluation, finite case distinction,
and natural recursion. It never decides an arbitrary termination predicate.
For the initial object I, presented inside the descending Σ-sequences F,
define

```text
hγ(φ)(k) = { odd(size γ+k) | enabled γ = true ∧ φ(k) }.
```

Its domain is in Σ by Boolean case distinction. For any partial element U
of I, applying h to its pointwise union gives the Boolean above with domain
`enabled γ ∧ ∃φ∈U, φ(k)`. Applying `a ∘ L(h)` gives exactly the same
subsingleton. Thus h preserves the strict algebra, including bottom.

For successor s, `(sφ)(0)=true` and `(sφ)(k+1)=φ(k)`. In the enabled branch,
`hγ(sφ)(0)` is the base result. At a successor the domains on both sides
coincide and `odd(size γ+k+1)=not(odd(size γ+k))`. Hence
`hγ ∘ s = Tγ ∘ hγ`. In the disabled branch both h values are bottom and
T acts as identity. Initiality identifies h as the iteration map used to
select the fixed point.

The same displayed formula defines a morphism `h̄γ : F → D` extending h.
Completeness makes this extension unique. At infinity, every coordinate of
φ is true, so

```text
fix(Tγ)(k) = { odd(size γ+k) | enabled γ = true }.
```

Decoding proves `fix(TΓ) = meaning`. It retains the chosen tag, finite value,
and trace. On disabled inputs the equation `T(q)=q` alone would allow every
q; the extension construction selects bottom. The argument does not identify
I with a natural-number iteration chain or assume uniqueness of fixed points.

## Two substitutions and the information-loss control

Every construction is uniform in γ, so for internal σ and τ:

```text
Rσ(fix TΓ)(δ,k) = { selected(σδ,k) | enabled(σδ) = true },
Rτ(Rσ(fix TΓ)) = R(σ ∘ τ)(fix TΓ) = fix TΘ.
```

Take `Γ = 2×N`, `size(b,n)=n`, `enabled(b,n)=b`,
`σ(b,m)=(b,2m+1)` and `τ(t)=(true,t+1)`. Both are nonidentity internal maps.
At `t=1`, `k=2`, their composite supplies `size=5`; both routes retain
**`(true, 5 : Fin 6, [2,1,0])`**, since `odd(5+2)=true`. The other valid
record at the same index is **`(false, 0 : Fin 6, [2,1,0])`**. Changing τ's
Boolean to false gives the empty partial record in both routes. The fiber
really changes with the substituted size; this is not an unindexed Boolean
example followed by forgetting its payload.

Let `dom : L(Cert(γ,k)) → Σ` forget the result. Both singleton records above
map to true. A left inverse for dom would therefore identify their tags,
contradicting `false ≠ true`. A decoder given only the domain cannot recover
every valid result. More concretely, change the base selector to
`not(odd(size γ))` while keeping the same fiber, step and enabled flag.
The same extension calculation selects the complementary tag at every k,
with exactly the same termination domain. Thus even two independently fixed
computations with identical termination behavior require different data.
A decoder additionally supplied with a particular selector can reconstruct
its output, but that extra information is precisely what dom discarded.

## Recover the unique countdown and compare providers

The proof has a small reusable form. Let a fixed complete object A have
complete lift, let `Cert(γ,k) ≅ A` be a uniform encoding, and specify
`bγ : A`, `uγk : A → A`. Define `vγ0=bγ` and
`vγ(k+1)=uγk(vγk)` by recursion. Then use

```text
Tγ(q)(0) = {bγ};    Tγ(q)(k+1) = L(uγk)(q(k))
hγ(φ)(k) = {vγk | enabled γ ∧ φ(k)}
```

with the same disabled clause. The union, successor, extension, and
base-change arguments above apply. The present client uses `A=2`,
`bγ=odd(size γ)` and `uγk=not`. This formulation requires the actual encoding
and maps; mere existence of some inhabitant is insufficient.

For #347 take `A=1`, its only base and transition maps, and the old encoding
`* ↦ (size γ : Fin(size γ+1), tr(k))`. Then `L(1) ≅ Σ` and the general
formula is exactly the earlier selected countdown. This is a specialization
of the construction, not a claim that restricting today's alternating
program to the true-tag subset preserves its transition. That subset is
not invariant under complement.

For the external provider of [#346](context-dependent-partial-computation.md),
use the same records in flat partial orders and the same three functional
clauses. Constants, projections, and partial mapping of the tag transition
preserve increasing-chain suprema. The nth approximant is the singleton
selected record precisely when enabled and `k<n`; otherwise it is bottom.
Induction proves this formula, and taking the supremum proves the same
selected graph. Reindexing is strict and continuous and intertwines the
functional, so the existing
[`SelectedFixedPoint.map_solution`](../../SquareKit/SelectedFixedPoint.lean)
has the needed hypotheses. This is a paper instantiation of a checked generic
theorem, not a new checked instance of the two-tag client. The checked
[`IndexedPartialComputation`](../../Examples/IndexedPartialComputation.lean)
still implements the unique-result specialization.

The comparison is equality of the displayed records on numerical inputs.
It supplies no equivalence between Eff and the external ω-cpo setting.
Externally continuity must be proved for the allowed functions; internally
the functions must be morphisms of Eff. Arbitrary set functions on underlying
carriers do not acquire this property merely from their type.

## Architectural consequence and validation boundary

This consumer requires preserving values in a partial element through
extension and substitution. Termination-only machinery fails its negative
control. A small future checked interface could separate:

1. A chosen initial iteration map and uniquely extendable inclusion.
2. The strict algebra and successor laws producing that map.
3. A comparison preserving those structures, extension and evaluation.

Its global selected-result transport should be derived from those local
laws, rather than supplied by each caller. The pointwise formulas here show
what a concrete provider must discharge. The existing external provider
already derives transport from strict continuous intertwining; it needs no
replacement. #289 owns a future checked extension/base-change interface,
triggered by a second nonconstant, nontrivializable dependent client or an
actual compiler consumer requiring that interface. A full Lean Eff provider
remains deferred: this example adds no need to formalize an entire topos.

Semantic selection, operational adequacy and executable evaluation remain
separate. A finite-fuel approximation exposes the selected record only after
`k+1` unfoldings; before that its empty result means unknown. An enabled
countdown program with parity and tag complement is an evident operational
candidate, but no language semantics or adequacy proof relating such a
program to Eff is provided here. Nothing here measures agent productivity.

The source audit checked the specific completeness implication for `L(2)`
and the hypotheses of extension selection. The statement audit checked the
two inverse certificate maps, algebra union laws, the parameter argument in
slices, the strict iteration equation, both substitutions, the complementary
selector control, and the singleton specialization. These are paper arguments.
Validation additionally checks local Markdown targets and whitespace. No Lean
sources change, so there is no new build or proof-audit claim for this report.
[#107](https://github.com/VladimirMarko/conaled/issues/107) remains paused and
[#108](https://github.com/VladimirMarko/conaled/issues/108) remains unselected.
