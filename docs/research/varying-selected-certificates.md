# Varying finite certificates and selected partial solutions

[#361](https://github.com/VladimirMarko/conaled/issues/361) tests the interface
question left by [the two-tag construction](effective-topos-multiple-certificates.md).
The new client has changing fiber cardinalities and non-surjective maps of
valid certificates. The checked external construction still uses
[`SelectedFixedPoint.map_solution`](../../SquareKit/SelectedFixedPoint.lean)
without adding a global transport assumption. An independent internal
construction below establishes applicability in Eff on paper by a bound-filter
argument. Neither result requires replacing the existing external provider.

## Independent client and discrimination

Take a capacity n, a seed j≤n, an enabled Boolean b, and a counter k. A valid
certificate is a value v in `Fin(n+k+1)` and the trace `[k,k-1,...,0]`.
The bound and trace equation specify validity; they do not constrain v to the
chosen result. The program specification starts at value j when k=0 and
increments the preceding value at each successor. Disabled states recur
without returning. Thus the independently required partial graph is

```text
meaning(b,n,j,k) = {(j+k, [k,k-1,...,0]) | b=true}.
```

Equality compares the whole partial certificate, including its finite bound
and trace. Proof fields are propositions; no additional proof observations
are claimed. This is a mathematical countdown client, not a compiler or a
benchmark for an external language.

At k=0 every one of the n+1 values can be selected by a permitted seed. At
larger k every bounded value remains a valid certificate, although this
recurrence reaches only j+k. The family is isomorphic to `Fin(n+k+1)`, not to
a fixed Boolean tag: the fibers at (0,0) and (1,0) have different cardinalities.
The checked `no_fixed_tags` rules out a common type with equivalences to all
fibers. A natural-number encoding remains possible, but it must retain the
varying bound predicate. Dropping that predicate would admit invalid values.
The previous constant-tag completeness proof therefore does not apply as
written. This is not a claim that dependent data cannot be encoded at all.

The two parameter changes are

```text
A: (b,n,j) ↦ (b,n+1,j),       v ↦ v;
B: (b,m,j) ↦ (b,m+2,j+1),     v ↦ v+1.
B∘A: (b,n,j) ↦ (b,n+3,j+1),  v ↦ v+1.
```

Both preserve the trace and change the actual target certificate type. A
misses the new maximal value; B misses zero. These are proper embeddings,
not inverse presentations or pullback renamings. In particular they test more
than the old substitution example. With n=1,j=0,k=2 the successive values
are 2 in Fin 4, 2 in Fin 5, then 3 in Fin 7, always with `[2,1,0]`.

## Checked external provider

[The checked client](../../Examples/VaryingPartialCertificates.lean) reuses
Mathlib's pointwise ω-cpo of `Part` records. Its `functional` uses a constant
at zero, partial mapping of `step` at successors, and identity on disabled
states. Continuity is proved from constant, evaluation and partial-map
continuity. The classical external specification permits arbitrary index
sets; this client needs only Nat and finite values.

The mathematical background is Abramsky and Jung,
[*Domain Theory*](https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf),
Theorem 2.1.19 and Lemma 2.1.21: least fixed points in pointed dcpos arise from
iteration, and strict continuous intertwining preserves them. Sections
3.2.1 and 3.2.5 provide products and lifting. The checked implementation needs
only increasing countable chains.

The proof order in the client is:

1. `approximants_eq_bounded`: fuel f returns the specified certificate exactly
   when enabled and k<f. Otherwise its observation is empty.
2. `solution_eq_meaning`: leastness gives one inequality, and the (k+1)st
   approximant gives the other. Disabled identity coordinates select bottom,
   even though their fixed-point equations admit other answers.
3. `embed d h` translates v to v+d when n+d≤m. Its proof retains the new bound
   and the old trace. `embed_step` and `embed_selected` are the local laws.
4. `transport` partially maps that embedding at each k. It is continuous,
   `transport_strict` preserves bottom, and `transport_step` intertwines
   the functionals. `transport_solution` applies the existing generic
   `map_solution`; the desired selected-result equality is not a premise.
5. `transport_comp` compares sequential and composite maps on every partial
   state. `two_changes` applies the transport theorem twice. The numerical
   application checks the independently calculated 3 and its retained trace.

This is a concrete provider and a second checked client of the existing
bounded interface. No new class or extension operator is needed to obtain
this external theorem. The old unique-certificate client remains unchanged.

The control `same_domain` applies to arbitrary seeds in the same capacity.
`different_selection` shows that seeds 0 and 1 at n=1,k=2 return distinct
certificates despite both domains being true. Termination observation cannot
reconstruct both. This also distinguishes two actual selected computations,
not merely two unused inhabitants of a type. `first_not_surjective` and
`second_not_surjective` check both changes on the entire certificate family.

## Internal specification and source hypotheses

The internal alternative uses Eff with the halting dominance, Σ-partial
singletons L, and internal arithmetic and finite sequences. It specifies the
same graph independently of the external order. Its maps must be Eff
morphisms; arbitrary external functions are not inputs to this account.

The primary source is van Oosten and Simpson,
[*Axioms and (counter)examples in synthetic domain theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf).
The source inputs used here are:

| Source location | Input |
|---|---|
| Definitions 1.1–1.2, Theorems 1.4–1.5 | Lift monad, initial iteration structure I, final coalgebra F |
| Definition 1.11, Theorem 1.13, p.244 | Completeness is unique extension along I→F; extension at infinity selects a fixed point |
| p.245 | Complete objects form an exponential ideal and are closed under retracts |
| p.250 following Axiom 3 | Decidable objects, including N, are complete |
| Definition 1.15, Proposition 1.31 | Under Axioms 1–3 and Σ's N-existential closure, complete objects have complete lifts |
| §3, p.266 | Eff's halting dominance satisfies these hypotheses |

Thus `D=L(N)^N` is complete. The following dependent construction and
transport argument are this report's paper derivation, not an additional
source theorem or a Lean-checked Eff provider.

### Establish completeness without a fixed fiber

Let Γ contain the parameters (b,n,j) with j≤n. More generally they may be
internal morphisms on an arbitrary context. At γ define
`Xγ=∏k L(Fin(nγ+k+1))`; attach the canonical trace to recover Cert exactly.
Embed X into Γ×D by forgetting only the finite bound proof. Define a
parameter-dependent idempotent on D by

```text
eγ(q)(k) = {v ∈ q(k) | v < nγ+k+1}.
```

The predicate on v is decidable. Its partial domain is in Σ: under the
Σ-domain of q(k), decide the finite comparison, then apply the dominance
composition law. No decision of the domain of q(k) is used. Applying the
filter twice has the same result. The fixed subobject of eγ is precisely Xγ:
all defined values satisfy the bound, so they uniquely lift to Fin; conversely
forgetting a bounded value is fixed by the filter. This is a retract of a
constant complete ambient family, not an equivalence to that constant family.

Here is the full parameterized extension check. Given a map h:Γ×I→X over Γ,
forget bounds and transpose to I→D^Γ. Completeness of D and its exponential
ideal property give a unique extension H:Γ×F→D. Both H and
`(γ,φ) ↦ eγ(H(γ,φ))` extend the same map on Γ×I. Uniqueness makes them equal,
so H factors uniquely through X. The bound reconstruction above makes that
factorization an internal morphism. This proves completeness in the required
slice, including generalized parameters, without claiming completeness of
every dependent family.

The partial singleton algebra on X is coordinatewise nested union:
`a(Q)(k)={v | ∃q∈Q, v∈q(k)}`. The resulting value retains the bound from q;
the dominance law gives its domain. Singleton insertion and reassociation of
the two bounded existential quantifiers prove the unit and multiplication
laws. The algebra is strict in the monad-algebra sense. This is a different
use of “strict” from bottom preservation of an external order map.

The slice iteration objects can be taken as Γ×I and Γ×F. For initiality,
transpose a fiber algebra with successor to its object of dependent sections:
a partial section is evaluated at γ and the fiber algebra applied. Unit,
multiplication and successor laws hold pointwise; initiality of I gives the
unique fold. For finality, a coalgebra over Γ gives a total-object coalgebra
after forgetting Γ. Its unique map to F, paired with the unchanged base,
is the unique slice coalgebra map. These constructions require no global
section of Γ. They justify the iteration structures used by the extension
argument, rather than presupposing a general theorem about all slices.

### Selection and the two changes

The internal functional T has the same independently stated recurrence:
return j at zero, increment a predecessor value at successors, and use the
identity when disabled. Increment preserves the changing bound. All these
operations are internal maps built from arithmetic, evaluation and finite
case distinction.

For φ in I, viewed as a descending sequence of Σ-predicates, set

```text
hγ(φ)(k) = {(jγ+k, trace(k)) | bγ=true ∧ φ(k)}.
```

Its value is in the required fiber by j≤n. This is a strict algebra morphism:
applying h to the coordinatewise union of a partial element of I gives the
same singleton and domain as `a∘L(h)`. Its successor equation is
`hγ(sφ)=Tγ(hγ(φ))`: at zero, sφ has true domain; at k+1 its domain is φ(k),
and increment sends j+k to j+k+1. Disabled values remain empty. Initiality
identifies h as the iteration map.

The same formula on F extends h. The preceding completeness proof makes
this extension unique. Evaluation at infinity, whose predicates are all
true, gives the specified graph, including bottom for disabled inputs.
This derivation neither equates I with an external natural-number chain nor
assumes uniqueness of arbitrary fixed points.

For n+d≤m, define H on partial certificates by v↦v+d, retaining traces.
It commutes with the union algebra and is therefore an algebra morphism;
it intertwines T with the target functional whose seed is j+d. Consequently
H∘h is the target iteration map by initiality. H composed with the source
extension is an extension of that map, so target completeness identifies it
with the target extension. Evaluation at the same infinity yields
`H(fix T)=fix T'`. This is the derivation from local iteration, strict-algebra,
extension and evaluation laws. No global selected-result equation was an
assumption. Taking (m,d)=(n+1,0), then (n+3,1) proves the two-change law.
Addition associativity proves equality with the composite on all partial
records, including empty ones.

Pure substitution is also supported. For any internal σ:Δ→Γ, the filter,
finite-bound reconstruction, union and displayed h formula substitute
pointwise. The dependent product over k is over the constant natural-number
index, so substitution commutes with its evaluation. The extension uniqueness
argument applies with Δ as parameter, proving the pulled extension is the
chosen extension. A second substitution τ gives the same formula as σ∘τ.
The A and B changes above additionally act on fibers; their non-surjectivity
is not hidden by calling them substitutions.

## Applicability, replacement and remaining boundaries

The two methods establish the same selected partial graph for this client.
Their premises differ: external bottom, chain suprema and continuity versus
internal dominance, algebra, completeness and internal morphisms. The
bound-filter proof discharges the extra dependent-family obligation on paper.
It is positive applicability evidence; absence of a Lean Eff implementation
is not an obstruction to the mathematics.

The larger hypothesis gap is precise. A different certificate family with
no demonstrated complete ambient object and stable filtering/retraction
cannot borrow this completeness argument. Nor does a bare fixed-point
existence theorem imply preservation of a selected solution. A proposed
internal provider must supply initiality, unique extension, algebra and
parameter compatibility. These are construction obligations, not a claim
that they are impossible. For example, merely knowing an unlifted object is
complete outside the hypotheses of Proposition 1.31 does not license the
complete-lift step above.

An SDT replacement could make its internal morphisms the native client maps
and select solutions by extension, eliminating per-client order-continuity
proofs in that setting. It would need the indicated lift, iteration and
complete-family constructions plus checked recovery of both existing
countdown clients. It would also change the admitted morphism class; this
report proves no equivalence with all classical external maps. Requiring
SDT to be an adapter into an ordered-domain API would obscure that independent
option. For the present bounded client the existing external API already
works, so no shared-interface migration is justified by missing capability.

[#289](https://github.com/VladimirMarko/conaled/issues/289), coordinated with
[#235](https://github.com/VladimirMarko/conaled/issues/235), #36 and #196,
owns any future extension/base-change interface. A useful trigger is a checked
internal provider or a client whose complete-family argument cannot reuse
this decidable filtering construction. The nonconstant client condition is
now met; its result is that selected transport alone still does not require
a new external interface. There is no measured author-productivity comparison.
The formal work added one client module and reused the existing solver;
the internal proof remains paper mathematics. #107 stays paused, #108
unselected and #260 inactive.

Implementation has since begun in [#371's checked assembly
prerequisites](internal-sdt-prerequisites.md): tracked maps, program-index
lifting, and proper certificate embeddings. The complete-family theorem and
internal selected-solution comparison remain unimplemented; that note records
their dependency graph.

## Undefinedness, fuel and statement review

A disabled coordinate has semantic result bottom. On an enabled coordinate,
fuel k or less also observes bottom, while the selected solution returns the
certificate. The checked finite-fuel example separates these cases. `bounded`
is a semantic approximation in the noncomputable `Part` model. No executable
evaluator, external language semantics or operational adequacy theorem is
claimed. An eventual evaluator needs its own semantics and adequacy statement.

Statement review checked all new claims against the independent recurrence:
validity does not include the selector; bound inequalities justify both
embeddings and increments; seed and capacity changes are quantified separately;
transport equality retains the entire certificate; the composite law holds
before solving; the negative controls use satisfiable inputs. `no_fixed_tags`
excludes equivalences, not arbitrary encodings with a retained predicate.
The external global theorem uses local strictness and intertwining, not the
explicit solution formula as a transport premise. The internal extension
argument applies to arbitrary parameter maps and preserves the bound in
its factorization; it does not infer slice completeness from global points.
