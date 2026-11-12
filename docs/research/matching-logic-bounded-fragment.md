# A bounded matching-logic study

Issue [#439](https://github.com/VladimirMarko/conaled/issues/439), inspected at
`f1f3918744183526b48806be93bbfd0949583be7` on 2026-11-12.

A small sorted matching-logic implementation is worth testing for symbolic
possible-outcome specifications. The concrete task proposed here is to check
substitution and a one-step configuration calculation, including a case where
unrestricted substitution fails. This is a recommendation for a separate
bounded implementation, not adoption of a shared language or proof interface.
The derivations below are handwritten mathematics; this report adds no Lean
results and makes no measured author-productivity claim.

## Source and scope

The primary reference is Grigore Roșu, *Matching Logic*, LMCS 13(4:28), published
2017-12-20, [journal record](https://lmcs.episciences.org/4153),
[61-page journal PDF](https://lmcs.episciences.org/4153/pdf), DOI
`10.23638/LMCS-13(4:28)2017`. The retrieved PDF has SHA-256
`d32b87b3c0354aa31bf9c6388185f1e7a49edf77cd5ddacb810bee2886f296a3`.
The author-hosted 65-page draft was not used as the reference version.

Source anchors: Definition 2.1 supplies sorted syntax; Definitions 2.2–2.3
supply nonempty carriers and powerset interpretation. Assumption 5.1 and
§§5.1–5.3 supply definedness, equality and membership. Corollary 5.23 covers
term substitution. Figure 5, printed p.53, gives the inference system;
Theorem 11.2, p.55, proves its soundness and completeness. Its equality and
substitution rules require the stated definedness infrastructure and freshness
conventions. Proposition 10.1, p.51, gives the predicate-logic translation.
We select sound rules from this presentation; neither completeness of the
selected subsystem nor any later matching μ-logic result is claimed.

The rest of the report constructs a local client and derives its contracts.
It does not formalize the paper's separation-logic examples, fixed points,
rewriting reachability, a K backend, or an automatic prover.

## Client meaning before patterns

Let configurations be the disjoint union
`Cfg = {run(n) | n ∈ ℕ} + {done(n) | n ∈ ℕ}`. Define a labelled relation:

- `keepA`: `run(n)` goes to `done(n)`;
- `keepB`: `run(n)` goes to `done(n)`;
- `bump`: `run(n)` goes to `done(n+1)`.

There are no outgoing steps from `done(n)`. Labels are data, not proofs of a
proposition. This deliberately small specification allows both a change of
value and distinct derivations with the same outcome.

The primary observation contract forgets labels:

```
R(c,d)       := there exists a label giving the specified step from c to d
Out(c)       := {d | R(c,d)}
Post(A)      := {d | there exists c ∈ A with R(c,d)}
Safe(c,B)    := Out(c) ⊆ B
```

Thus `Out(run(n)) = {done(n), done(n+1)}` and `Out(done(n)) = ∅`.
The concrete obligations are exact possible outcomes, exclusion of
`done(n+2)`, and the empty terminal fiber. Safety alone could conceal a missing
outcome; exact equality is deliberately part of this contract. An optional
trace consumer additionally asks which of `keepA` and `keepB` produced
`done(n)`. That is a different observation and is treated separately below.

## Frozen sorted fragment and model

Use sorts `N` and `C`, carriers `M_N = ℕ`, `M_C = Cfg`, and countably many
variables of each sort. A valuation assigns one carrier element to each
variable. Both carriers are nonempty. The symbol signature is:

| Symbol | Sort | Interpretation on elements |
|---|---|---|
| `zero` | `N` | `{0}` |
| `succ` | `N → N` | `n ↦ {n+1}` |
| `run`, `done` | `N → C` | singleton configuration constructor |
| `step` | `C → C` | `c ↦ Out(c)` |
| `δ_s^t`, for `s,t ∈ {N,C}` | `s → t` | `a ↦ M_t` |

The constructors are injective and disjoint in this particular model. Those
properties are not consequences of arbitrary matching-logic signatures.
`step` is neither total as an element-valued function nor functional in the
matching-logic sense. Its union extension is precisely `Post`.

Patterns contain sorted variables, these symbol applications, negation,
conjunction, and existential binding of a variable of either sort. The body
and result of a binder have the same sort; the bound variable may have another
sort. No untyped application or implicit coercion is allowed. Disjunction,
implication, equivalence, universal quantification, top and bottom are Boolean
abbreviations, not additional primitives. No least/greatest fixed points,
reachability modality, probability, resource connective or higher identity
constructor is included.

Here is the entire interpretation recipe for this local model. Write
`Eρ(p) ⊆ M_s` for a pattern of sort `s`:

```
Eρ(x)           = {ρ(x)}
Eρ(σ(p₁,…,pₖ)) = ⋃ {σ_M(a₁,…,aₖ) | aᵢ ∈ Eρ(pᵢ) for every i}
Eρ(¬p)          = M_s \ Eρ(p)
Eρ(p ∧ q)       = Eρ(p) ∩ Eρ(q)
Eρ(∃x.p)        = ⋃ {E(ρ[a/x])(p) | a ∈ M_sort(x)}
```

In particular, `Eρ(step(run(x))) = {done(ρx),done(ρx+1)}` by two union
calculations. Applying `step` again gives the empty set. The symbolic pattern
`∃x:N. step(run(x))` denotes exactly all terminal configurations: every output
is terminal, and `done(n)` is produced from `run(n)`. These are sets of
configurations, usually neither empty nor the entire `C` carrier. Restricting
all patterns to truth-valued predicates would lose this use of symbol inputs.

For this model, define `ceil_s^t(p) := δ_s^t(p)` and
`floor_s^t(p) := ¬ceil_s^t(¬p)`. The first is `M_t` exactly when `Eρ(p)` is
nonempty; the second is `M_t` exactly when `Eρ(p)=M_s`; otherwise each is empty.
The element interpretation of `δ` proves the required variable-definedness
axioms, rather than assuming a conclusion about arbitrary pattern values.
Define whole-pattern equality
`Eq_s^t(p,q) := floor_s^t(p ↔ q)` and membership
`Mem_s^t(x,p) := ceil_s^t(x ∧ p)`. They denote `M_t` exactly when respectively
`Eρ(p)=Eρ(q)` and `ρx ∈ Eρ(p)`. They are not selected equality proofs or selected
matches. Pointwise equivalence `p ↔ q` itself can be a proper subset; it must
not be confused with the predicate `Eq`.

Validity in this model means `Eρ(p)=M_s` for every valuation. A specification
axiom is required to hold for every valuation, not just under one assignment.
Consequently generalization below concerns globally valid premises. For local
hypotheses, its familiar no-free-variable-in-hypotheses condition is necessary.

## Substitution, sound rules, and an inference

All substitution is sorted and capture avoiding. Bound variables are renamed
fresh before substitution; this requires fresh names in the appropriate sort.
For `q` of the sort of `x`, if `Eρ(q)={a}`, the substitution equation is

```
Eρ(p[q/x]) = E(ρ[a/x])(p).
```

A structural proof handles a variable by singleton equality, an application
by replacing each argument set, and negation/conjunction by equality of their
operand sets. At `∃z.p`, after making `z` distinct from `x` and absent from
`FV(q)`, the interpretation of `q` is unchanged under `ρ[b/z]`; apply the
induction hypothesis for each `b`, commute the two distinct updates, and take
the union. A binder for `x` blocks substitution and its bound interpretation
is independent of the external assignment to `x`. The same induction proves
valuation agreement on free variables, used in the freshness step.

This proves variable substitution without an extra premise, since a variable
always denotes a singleton. For an arbitrary pattern it proves only the
conditional equation. Set-valued substitution is not evaluation at an element
chosen silently from that set.

The selected rules are propositional tautologies and modus ponens,
universal generalization, Functional Substitution, Equality Introduction and
Equality Elimination from Figure 5. Their local soundness follows as follows:

- At each carrier element the Boolean operations obey classical truth tables.
  If `Eρ(p)` and `Eρ(p → q)` are both the full carrier, so is `Eρ(q)`.
- Intersecting full carriers over all assignments to `x` proves generalization.
- For Functional Substitution, the antecedent
  `(∀x.p) ∧ (∃y.Eq(q,y))`, with `y` fresh for `q`, is empty unless `q` denotes
  a singleton. If it does, the preceding substitution equation and inclusion
  of an intersection in its `a` component prove the implication.
- Reflexivity of set equality proves Equality Introduction. For Equality
  Elimination, if the two substituted patterns have equal sets, structural
  congruence makes the two contexts equal. Under binders choose their bound
  names fresh for both replacements, so the equality remains valid under the
  bound-variable updates. No singleton assumption is needed for this
  congruence argument. The equality guard handles valuations where they differ.

These are local semantic derivations of selected published rules, not a
machine-checked reconstruction of Theorem 11.2. To make the rule use explicit,
let `A(x)` abbreviate the `C`-sorted equality

```
Eq_C^C(step(run(x)), done(x) ∨ done(succ(x))).
```

Take a specification `F` containing `A(x)` and the functionality axiom
`∃z:N. Eq_N^C(zero,z)`. Both are validated by the independent model above.
The following derivation uses the selected rules, not a completeness oracle:

1. From the specification axiom `A(x)`, generalization yields `∀x:N.A(x)`.
2. Functional Substitution with `q=zero`, together with the functionality
   axiom and propositional modus ponens, yields `A(zero)`.
3. Put `Q = done(zero) ∨ done(succ(zero))` and `T = step(run(zero))`.
   Equality Introduction yields `Eq_C^C(T,T)`. Equality Elimination in the
   context `Eq_C^C(h,T)`, with fresh `h:C`, and `A(zero)=Eq_C^C(T,Q)` yields
   `Eq_C^C(Q,T)` by propositional modus ponens.

The conclusion denotes the full `C` carrier because both sides denote exactly
`{done(0),done(1)}`. Membership in this set excludes `done(2)` by constructor
injectivity and arithmetic. This last exclusion is a native set calculation;
it is not claimed to have a derivation from `F` alone, which contains no
constructor-disjointness or arithmetic axiom scheme. Similarly, the terminal
empty-fiber and existential calculations above are local model theorems,
not consequences claimed of that small specification in every model.

A rejecting instance uses the same model. `∀x:C.∃y:C.Eq_C^C(x,y)` is valid:
for every element choose that same element. Substitute `T` for `x` while
omitting the functionality premise. The proposed conclusion
`∃y:C.Eq_C^C(T,y)` is empty because `{done(0),done(1)}` is not a singleton.
This specializes the paper's substitution obstruction to the client.
Definedness alone would not repair the rule: `T` is nonempty. Nor does treating
`step(done(0))` as a term work; its empty interpretation is also not a singleton.

## The same observations in native and existing interfaces

The comparison keeps `Out`, `Safe` and the optional labelled observation fixed.
A proof that merely preserves some possible outcome does not meet exact `Out`.

| Route | Construction for this client | Reuse and remaining work |
|---|---|---|
| Native relations and sets | Define `R`; prove `Out(run(n))` by cases; define `Post` by existential composition. | Lean's sets, inductive configurations and arithmetic directly express the contract. No syntax or substitution infrastructure is needed for this client alone. |
| Sorted matching patterns | Represent the symbolic family `step(run(x))` and use a shared evaluation/substitution theorem across nested patterns. | Adds reusable binder and inference reasoning. Requires syntax, environments, freshness, definedness and rule proofs. Does not add outcomes inexpressible in native Lean. |
| Relational semantic boundary | Instantiate `RelRep` with representations `Cfg`, meanings `Cfg`, relation `R`; `possibilities` decodes to `Out`. | Existing whole-fiber equality and `client_invariant` support clients invariant under identical outcome sets. A forward simulation does not supply an exact `PossibilityMap`. |
| Institution capabilities | Translate a pattern judgment to its native set judgment, carrying its valuation and observed configuration. | `Connection` composes supplied evidence maps; `Reflects` additionally gives satisfaction equivalence. It supplies neither pattern substitution nor a proof of the translation. |

For a concrete optional institution comparison, fix this model and use source
sentences `(ρ,p,d)` with evidence `PLift (d ∈ Eρ(p))`; target sentences are
native propositions with evidence `PLift`. Both model types can be `Unit`.
Translate to the native membership proposition and use the same proof in both
directions. For safety sentences use `PLift (Eρ(p) ⊆ B)` on both sides instead.
This is a proposed instantiation, not new checked code. Its translation is
intentionally transparent: it preserves the exact chosen observation but does
not perform symbolic reasoning. Extending it to varying signatures/models
would need additional data; it is not required for this experiment.

The existing code inspected is
[`RelationalSemanticBoundary.lean`](../../SquareKit/RelationalSemanticBoundary.lean)
(`possibilities`, `client_invariant`, `PossibilityMap`, `selectedMap_meaning`)
and [`Capabilities.lean`](../../SquareKit/Institutions/Capabilities.lean)
(`Connection.comp`, `Connection.satisfaction`, `Proofs`, `ProofMap`,
`RealizationMap`). These checked declarations predate this study; no fresh
build or audit is asserted here. `ProofMap` can transport a supplied syntax of
proofs with an interpretation law, but inhabitation reflection alone cannot
recover a selected proof. A proposed interface should not be credited with
this additional capability before its map is constructed.

There is a separate transport trap even with native sets. Under the map
`{a,b} → {*} ` identifying both points, the direct images of `{a}` and its
complement `{b}` are both `{*}`. The complement of the first image is empty.
Thus forward image does not preserve negation. A whole-logic translation
requires constructor-specific compatibility, or an appropriate inverse-image
contract, rather than a forward relational simulation alone. This agrees
with the warning in
[external computational semantics](external-computational-semantics.md#matching-logic-and-equational-specifications).
The existing [relational/selected boundary study](relational-and-selected-path-boundaries.md)
provides related checked controls; it is not a matching-logic implementation.

## Membership versus selected derivations

For a trace consumer define the data type
`Trace(c,d) := {label // the specified labelled step holds from c to d}`.
There is an explicit forgetful map
`Trace(c,d) → R(c,d)` sending a label and its correctness proof to existential
membership, and therefore to `d ∈ Out(c)`. At `(run(n),done(n))`, `keepA` and
`keepB` are distinct inhabitants with identical images. No inverse of this
forgetful map can recover both originals: applying such an inverse to their
equal images would equate their distinct labels.

A selector can choose `keepA` for that output and `bump` for `done(n+1)`.
This gives a chosen witness for each inhabited fiber in this model; it does
not reconstruct a previously selected trace. It also illustrates why saying
that membership can never yield any witness would be too strong.
If selected traces are part of a transport contract, carry `(d,label,proof)`
and require equality of the observed label as well as preservation of output.
Forgetting this enrichment recovers the possible-outcome contract. With
`Relational.SemanticBoundary`, put `(d,label)` in the semantic carrier and use
a relation enforcing the labelled step. Its selected-witness operations then
preserve that semantic pair. The plain `Cfg` semantic carrier does not retain
labels just because the API uses the word `Selected`.

The original safety client intentionally forgets labels. It needs no enriched
bridge or maximum witness retention. All these equalities concern sets,
configurations or explicit label data, not proof identity or homotopy paths.

## Bounded implementation recommendation and obligations

Recommend one bounded task: **implement the two-sort configuration fragment,
prove evaluation/substitution and selected-rule soundness, then check both
outcome and trace controls above**. This gives the project a concrete symbolic
specification client and a reusable substitution proof; it does not warrant a
universal AST, compiler registration requirement, framework migration or a
claim that matching logic replaces native Lean.

Proposed declarations, scoped to this experiment:

1. `Sort`, context-indexed `Var`, `Symbol`, `Pattern`, `Model`, `Valuation`,
   `eval`, `rename` and capture-avoiding `subst`. Use typed de Bruijn variables
   or an equivalent context-indexed representation so binding obligations are
   explicit. Keep the signature fixed initially; make carrier universes
   explicit, e.g. `Carrier : Sort → Type u`, `eval : Set (Carrier s)`.
2. `eval_rename`, valuation agreement, and `eval_subst_singleton` with its
   exact functionality hypothesis. Define `ceil`, `floor`, `patternEq`,
   `membership`, `Valid`; prove their interpretation equations from the
   definedness-symbol law.
3. A derivation datatype for the selected rules and specification axioms,
   with `Derives.sound`. Include the global validity convention or explicit
   generalization side condition. Formalize the numbered inference as a
   derivation value, not just an independently proved semantic conclusion.
4. Independent `Cfg`, `Label`, labelled step, `Out` and `Post`; interpret the
   syntax in this model. Check exact outcomes for arbitrary `n`, the terminal
   empty case, the existential terminal family, exclusion of `done(n+2)`,
   valid functional substitution and failed unrestricted substitution.
5. `Trace.forget`, its concrete noninjectivity, the explicit selector, and
   the enriched `(output,label)` relation. Compare native and pattern safety
   for the same `B`; optionally instantiate the existing relational boundary.
   The institution wrapper above is optional, not an admission gate.

Source adequacy requires a sort-preserving embedding of the chosen syntax
and rules into the 2017 presentation on paper, checked semantic equations,
and an account of binding convention changes. It must distinguish global
specification validity from valuation-local assumptions and avoid claiming
completeness for the rule subset. The proposed singleton-substitution theorem
must include negation and a genuinely bound-variable example, not only closed
terms. Reject an implementation that calls `step` functional, replaces whole
pattern equality by overlap, or validates only a finite Boolean fixture.

Native carrier sets may be infinite, and classical set semantics need not be
executable. Concrete single-step outcomes and the selector are computable;
this does not imply decision procedures for quantified patterns, witness
extraction from arbitrary propositions, proof search, termination of a
rewriting engine, or physical execution. No new kernel axioms are proposed.
No quantitative effort comparison has been performed. If this task finds
that no second symbolic specification reuses the binder/rule machinery, retain
the native relation client and reassess generalization before expanding the
syntax. The benefit to test is shared proof work, not shorter notation alone.

Remaining owners: the next implementation author owns the declarations,
source adequacy, EDD specializations and statement review; its coordinator owns
README-prescribed build/audit and independent Standards/Spec acceptance.
The current research coordinator owns independent review and publication of
this report. Any later common-interface proposal belongs in #235/#288 with
concrete clients and preservation requirements, rather than being adopted by
this study.
