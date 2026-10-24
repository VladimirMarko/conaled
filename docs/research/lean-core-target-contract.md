# A bounded Lean core target for the graph proof

Design specification for [#114](https://github.com/VladimirMarko/conaled/issues/114),
2026-10-24, against local commit `c3b9cb62a89f23df20c4bfd808402ac9be1f1603`.
This develops [the self-modeling research](lean-self-modeling-and-reflection.md).
The [typed target and native denotation](graph-target-implementation.md) now
implement the first bounded experiment. Concrete Lean expression emission and
installed-environment correspondence remain unimplemented. The worked example
below records the design specification; the implementation note identifies
its checked target specializations.

## Consumer and generated artifact

Use the existing [`Graph.forward`, `Graph.backward`, and `Graph.inSet`](../../SquareKit/Internal/Graph.lean).
Their source judgments, in context `[input, output]`, are

```text
∃y:middle. y=f(x) ∧ z=g(y)  ⊢  z=g(f(x))
z=g(f(x))  ⊢  ∃y:middle. y=f(x) ∧ z=g(y).
```

The source is the equality-only sublanguage of
[`FormulaCore` and `Derives`](../../SquareKit/Internal/Logic.lean), with the
three distinct `GraphSort` sorts and two `Arrow` symbols. The model supplies
arbitrary `A B C : Type v`, `f : A → B`, and `g : B → C`; no inhabited-carrier
assumption is needed. `Graph.inSet` consumes `sound` for these two derivations.
The existing [`horizontal_comparison`](../../SquareKit/Internal/Squares.lean)
connects interpreted graph composition with square composition. This is an
existing consumer, independent of #107/#108's repair and fresh-theorem retest.

Propose a canonical translation of these source rule instances into two closed
Lean theorem declarations after abstracting their carrier, arrow, endpoint and
hypothesis parameters. The output is a proof term and its proposition in core
syntax. Runtime IR, code generation, proof erasure, executable performance and
native evaluation are outside this contract. Lean's
[processing pipeline](https://lean-lang.org/doc/reference/4.35.0/Elaboration-and-Compilation/)
distinguishes kernel checking from subsequent compilation.

Do not export the elaborated body of `Graph.inSet` as the initial backend.
That body references the generic syntax, its inductive recursors, `sound`,
substitution lemmas and their transitive dependencies. Our canonical translation
compiles the selected derivations directly. Its proposed dependency closure is
smaller, and must be measured on the actual emitted declarations before an
implementation claims coverage. The source proof remains available to ordinary
Lean clients; embedded Lean, slean and other possible surfaces can share this
backend only where their elaborations meet its stated source contract.

## Fragment K and its environment

K is a restricted, typed representation of a specified image in Lean core,
not a new definition of the whole kernel language. Its constructors carry
first-order sort and context information. Erasure produces `Lean.Expr` nodes;
a recognizer for arbitrary `Lean.Expr` is not required for this first step.
Keep the restricted representation and the installed Lean expression distinct.

For each chosen external universe parameter `v`, its admissible declarations
have the following inventory. The value of `v` is a parameter of the construction,
not an object-language quantifier over the host's whole universe hierarchy.

| Component | Admitted image and obligation |
|---|---|
| Data types and terms | Three carrier parameters `A B C : Type v`, variables, and applications of `f` and `g` with their declared domains. No type-valued source terms or quantification over all types inside formulas. |
| Propositions | `Eq` on a carrier, `And`, `Exists` over a carrier; implication and universal carrier quantification close sequents. Carrier and arrow parameters occur only in the declaration telescope. No arbitrary `Prop` parameter or impredicative propositional quantifier in source formulas. |
| Expressions | Bound variables, constants with explicit universe instances, application, lambda and dependent function binders. `Sort` occurs in telescope and primitive signatures. The image also admits `Expr.proj And 0` and `Expr.proj And 1` for conjunction elimination at K formulas. It contains no lets, metadata, free variables, metavariables, literals, arbitrary structure projections or unresolved names. |
| Proof operations | Identity and composition of implications; conjunction introduction/elimination; reflexivity, symmetry, transitivity and congruence of equality; existential introduction/elimination into propositions. These are typed schemas, instantiated only at K formulas and carriers. |
| Primitive environment E₀ | Fixed installed definitions of `Eq`, `Eq.refl`, the equality eliminator, `And` with its constructor/eliminator, and `Exists` with its constructor/eliminator. Helpers for symmetry/transitivity/congruence and projections have explicit checked bodies over these primitives. The implementation must list their exact installed names, universe parameters, types, bodies or recursor metadata, and dependency closure; this design does not assert that every helper already expands to a particular minimal constant list. |
| Environment extension | Start with E₀ and the abstract parameter telescope. Append only fresh theorem names whose type and body are generated together and checked in that environment. No arbitrary axioms, imported theorem bodies, new inductives, opaque semantic oracles, unsafe definitions or recursive definitions are admitted by the backend. |
| Conversion | Typed substitution and alpha-renaming; beta reduction, delta unfolding of the listed helpers, iota rules for the admitted recursors, and the two `And` projection reductions on `And.intro`. Support proof irrelevance at proposition types. Expand lets before emission. No reliance on arbitrary delta unfolding, quotient reduction, unrestricted inductive reduction or data eta is allowed. Any additional installed-kernel conversion used by a future emitter must be exposed and justified. |
| Universes | Carrier variables have sort `Sort (v+1)`; their binder types live in `Sort (v+2)`. Formula results live in `Sort 0`. Record primitive universe instantiations and the `imax` rule for dependent function formation, including propositions. Check level expressions against the declaration's parameter list; no cumulativity assumption. |

The conjunction projection forms were added to this inventory after the #125
emission experiment: on pinned Lean 4.35.0, expanding `And.left` and `And.right`
produces `Expr.proj And 0` and `Expr.proj And 1`, respectively. They implement
exactly K's `Code.left` and `Code.right` schemas. `GraphTarget.sound` interprets
those schemas by the native conjunction projections; `left_iota` and
`right_iota` compare the resulting native proofs after introduction. This
justifies the bounded choice of operations. These are proofs about K and its
native denotation, not a proved interpretation of `Lean.Expr.proj` or of kernel
conversion. The emitted projection reductions remain part of the tested/trusted
emission connection. No projection from an arbitrary structure, data product,
or other inductive type is admitted by this revision.

The implemented emitter constructs this image from typed K code and the pinned
helper bodies. Its final checks enforce closure, expected proposition structure,
primitive dependencies and kernel typing. They do not separately recognize the
admitted Expr constructors or prove grammar membership for an arbitrary input.
There is no arbitrary Expr import interface. A future importer or fragment
recognizer would need its own constructor checks and correctness contract.

Lean's actual expression datatype and kernel conversion support more than this
image. The pinned [expression source](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Expr.lean)
and [universe reference](https://lean-lang.org/doc/reference/4.35.0/The-Type-System/Universes/)
are the target interface. `Type v` is `Sort (v+1)`; universes are noncumulative,
and proposition-valued dependent functions use impredicativity. Our restriction
is on admitted instances, not a claim that the installed primitive declarations
lose their full polymorphic types.

E₀ is a semantic signature boundary: importing Lean's `Init` may expose many
more constants operationally, but the emitted dependency manifest must prohibit
references outside the declared closure. Validate that closure, not just the
surface identifiers. The repository's allowed axioms (`propext`,
`Classical.choice`, `Quot.sound`) remain the audit ceiling. This fragment's
mathematical proof uses none of those principles; a claim of an empty transitive
axiom list requires actual emission and audit. The #125 emitter measures empty
sets for both graph declarations; see [its implementation record](graph-emission-implementation.md).

## Six independent obligations

1. **Syntax.** Define the typed K representation, its contexts, capture-avoiding
   substitution, declaration telescope, and finite environment manifest. An AST
   without an interpretation is not a denotation.
2. **Declarative judgments.** Specify `E;Γ ⊢K t:A`, allowed environment extension
   and conversion. Primitive schemas have the interpretation just stated.
   Explicitly distinguish these restricted judgments from full Lean derivability.
3. **Checking.** If a checker is introduced, prove acceptance implies this
   judgment. Rejection or fuel exhaustion may be incomplete; neither may be
   treated as acceptance. Installed kernel acceptance alone does not establish
   that an artifact lies in K.
4. **Denotation.** Define carrier-term evaluation and formula satisfaction for
   the fixed signature and a model M. Prove admissible conversion preserves
   interpretation and that K proofs map satisfaction of their premise to their
   conclusion. State the environment interpretation as a premise until E₀'s
   schemas have been discharged.
5. **Emission.** Prove or validate a separate correspondence between K's
   declaration representation and the actual names, levels, binders, types and
   bodies sent to the pinned Lean kernel. Checking the wrong proposition proves
   nothing about the requested source sequent.
6. **Source preservation.** Translate source rules and prove the comparisons
   below, using existing `term_subst`, `formula_subst`, and `sound` where their
   types fit. A new backend should not force clients to reconstruct these laws.

Let `C` translate the specified source terms, formulas and derivations to K.
Let `J` interpret K in M, `I` be the existing source interpretation, and `ρ` be
an assignment to the source context. Context comparison identifies the same
ordered endpoints. The proposed square consists of

```text
Jterm(M, C(t), ρ) = Iterm(M, t, ρ)
Jformula(M, C(p), ρ) ↔ Iformula(M, p, ρ)
C(d) : C(p) → C(q), with Jproof(M, C(d), ρ) : Jformula(M,C(p),ρ) → Jformula(M,C(q),ρ).
```

For the proof comparison, if `a_p` and `a_q` are the two directions of the
formula equivalences in their appropriate domains, require pointwise agreement
of `a_q ∘ Jproof(C(d)) ∘ a_p` with `sound M d ρ`. This is equality of proofs of
the same proposition in Lean's proof-irrelevant Set interpretation. It does
not identify proof-relevant existential data, higher identities or arbitrary
model morphisms. Term equality and formula equivalence remain distinct claims;
`propext` is unnecessary for stating the latter.

Substitution must commute with C and the context assignment. This matters in
the existential case: a de Bruijn index shift error can produce a well-typed
proof of a different proposition. The graph example below fixes the binder
ordering, terms and observation instead of checking only successful elaboration.

## Worked source-to-target example

Interpret the source context `[input,output]` by `x:A, z:C`. Inside the
existential, `[middle,input,output]` is interpreted by `y:B, x:A, z:C`.
The source `body` becomes `y=f(x) ∧ z=g(y)`, `composite` becomes
`P := ∃y:B. y=f(x) ∧ z=g(y)`, and `result` becomes `Q := z=g(f(x))`.

A schematic core proof of the forward sequent is

```text
λ h:P.
  existsElim h (λ y:B. λ k:(y=f(x) ∧ z=g(y)).
    eqTrans (andRight k) (eqCongr g (andLeft k)))
```

Here `eqCongr g (andLeft k)` has type `g(y)=g(f(x))`, so transitivity with
`z=g(y)` has exactly the requested result. The target reverse proof is

```text
λ h:Q. existsIntro (f(x)) (andIntro (eqRefl (f(x))) h)
```

These helper names denote K's typed schemas, **not executable Lean code**.
Lowering them to the installed eliminators is the emission obligation. The
first term is the direct image of `Graph.forward`; the second performs the
cut and witness introduction of `Graph.backward`. Interpretation of the forward
term eliminates the existential into Q, retaining the arbitrary witness y until
equality transports `g(y)` to `g(f(x))`. Interpretation of the reverse term
chooses `f(x)`; it uses neither global choice nor an inhabitant of every B.
Thus both interpretations give the two implications already consumed by
`Graph.inSet`, and their formula observations are exactly P and Q.

For a concrete mathematical instance, take natural-number carriers,
`f(n)=n+1`, `g(n)=2*n`, and `x=2`. Both source and target formulas reduce to
`(∃y. y=3 ∧ z=2*y) ↔ z=6`; the reverse witness is 3. This design calculation now has a
[checked target specialization](../../Examples/GraphTarget.lean). It does not
require adding natural-number recursion to K: the external model supplies
the two functions. Empty carriers remain allowed: when A is empty there is no
assignment of x, and the universally closed judgment is vacuous.

## Fragment interpretation or relative model

The first implementation route should interpret only K. Fix M's carriers in
`Type v`; interpret data terms in those carriers and formulas in host `Prop`.
Prove validity by induction on the restricted proof rules. Its metatheory can
live at the host levels needed to package this fixed model. This interprets
instantiations of a finite signature; it does not decode every host type or
interpret every universe-polymorphic declaration in `Init`. Validating the
restricted uses of the primitives is enough for this route. Their full core
signatures and installed implementation remain in the emission/checking seam.

A second route can use a relative model for a larger declarative core. It needs
an environment accepted by that core, a model of its primitives and universe
structure, and a correspondence from K's declarations to that environment.
ConLeche's conditional set-theoretic model theorem is evidence for such a
route, with its actual assumptions recorded below. Satisfaction in that model
is not automatically the native host interpretation of A, B, C, Eq, or Exists:
provide a carrier/operation comparison and formula preservation before using
it in this square. A model-existence theorem alone does not provide this
comparison or an evaluator returning arbitrary native Lean types.

The routes can coexist. The fragment route has a smaller semantic obligation
and a more exposed installed-primitive seam. The relative route can cover more
core rules, at the cost of stronger model hypotheses, version adapters, and a
semantic comparison to the source. Neither is a mandatory predecessor of the
other or of surface-language work.

## Pinned upstream evidence

Inspected on 2026-10-24. These are source inspections of cloned upstream repositories, including proof bodies and build configuration. Neither project was built or independently axiom-audited in this investigation. An upstream axiom guard is evidence about its intended gate, not a locally reproduced audit. The earlier self-modeling note used moving branches; the revisions below fix this comparison.

| Project | Inspected revision | Toolchain and dependencies | License |
| --- | --- | --- | --- |
| Lean4Lean | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` | `leanprover/lean4:v4.33.0-rc2`; Batteries `76e1c118b0700b4ceafe99532e887d6431625e1a` | Apache-2.0 |
| ConLeche | `8e166ca53cd1f864b63c13cc1d326d38316d00ea` | `leanprover/lean4:v4.35.0`; empty Lake dependency manifest | Apache-2.0 |

Sources: [Lean4Lean toolchain](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/lean-toolchain), [manifest](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/lake-manifest.json), [license](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/LICENSE); [ConLeche toolchain](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/lean-toolchain), [manifest](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/lake-manifest.json), [license](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/LICENSE).

ConLeche's toolchain matches this repository's declared version; Lean4Lean's does not. Matching a version does not establish package compatibility or audit acceptance.

### Lean4Lean: syntax and checker contracts, with admitted gaps

Reusable vocabulary includes `Lean4Lean.VLevel`, `VExpr`, `VDecl`, `VEnv`, `VEnv.IsDefEq`, `VEnv.HasType`, `VEnv.IsType`, and `VEnv.IsDefEqU`. `HasType env U Γ e A` is reflexive typed definitional equality. `IsDefEq` includes variables, sort/constant level equivalence, application, lambda, dependent function formation with `imax`, conversion, beta, eta, proof irrelevance, and environment-supplied equality rules. Thus its core handles more than a simply typed lambda fragment. Source declarations and their universe parameters must be connected to the environment's constants and equations, rather than treating a bare expression as the entire target. [Typing definitions](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Theory/Typing/Basic.lean), [declarations](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Theory/VDecl.lean), [environment](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Theory/VEnv.lean).

Implementation correspondence is exposed through `Lean4Lean.TrEnv`, `VEnvs.WF`, `VEnvAt`, and expression translation relations. Theorems `Lean4Lean.TypeChecker.inferType.WF`, `checkType.WF`, `isDefEq.WF`, and `Methods.withFuel.WF` connect successful computations to these invariants. They do not supply an interpretation of the type theory in host mathematics. Fuelled correctness describes successful runs; it does not establish unrestricted termination or completeness. [Checker verification](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/TypeChecker.lean).

Concrete blockers to importing this verification as a completed, locally auditable proof:

- `Lean4Lean.VInductDecl.WF` and `VEnv.addInduct` are `sorry` definitions; `VEnv.addInduct_WF` is admitted. [Inductive definitions](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Theory/Inductive.lean), [preservation claim](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Theory/Typing/InductiveLemmas.lean).
- `Lean4Lean.AddInduct` has no constructors. The source explicitly explains that environments containing inductives are outside the verified `TrEnv` relation. `addDecl.WF` has a `sorry` in its inductive declaration branch. [Translation relation](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Environment/Basic.lean#L101-L112), [declaration theorem](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Environment.lean#L223-L235).
- `Lean4Lean.VEnv.IsDefEqU.sort_inv`, `forallE_inv_stratified`, and `sort_forallE_inv` are admitted. The proved wrapper `forallE_inv` calls the admitted stratified theorem. [Injectivity](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Theory/Typing/Injectivity.lean).
- Projection translation `TrProj` is a `sorry` definition, with further admitted projection and structural lemmas and checker cases. [Translation](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Typing/Expr.lean#L68), [inference](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/TypeChecker/InferType.lean#L391).
- `Verify/Axioms.lean` introduces non-foundational implementation assumptions, including `Std.TreeMap.all_eq_all_toList`, `Std.TreeMap.any_eq_any_toList`, `Lean.PersistentArray.toList'_push`, `Lean.PersistentHashMap.WF.toList'_insert`, `Lean.PersistentHashMap.WF.find?_eq`, `Lean.Level.normalize_eq`, and metadata/Boolean-equality assumptions. These are explicit axioms, not discharged proof obligations. This list identifies concrete examples and is not an exhaustive transitive axiom report. [Implementation axioms](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Verify/Axioms.lean).

The syntax and declarative rules are candidates for a narrow reuse investigation. A dependency decision needs a selected import closure, a port to Lean 4.35.0, and an axiom audit of the exact declarations used. Importing the entire verification tier would not meet this repository's present proof standard on the evidence above.

### ConLeche: relative semantic model

`ConLeche.Denotes cval env φ ρ e v` interprets checker expressions in sets: `φ` assigns natural numbers to universe parameters, `ρ` assigns sets to de Bruijn indices, and `cval` assigns meanings to constants at universe assignments. Its clauses cover bound variables, sorts, constants, application, lambda, dependent function types, lets, projections, and literals. There is no free-variable clause. `ConLeche.Denotes_functional` proves uniqueness when a denotation exists; it is not totality for arbitrary raw syntax. [Denotation relation and functionality](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Denotes.lean).

`ConLeche.Model V env` contains `cval`, a `mem` field interpreting every stored constant as a member of its interpreted type at every universe assignment, `false_empty`, and `eq_equality`. The last field makes the built-in equality denote set equality subject to the type and element membership premises. This public structure does not directly assert preservation of every unfolding or iota equation; accepted explicit equality theorems can provide the corresponding semantic equality. [Model fields](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Denotes.lean#L248-L270).

The exact principal theorem is `ConLeche.model_exists (V : Type w) [SetTheory V] (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env) (accepted : ConLeche.Cached.checkDecls .verified pins ds = .ok env) : Nonempty (Model V env)`. `ConLeche.no_False_declaration` retains `V` and `[SetTheory V]` and proves failure of the parser/preparation/checker chain for the specified `jsonWithTheoremFalse chunks` template. It is not a theorem about arbitrary installed Lean kernel acceptance or all possible file encodings. [Main theorems](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/MainTheorem.lean).

`ConLeche.SetTheory V` requires membership, extensionality, pairing, union, power set, regularity, replacement for arbitrary Lean functions `V → V`, and a natural-number-indexed chain of Grothendieck universes (`univChain`, `univChain_mem`, and universehood). These are hypothesis fields; the main theorem does not produce a `SetTheory` instance. The interpretation's object universe levels are natural-number syntax interpreted inside this stipulated set-theoretic hierarchy, not a universal evaluator into all native Lean universe levels. [SetTheory core](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/SetTheory/Core.lean).

The upstream `ConLecheTests.Axioms` file guards `#print axioms` for `model_exists`, `Denotes_functional`, `no_False_declaration`, and other capstones against precisely `propext`, `Classical.choice`, and `Quot.sound`. That gate would not erase the explicit `SetTheory V` hypothesis. It also does not by itself certify compiled behavior; the same source points to a separate runtime trust-surface check. The separate `ConLeche.Challenge` module deliberately admits its theorem statements with `sorry` for comparison tooling and is excluded from default build targets. No claim here is based on that challenge proof. [Axiom guard source](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/tests/ConLecheTests/Axioms.lean), [build targets](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/lakefile.toml).

For a commuting square, ConLeche supplies a candidate target denotation and accepted-environment model theorem. Remaining obligations are the compiler into its `Expr`/`Declaration` representation, the relationship between source model meanings and its set meanings, and correspondence with the actual Lean declarations emitted. Neither its main theorem nor Lean4Lean's translation relation establishes this repository-specific square or reflection back to the source. The public model theorem is useful evidence for relative semantics; it does not discharge a local compiler's preservation theorem.

## Reflection and universe limits

For a sufficiently strong effectively axiomatized theory T with diagonalization,
let `□` encode its provability. The Hilbert–Bernays–Löb conditions are external
necessitation (`T ⊢ φ` implies `T ⊢ □φ`), internal distribution over implication,
and `T ⊢ □φ → □□φ`. Löb gives: `T ⊢ □φ → φ` implies `T ⊢ φ`.
At falsehood this yields Gödel II's consistency obstruction for consistent T
under those hypotheses. Tarski's obstruction concerns a self-applicable truth
predicate with unrestricted disquotation. A satisfaction relation for a fixed
object language and model has a narrower domain.
[Bailitis, §§5.2 and 6](https://www.ps.uni-saarland.de/~bailitis/bachelor/Bailitis_thesis.pdf)

Our proposed validity induction quantifies over K derivations, not faithfully
encoded full Lean proofs. The relative route retains its model premise. Neither
requires unrestricted self-reflection. We have not established the derivability
conditions for an arithmetization of this repository's exact Lean theory, so
these general results constrain the design rather than constitute a local
formal impossibility theorem.

A finite file is not a bounded theory: it can import strong axioms, quantify
polymorphically and access the whole environment. K is bounded by its grammar,
allowed instances, model parameters and declaration closure, rather than line
count. One universe shift may suffice to package a particular interpretation;
it does not produce a universe containing all its own models or a truth predicate
for the entire host. Extending K with arbitrary inductives, impredicative
quantification or quotients requires new semantic obligations.

The [composition contracts](composable-setting-contracts.md) and their
[checked branching example](branching-graph-transport.md) keep forward transport
separate from reflection. A return from this Set-valued K interpretation to the
same source satisfaction uses the explicit formula equivalence above. It does
not recover derivability from validity in one model. A route through sheaves,
groupoids or internally formed settings must retain that route's observations,
universe parameters and comparison data. Finite route composition does not
supply a universal model or unrestricted return map. The target is one branch;
no sheaf-local witness, constructive witness type or higher identity may be
collapsed into this Set/Prop observation without a separate justified contract.

## Failure cases and trusted seam

- Reject a declaration referencing `Classical.choice`, a quotient eliminator,
  arbitrary recursive code or an unlisted axiom, even when Lean accepts it and
  the repository's broader axiom whitelist would allow it. Its interpretation
  has not been supplied for K.
- Reject unbound indices, unresolved metavariables, unexpected universe levels,
  mismatched environment fingerprints and unsupported conversion steps. Report
  the missing constructor, constant or semantic obligation.
- Existential elimination here targets a proposition. Extracting a witness from
  arbitrary `Exists` into data is outside the fragment. Higher-identity routes
  and computational Sigma witnesses need their own targets.
- A deliberately altered conclusion such as `z=f(x)` can be ill-typed, but with
  equal carriers a wrong conclusion might remain well-typed. Source/target
  comparison must catch it independently of kernel rejection.
- Accepting a serialized term in a different environment does not validate its
  original denotation. Bind the emitted artifact to toolchain, signature,
  primitive metadata and declared dependency closure.

Until a verified emitter and environment adapter exist, the implementation of
serialization, binder/level mapping and installed primitive identification is
trusted for correspondence. Kernel checking establishes the emitted theorem in
Lean; proof auditing bounds its transitive axiom dependencies. Neither proves
the emitter preserved the source statement, nor certifies the C++ kernel,
runtime/compiler, or filesystem/toolchain integrity. Round-trip structural
checks and negative fixtures reduce this seam empirically; label them as tests,
not as a formal refinement theorem.

## Bounded implementation follow-ups

These scopes are tracked by #124, #125 and #126 respectively. The first has a
[checked implementation](graph-target-implementation.md); the other two retain
their separate emission and relative-model contracts.

1. **Represent and interpret the graph core image.** Define typed K syntax,
   substitutions, restricted judgments and native Set denotation for the
   equality/conjunction/existential graph signature. Translate the existing
   forward/backward derivations and prove term/formula/substitution and proof
   comparisons above. Check distinct and coincident carriers and empty-carrier
   cases using existing graph proofs. Keep native clients unchanged. Acceptance
   excludes arbitrary core import, model-existence axioms and #107/#108's fresh
   theorem. Use statement review, checked specializations and the full audit.
2. **Emit and inspect graph proof declarations on Lean 4.35.0.** From that K,
   emit the two theorem declarations with an exact primitive/dependency manifest,
   explicit universe instances, and fresh names. Check them and compare emitted
   types structurally with independently constructed expected propositions.
   Audit transitive axioms. Include binder, level, unknown-constant and changed
   conclusion failures. Record which correspondence is proved and which is
   tested; kernel acceptance alone fails acceptance. This depends on experiment 1.
3. **Test one relative-model adapter.** Independently investigate the smallest
   environment translation mapping the same graph signature to the pinned
   Lean4Lean/ConLeche declarative language. Prove or expose the model assumption
   as a parameter, establish the formula comparison to a specified semantic
   carrier model, and identify every unsupported environment feature. First
   establish a compatible isolated build and an axiom inventory; do not add
   either project as a dependency merely because its source contains a theorem.
   No full-host reflection or general Lean importer is required.

A successful first experiment establishes a restricted interpretation. A
successful second adds concrete emitted artifacts with an explicit remaining
trust boundary. The third tests a different semantic route. Broader fragment
extensions should follow a consumer's demonstrated requirements.
