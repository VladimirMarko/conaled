# A proof-relevant bridge into the typed compiler

Issue [#203](https://github.com/VladimirMarko/conaled/issues/203) implements a
bounded Curry–Howard interface over the existing compiler. Its proof objects
retain inspectable syntax in `Type`; they support capture-avoiding substitution
and a one-step simulation of natural-deduction detours by compiler-term
reductions. This is an experimental author interface, with the same validation
standard as the rest of the integrated library.

## Mathematical choice

The fragment has one atomic proposition, truth, conjunction, and implication:

```
A, B ::= atom | truth | and A B | implies A B
Γ ::= [] | A :: Γ
Γ ⊢ A
```

One atom is a finite signature, mapped exactly to `CategoricalCompiler.Ty.base`.
This experiment does not encode several distinct atoms as the compiler's single
base type. Truth maps to unit, conjunction to product, and implication to arrow.
Contexts are lists; the newest assumption is at the head, and its semantic value
is the right component of the environment product. Typed de Bruijn variables
select hypotheses. Weakening, duplication, and exchange are permitted; this is
intuitionistic, non-linear natural deduction.

[Proofs and Types, §§3.4–3.6](https://paultaylor.eu/stable/prot.pdf) relates
conjunction and implication rules to typed lambda terms and identifies the
corresponding introduction/elimination contractions. We use those three
contractions, with compatible closure, and include truth. The book's normalization
results are not proved by this implementation.

[LF, introduction and §4](https://homepages.inf.ed.ac.uk/gdp/publications/Framework_Def_Log.pdf)
distinguishes a logic's judgments from the framework used to represent their
proofs, and makes substitution compatibility part of adequacy. Here Lean is the
host, and the object judgment is explicitly indexed by its context and formula.
This is not an LF implementation or an adequacy theorem for arbitrary logics.

## Shared representation and equality

[SquareKit/CurryHoward.lean](../../SquareKit/CurryHoward.lean) defines
`Proof Γ A` as a compiler `Term NoPrim (context Γ) A.type`, together with an
`Admissible` certificate. `Program` is deliberately an alias of this same type.
`toProgram` and `toProof` are identity functions; both round-trip theorems are
exact equality, proved by reflexivity. `typedCompilation` exposes the indexed
compiler term, so context and conclusion preservation are intrinsic in its type.
These identity translations are an interface choice, not evidence of a separately
proved bijection between independently defined syntaxes.

The proof rules have named constructors in the author interface:
`hyp`, `truth`, `andIntro`, `andLeft`, `andRight`, `impliesIntro`, and
`impliesElim`. The admissibility predicate permits exactly their underlying term
constructors. It checks lambda-domain types as well as the external formula
indices. Thus an unused sum-typed binder cannot silently extend the fragment.
`letE`, sums, case analysis, and primitives are not proof rules; `NoPrim` has no
inhabitants. The compiler still retains its broader syntax.

The term tree lives in `Type`; only its admissibility evidence lives in `Prop`.
Proof irrelevance identifies certificates for the same tree, without collapsing
different trees. The checked capture example distinguishes two proof objects by
their different returned values. Existing
[Internal.Derives](../../SquareKit/Internal/Logic.lean) is `Prop`-valued and remains
unchanged; we do not recover erased proof distinctions from it.

There is no alpha, beta, eta, or proof-equation quotient. De Bruijn indices avoid
binder names and therefore the need for alpha-renaming quotients. Beta and
projection contractions are directed steps, not definitional equality of term
trees. Semantic equality is separate from both syntactic equality and reduction.

## Substitution and operational contract

[STLCSubstitution](../../SquareKit/STLCSubstitution.lean) adds shared operations
to the existing `CategoricalCompiler.Term`, covering all its constructors:

| Declaration | Contract |
|---|---|
| `rename`, `liftRen` | Type-preserving renaming; the new binder stays fixed and older variables shift. |
| `subst`, `liftSub` | Simultaneous typed substitution; substitution images are weakened beneath binders. |
| `single` | Replace the newest hypothesis, leaving older variables as variables. |
| `eval_rename` | Evaluation agrees when environments agree on renamed variables. |
| `eval_subst` | Evaluation agrees when substitution images evaluate to the source environment's values. |
| `eval_single` | Evaluating a substituted body agrees with evaluating the body in the extended argument environment. |

These are operations on compiler syntax, not new logical rules for its extra
constructors. `Admissible.rename` and `Admissible.subst` prove closure of the
selected fragment. `Proof.cut` packages single substitution; `cut_compiles`
expresses exact syntactic substitution compatibility, and `cut_meaning` supplies
the semantic equation. The general substitution theorem's environment agreement
is an explicit hypothesis, not an implicit claim about arbitrary environments.

`Term.Step` has the contractions
`app (lam t) u → subst (single u) t`, `fst (pair t u) → t`, and
`snd (pair t u) → u`. It closes them through pairing, projections, abstraction,
and both arguments of application. It supplies no contraction or compatible
closure for the compiler's sum, case, primitive, or let constructors, and chooses
no evaluation strategy. `Detour` separately presents the matching proof-rule
contractions and closure. `detour_simulates` sends every proof detour to exactly
one `Term.Step`. `Step.sound` and `detour_meaning` then establish interpretation
preservation; they are not substitutes for the operational simulation.

The checked binder example substitutes a free `z` for `x` in `λy. x`. The result
is `λy. z`, with `z` still free: at `z = 7` and `y = 99` it returns 7. A deliberately
capturing alternative returns 99 and is proved different. A second example lifts
the entire detour under another abstraction, exercising compatible closure.

Operational reflection (the converse of `detour_simulates`), normalization,
confluence, substitution identity/composition laws, semantic completeness, and
full abstraction are outside this experiment. In particular, equal denotations
do not imply equal trees or a reduction path. There is no free-CCC theorem.

## Models, composition, and callers

[Examples/CurryHoward.lean](../../Examples/CurryHoward.lean) interprets the same
conjunction-swapping proof through two existing models: raw categorical code and
functions with `Nat` as the atom interpretation. `two_models` uses
`STLCNaturality.naturality` and the existing `soundMap` preservation package.
Raw code has category and closed laws under `CodeCategory.equiv meaning`, which
observes evaluation, not under equality of its syntax trees. Checked instances
reuse `CodeCategory.laws` and `CodeCategory.closedLaws`.

`composed` then uses `STLCNaturality.naturality_comp` to compose code interpretation
with `FunctionCategory.toTypes`. The final bundled-function adapter reuses the
existing `FullSourceNaturality.bundle`. It is a third representation of the
function interpretation, not a claim of a third distinct semantics.

This adapter uses the existing full-source `Target`/`Model` signature, whose sum
operations exceed what the proof fragment needs. The logic and its substitution
and reduction theorems have no backend-structure assumptions. The demonstrated
backend instances already provide the broader signature; this experiment does
not introduce or claim a minimal CCC-only compiler interface. Terminal, product,
and closed operations are the mathematical capabilities used by this fragment.
The checked identity-only category on `Ty` cannot even supply a `base → unit`
arrow, so it cannot interpret truth introduction with the stated object mapping.
This is a mathematical impossibility example, not a failed elaboration test.

The ordinary Lean client `ordinarySwap` remains polymorphic and uses ordinary
pairs. The opt-in author client `swap` uses named proof rules and one typed
hypothesis annotation. Binder examples still expose de Bruijn positions; those
positions and the annotation are current bookkeeping costs. Callers do not build
admissibility certificates, rename substitutions, or prove model-preservation
obligations anew. This low-level binder interface is not the intended final
surface language.

## Reuse and boundaries

The implementation reuses the compiler's types, variables, terms, evaluation,
categorical compilation, model preservation, and relation-based categorical laws.
It adds no emitter, parser, elaborator, universal AST, kernel axiom, or package.
The independent proof-tree datatype considered during design would duplicate
the compiler's binders and require an avoidable synchronization proof; the shared
representation leaves substitution closure, substitution meaning, and the
operational simulation as explicit substantive obligations.

This contributes an inspectable proof interface to
[#36](https://github.com/VladimirMarko/conaled/issues/36), and coordinates with
[#128](https://github.com/VladimirMarko/conaled/issues/128) through existing
compiler boundaries. Accepted [#140](https://github.com/VladimirMarko/conaled/issues/140) retains its
selected-witness and dependent-vector fixtures, and
[#147](https://github.com/VladimirMarko/conaled/issues/147) retains its bounded
elaboration contract. The present proof fragment neither replaces those
representations nor generalizes their acceptance results. This fragment does not make arbitrary Lean proofs
compilable through those paths.

A richer atom signature should wait for an explicit compiler object mapping that
keeps distinct atoms distinct. A better author surface should remove binder
indices while preserving the current substitution and reduction contracts.
Operational reflection or a normalizer would need new theorems and checked
counterexamples, rather than an inference from `Step.sound`. A minimal backend
adapter would be justified by an actual CCC-only target that cannot use the
existing full-source signature.

The public entrypoint imports the checked examples. Validation for a candidate
uses the repository's fresh `check.sh` compilation and transitive proof audit;
ordinary incremental example builds are development feedback, not the final
validation boundary.
