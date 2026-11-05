# Primary-source preparation for issue 317

Read-only preparation, 2026-11-05. Scope: saved `specs/317.json` and `specs/orchestration.md`. Implementation remains blocked on reviewed #315. The example below is a proposed obligation map, not an adopted interface, checked formalization, or review of #317. No repository or tracker changes were made.

## Source facts and their limits

[Bauer–Haselwarter–Lumsdaine, *A general definition of dependent type theories*, v1](https://arxiv.org/html/2009.05539v1): Definitions 5.1/5.6/5.7 require a bijection between metavariables and object premises respecting scopes, classes and generic heads; derivable presuppositions of every premise and conclusion; and empty conclusion context. Definition 5.12 additionally requires one object rule per symbol and associated congruence rules (Definition 4.34). Definitions 6.16–6.20 require well-founded dependencies and presupposition derivations over preceding rules; Proposition 6.21 makes the resulting flattening acceptable. Theorem 5.15 requires weak presuppositivity; Theorem 5.22 requires substitutivity and congruity; Corollary 5.24 and Theorem 5.27 use acceptability for typing uniqueness and inversion. Inversion leaves equality derivations outstanding. Appendix A explicitly distinguishes formalized results from unformalized ones.

[Haselwarter–Bauer, *Finitary type theories with and without contexts*, v1](https://arxiv.org/html/2112.00539v1): Definition 2.18 requires derivable metavariable-context and conclusion-boundary judgments, with each rule checked over predecessors. Definition 2.20 additionally requires a unique symbol rule per symbol. Theorems 3.8, 3.13, and 3.17 address substitution and instantiation, including equality; Theorem 3.18 addresses presuppositions. Proposition 3.22 gives economical congruence under its finitary hypotheses. This is a related alternative presentation, not a theorem identifying arbitrary guarded Horn encodings with either framework.

## Concrete Σ presentation to check

Take a base with dependent contexts, substitution, judgmental equality/conversion, and **without** object-language Σ. Retain any Id structure required by the selected #315 fragment. Write `≡` for judgmental equality and `Id` for object-language identity. Ambient `Γ` below is schematic; internal rule templates have empty conclusion context and acquire `Γ` by instantiation.

| Addition | Ordered object premises and conclusion |
|---|---|
| Formation | `Γ ⊢ A type`; `Γ,x:A ⊢ B(x) type`; conclude `Γ ⊢ Σ(A,B) type`. |
| Introduction | Previous two premises; `Γ ⊢ a:A`; `Γ ⊢ b:B(a)`; conclude `Γ ⊢ pair(A,B,a,b):Σ(A,B)`. |
| Dependent elimination | `A`, `B` as above; `Γ,z:Σ(A,B) ⊢ C(z) type`; `Γ,x:A,y:B(x) ⊢ d(x,y):C(pair(A,B,x,y))`; `Γ ⊢ p:Σ(A,B)`; conclude `Γ ⊢ split(A,B,C,d,p):C(p)`. |
| β | Premises for `A,B,C,d,a,b`; conclude `split(A,B,C,d,pair(A,B,a,b)) ≡ d(a,b) : C(pair(A,B,a,b))`. |

This candidate has three new symbols. Their argument classes/binding counts are respectively `(Ty0,Ty1)`, `(Ty0,Ty1,Tm0,Tm0)`, and `(Ty0,Ty1,Ty1,Tm2,Tm0)`. Each listed object premise introduces exactly one metavariable with that scope and class. Keep explicit `A,B,C` arguments in this presentation; erasing them would require a separate adequacy argument.

To discharge presuppositions, derive `B(a)` by substitution, `C(pair(x,y))` using formation/introduction followed by substitution, and `C(p)` using the typing of `p`. For β, derive both terms at the displayed common type before adding their equation. A valid dependency order is base, formation, introduction, elimination, β, with the associated congruences available at each object-symbol stage. The two-variable branch context depends first on `A`, then on `B(x)`; treating it as an untyped list loses an obligation.

These are my proposed checks against BHL Definitions 5.1, 5.6, 6.16–6.20, not a claim that the emerging local representation satisfies them. In particular, generated congruence needs both well-formed argument instances and equalities in converted common contexts. A single untyped equality guard does not establish this.

## η and the distinction between operations and laws

For preparation, separate a β-only extension from an optional judgmental η extension:

```text
split(A,B, (z ↦ Σ(A,B)), ((x,y) ↦ pair(A,B,x,y)), p)
  ≡ p : Σ(A,B).
```

This η rule adds a law over the existing symbols, not a new operation. Both sides type-check using the earlier rules, so its boundary can be checked without assuming η. Do not claim the judgmental equation from β alone. If the base admits Id and reflexivity, Σ elimination with motive `Id(repack(z),z)` and reflexive branch gives a propositional η witness, because `repack(pair(x,y))` computes by β. That derivation does not establish judgmental η. #317 must explicitly select its contract after #315 is reviewed.

Projections can likewise be defined from dependent elimination. Their pair computations follow from β; the dependent second projection needs conversion using the first projection's computation. They need not become primitive symbols. In contrast, a chosen semantic eliminator's naturality or preservation is not supplied merely by naming these derived projections. Derive it from a stated uniqueness/universal property if available, or record it as an independent law on the chosen operation.

## Substitution, comparison, and type equations

For `σ:Δ→Γ`, the interpretation must validate the selected form of:

```text
Σ(A,B)[σ] ≡ Σ(A[σ], B[σ⁺])
pair(A,B,a,b)[σ] ≡ pair(A[σ],B[σ⁺],a[σ],b[σ])
split(A,B,C,d,p)[σ]
  ≡ split(A[σ],B[σ⁺],C[σΣ⁺],d[σ⁺⁺],p[σ]).
```

The first equation or its declared semantic comparison aligns the domains of the latter two. `σΣ⁺` lifts through the Σ extension; `σ⁺⁺` lifts through the two-entry branch telescope. The final terms must inhabit the aligned type `C(p)[σ]`. Identity/composition of these lifts and comparisons is part of the obligation, not just equality of final scalar observations. For model morphisms, the same issue arises with the transported motive and branch under the morphism's context/family comparison.

Raw-syntax substitution commuting with constructors can be definitional; admissibility on derivations is another claim; preservation by an interpretation is a third. A proposed Horn encoding needs a translation respecting binding, all four judgment forms, boundaries, congruence, conversion, substitution, and derivability before the cited metatheorems can be transferred. Alternatively prove the required local results directly and cite BHL only as the specification discipline.

[Lumsdaine–Warren, v2, Theorem 3.4.1, Definition 3.4.4.1 and Lemma 3.4.4.2](https://arxiv.org/html/1411.1736v2) provide a semantic route from full comprehension, LF, and appropriate weakly stable Σ structure to strictly stable structure in the split replacement. Their §4.1, Heuristic 4.1.1, expressly excludes general type-equality conclusions from the extension heuristic. It therefore cannot discharge an arbitrary type-equation admission obligation for #317.

## Two rejection tests and the eventual division of work

An ill-scoped eliminator that omits the `C` premise while using `C(p)` should fail the syntax/boundary check. A separate semantic test is the well-formed extra law `Σ(A,B) ≡ A`. Its endpoints can be formed and its rule can be placed after formation, yet in the ordinary family interpretation with `A` a singleton and `B` constantly a two-element set, the left side has two elements and the right side one. Even an equivalence interpretation cannot validate it. Thus a syntactically acceptable extension need not extend a designated model. This is an original candidate negative control, not a checked repository theorem.

The extension author should provide the finite rule boundaries, dependency derivations, congruence and η choice. The model builder should construct the Σ operations and prove β, the selected η, substitution, type-equation evidence, and morphism preservation. Ordinary proof authors should consume the resulting generic interpretation theorem without re-supplying those laws.

Adding η after β illustrates a potentially valid sequential extension of a presentation; extending a model through both stages additionally requires its η proof. Recovery of old derivations under reduct should be proved through the inclusion/interpretation construction. It is distinct from every old model admitting an expansion, conservativity of new equations over old syntax, and recovery of selected witnesses. No such stronger result, higher-model interpretation, or adoption decision follows from this preparation.

## Candidate infrastructure pointer, pending review

The unaccepted #315 candidate d9d994e contains `SquareKit/GuardedTheory/Extension.lean`. Its `Theory.extend`, `Derivation.inl`, `Model.restrictLeft`, `Term.eval_inl`, and `Atom.eval_inl` already implement signature inclusion and recovery under reduct for arbitrary guarded theories. Inspect the approved successor before implementation and reuse these mechanisms where applicable. They are not constructor admission proofs, all-model expansion, conservativity, or selected-witness recovery by themselves. Concrete constructor operation domains, rule validation, substitution and comparisons still need their own construction.
