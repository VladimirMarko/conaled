import SquareKit.Internal.Cubical.Judgments.SumsSyntax
import SquareKit.Internal.Cubical.Judgments.ProductsTheory
import SquareKit.Internal.Cubical.SumElimination

namespace SquareKit.Cubical.Source.Sums
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

noncomputable def extraOperation (op : Operation)
    (args : Fin 2 → Value.{u}) : Value.{u} :=
  match args 0 with
  | .family Γ A => match (args 1).familyAt (total A) with
    | some B => match op with
      | .sigma => .family Γ (Presheaf.sigma A B)
      | .pack => .substitution (total B) (total (Presheaf.sigma A B)) (sigmaPack A B)
      | .unpack => .substitution (total (Presheaf.sigma A B)) (total B) (sigmaUnpack A B)
    | none => .invalid
  | _ => .invalid

@[simp] theorem extra_sigma (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)) :
    extraOperation .sigma ![.family Γ A,.family (total A) B] =
      .family Γ (Presheaf.sigma A B) := by
  change (match Value.familyAt (total A) (.family (total A) B) with
    | some B => Value.family Γ (Presheaf.sigma A B)
    | none => .invalid) = _
  rw [Value.familyAt_family]

@[simp] theorem extra_pack (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)) :
    extraOperation .pack ![.family Γ A,.family (total A) B] =
      .substitution (total B) (total (Presheaf.sigma A B)) (sigmaPack A B) := by
  change (match Value.familyAt (total A) (.family (total A) B) with
    | some B => Value.substitution (total B) (total (Presheaf.sigma A B)) (sigmaPack A B)
    | none => .invalid) = _
  rw [Value.familyAt_family]

@[simp] theorem extra_unpack (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)) :
    extraOperation .unpack ![.family Γ A,.family (total A) B] =
      .substitution (total (Presheaf.sigma A B)) (total B) (sigmaUnpack A B) := by
  change (match Value.familyAt (total A) (.family (total A) B) with
    | some B => Value.substitution (total (Presheaf.sigma A B)) (total B) (sigmaUnpack A B)
    | none => .invalid) = _
  rw [Value.familyAt_family]

noncomputable def algebra : Algebra signature where
  Carrier := Value.{u}
  operation
    | .inl op => Products.algebra.operation op
    | .inr op => extraOperation op
  predicate
    | .inl p => Products.algebra.predicate p
    | .inr p => nomatch p

theorem formationSchema_valid (out : Judgment (Fin 3))
    (valid : ∀ (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)),
      out.eval algebra ![.context Γ,.family Γ A,.family (total A) B]) :
    Satisfies algebra.{u} (formationSchema out) := by
  intro ρ h
  have hp : ∀ i, (Products.formationRule.premise i).eval Products.algebra ρ := by
    intro i
    simpa only [formationSchema, Atom.eval_inl, algebra, Algebra.restrictLeft, Products.algebra] using h i
  rcases Products.formationSchema_inputs _ ρ hp with ⟨Γ,A,B,rfl⟩
  exact valid Γ A B

theorem substitutionSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ),
      out.eval algebra ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (substitutionSchema out) := by
  intro ρ h
  have hp : ∀ i, (Products.piSubRule.premise i).eval Products.algebra ρ := by
    intro i
    simpa only [substitutionSchema, Atom.eval_inl, algebra, Algebra.restrictLeft,
      Products.algebra] using h i
  rcases Products.substitutionSchema_inputs _ ρ hp with ⟨Γ,Δ,A,B,σ,rfl⟩
  exact valid Γ Δ A B σ

theorem lifted_eval (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ) :
    lifted.eval algebra ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ] =
      .substitution (total (reindex A σ)) (total A) (liftSub A σ) := by
  simp only [lifted, GuardedTheory.Term.eval_inl, algebra, Algebra.restrictLeft, Products.algebra]
  exact Products.lift_eval Γ Δ A σ

theorem eliminationSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ : Context.{u}) (A : Family Γ) (B : Family (total A))
      (C : Family (total (Presheaf.sigma A B))) (b : Presheaf.Term (reindex C (sigmaPack A B))),
      out.eval algebra ![.context Γ,.family Γ A,.family (total A) B,
        .family (total (Presheaf.sigma A B)) C,.term (total B) (reindex C (sigmaPack A B)) b]) :
    Satisfies algebra.{u} (eliminationSchema out) := by
  intro ρ h
  have hf : ∀ i, (Products.formationRule.premise i).eval Products.algebra (fun j => ρ (j.castAdd 2)) := by
    intro i
    fin_cases i
    · exact h 0
    · exact h 1
  rcases Products.formationSchema_inputs _ _ hf with ⟨Γ,A,B,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hA : ρ 1 = .family Γ A := congrFun e 1
  have hB : ρ 2 = .family (total A) B := congrFun e 2
  have hc := h 2
  change ∃ Δ C, Source.operation .extend ![ρ 0,extraOperation .sigma ![ρ 1,ρ 2]] = .context Δ ∧ ρ 3 = .family Δ C at hc
  rw [hΓ,hA,hB,extra_sigma] at hc
  simp only [Source.operation, Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at hc
  rcases hc with ⟨Δ,C,eΔ,hC⟩
  have he := Value.context.inj eΔ
  subst Δ
  have hb := h 3
  change Source.predicate .term ![Source.operation .extend ![Source.operation .extend ![ρ 0,ρ 1],ρ 2],
    Source.operation .subTy ![ρ 3,extraOperation .pack ![ρ 1,ρ 2]],ρ 4] at hb
  rw [hΓ,hA,hB,hC,extra_pack] at hb
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at hb
  obtain ⟨b,hb⟩ := Value.term_input (total B) (reindex C (sigmaPack A B)) (ρ 4) hb
  have he : ρ = ![.context Γ,.family Γ A,.family (total A) B,
      .family (total (Presheaf.sigma A B)) C,.term (total B) (reindex C (sigmaPack A B)) b] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hB | exact hC | exact hb
  subst ρ
  exact valid Γ A B C b

theorem lift_eval {V : Type} (δ a τ : Expression V) (ρ : V → Value.{u})
    (Γ Δ : Context.{u}) (A : Family Γ) (σ : Δ ⟶ Γ)
    (hΔ : δ.eval algebra ρ = .context Δ) (hA : a.eval algebra ρ = .family Γ A)
    (hσ : τ.eval algebra ρ = .substitution Δ Γ σ) :
    (lift δ a τ).eval algebra ρ = .substitution (total (reindex A σ)) (total A) (liftSub A σ) := by
  change Source.operation .pair ![a.eval algebra ρ,
    Source.operation .comp ![τ.eval algebra ρ,
      Source.operation .weaken ![δ.eval algebra ρ,Source.operation .subTy ![a.eval algebra ρ,τ.eval algebra ρ]]],
    Source.operation .generic ![δ.eval algebra ρ,Source.operation .subTy ![a.eval algebra ρ,τ.eval algebra ρ]]] = _
  rw [hΔ,hA,hσ]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Value.familyAt_family,Value.substitutionAt_substitution]
  have ht : Value.termAt (total (reindex A σ))
      (Semantics.subTy A (Semantics.compSub σ (Semantics.weaken Δ (Semantics.subTy A σ))))
      (.term (total (reindex A σ)) (reindex (reindex A σ) (projection (reindex A σ)))
        (Presheaf.generic (reindex A σ))) = some (Presheaf.generic (reindex A σ)) := Value.termAt_term _ _ _
  rw [ht]
  rfl


end SquareKit.Cubical.Source.Sums
