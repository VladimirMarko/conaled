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

end SquareKit.Cubical.Source.Sums
