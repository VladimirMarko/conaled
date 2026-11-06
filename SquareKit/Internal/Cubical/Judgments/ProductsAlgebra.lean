import SquareKit.Internal.Cubical.Judgments.ProductsSyntax
import SquareKit.Internal.Cubical.Judgments.CoreTheory

/-! Π operation interpretation in the constructed presheaf model. Guards in the
source rules, rather than arbitrary semantic premises, ensure well-typed inputs. -/
namespace SquareKit.Cubical.Source.Products
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

noncomputable def extraOperation (op : Operation)
    (args : Fin (extraSignature.arity op) → Value.{u}) : Value.{u} :=
  match args ⟨0, by cases op <;> decide⟩ with
  | .family Γ A => match (args ⟨1, by cases op <;> decide⟩).familyAt (total A) with
    | some B => match op with
      | .pi => .family Γ (normalizedPi A B)
      | .lam => match (args 2).termAt (total A) B with
        | some b => .term Γ (normalizedPi A B) (normalizedLam b)
        | none => .invalid
      | .app => match (args 2).termAt Γ (normalizedPi A B) with
        | some p => .term (total A) B (normalizedApp p)
        | none => .invalid
    | none => .invalid
  | _ => .invalid

@[simp] theorem extra_pi (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)) :
    extraOperation .pi ![.family Γ A,.family (total A) B] = .family Γ (normalizedPi A B) := by
  change (match Value.familyAt (total A) (.family (total A) B) with
    | some B => Value.family Γ (normalizedPi A B)
    | none => .invalid) = _
  rw [Value.familyAt_family]

@[simp] theorem extra_lam (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)) (b : Presheaf.Term B) :
    extraOperation .lam ![.family Γ A,.family (total A) B,.term (total A) B b] =
      .term Γ (normalizedPi A B) (normalizedLam b) := by
  simp only [extraOperation]
  change (match Value.familyAt (total A) (.family (total A) B) with
    | some B' => match Value.termAt (total A) B' (.term (total A) B b) with
      | some b' => Value.term Γ (normalizedPi A B') (normalizedLam b')
      | none => .invalid
    | none => .invalid) = _
  simp only [Value.familyAt_family, Value.termAt_term]

@[simp] theorem extra_app (Γ : Context.{u}) (A : Family Γ) (B : Family (total A))
    (p : Presheaf.Term (normalizedPi A B)) :
    extraOperation .app ![.family Γ A,.family (total A) B,.term Γ (normalizedPi A B) p] =
      .term (total A) B (normalizedApp p) := by
  simp only [extraOperation]
  change (match Value.familyAt (total A) (.family (total A) B) with
    | some B' => match Value.termAt Γ (normalizedPi A B') (.term Γ (normalizedPi A B) p) with
      | some p' => Value.term (total A) B' (normalizedApp p')
      | none => .invalid
    | none => .invalid) = _
  simp only [Value.familyAt_family, Value.termAt_term]

noncomputable def algebra : Algebra signature where
  Carrier := Value.{u}
  operation
    | .inl op => Source.operation op
    | .inr op => extraOperation op
  predicate
    | .inl p => Source.predicate p
    | .inr p => nomatch p

@[simp] theorem lift_eval (Γ Δ : Context.{u}) (A : Family Γ) (σ : Δ ⟶ Γ) :
    (lift (.var 0) (.var 1) (.var 2) : Expression (Fin 3)).eval algebra
      ![.context Δ, .family Γ A, .substitution Δ Γ σ] =
        .substitution (total (reindex A σ)) (total A) (liftSub A σ) := by
  simp only [GuardedTheory.Term.eval, FinitaryTerm.fold, algebra, Source.operation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Value.familyAt_family, Value.substitutionAt_substitution]
  have ht : Value.termAt (Semantics.extend Δ (Semantics.subTy A σ))
      (Semantics.subTy A (Semantics.compSub σ (Semantics.weaken Δ (Semantics.subTy A σ))))
      (.term (Semantics.extend Δ (Semantics.subTy A σ))
        (Semantics.subTy (Semantics.subTy A σ) (Semantics.weaken Δ (Semantics.subTy A σ)))
        (Semantics.genericVariable Δ (Semantics.subTy A σ))) =
      some (Semantics.genericVariable Δ (Semantics.subTy A σ)) :=
    Value.termAt_term _ _ _
  rw [ht]
  rfl

end SquareKit.Cubical.Source.Products
