import SquareKit.Internal.Cubical.Judgments.NaturalsSyntax
import SquareKit.Internal.Cubical.Judgments.SumsTheory
import SquareKit.Internal.Cubical.Naturals

namespace SquareKit.Cubical.Source.Naturals
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

noncomputable def extraOperation (op : Operation)
    (args : Fin (extraSignature.arity op) → Value.{u}) : Value.{u} :=
  match args ⟨0, by cases op <;> decide⟩ with
  | .context Γ => match op with
    | .nat => .family Γ (natFamily Γ)
    | .zero => .term Γ (natFamily Γ) (natZero Γ)
    | .succ => match (args 1).termAt Γ (natFamily Γ) with
      | some n => .term Γ (natFamily Γ) (natSucc n)
      | none => .invalid
    | .elim => match (args 1).familyAt (total (natFamily Γ)) with
      | some B => match (args 2).termAt Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) with
        | some z => match (args 3).termAt (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) with
          | some s => .term (total (natFamily Γ)) B (natElim z (NatStep.ofTerm s))
          | none => .invalid
        | none => .invalid
      | none => .invalid
  | _ => .invalid

@[simp] theorem extra_nat (Γ : Context.{u}) :
    extraOperation .nat ![.context Γ] = .family Γ (natFamily Γ) := rfl

@[simp] theorem extra_zero (Γ : Context.{u}) :
    extraOperation .zero ![.context Γ] = .term Γ (natFamily Γ) (natZero Γ) := rfl

@[simp] theorem extra_succ (Γ : Context.{u}) (n : Presheaf.Term (natFamily Γ)) :
    extraOperation .succ ![.context Γ,.term Γ (natFamily Γ) n] =
      .term Γ (natFamily Γ) (natSucc n) := by
  change (match Value.termAt Γ (natFamily Γ) (.term Γ (natFamily Γ) n) with
    | some n => Value.term Γ (natFamily Γ) (natSucc n)
    | none => .invalid) = _
  rw [Value.termAt_term]

@[simp] theorem extra_elim (Γ : Context.{u}) (B : Family (total (natFamily Γ)))
    (z : Presheaf.Term (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ)))) (s : NatStepTerm B) :
    extraOperation .elim ![.context Γ,.family (total (natFamily Γ)) B,
      .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
      .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s] =
      .term (total (natFamily Γ)) B (natElim z (NatStep.ofTerm s)) := by
  change (match Value.familyAt (total (natFamily Γ)) (.family (total (natFamily Γ)) B) with
    | some B' => match Value.termAt Γ (reindex B' (Presheaf.pair (𝟙 Γ) (natZero Γ)))
        (.term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z) with
      | some z' => match Value.termAt (total B') (reindex B' (projection B' ≫ natSuccessorSub Γ))
          (.term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s) with
        | some s' => Value.term (total (natFamily Γ)) B' (natElim z' (NatStep.ofTerm s'))
        | none => .invalid
      | none => .invalid
    | none => .invalid) = _
  simp only [Value.familyAt_family,Value.termAt_term]

noncomputable def algebra : Algebra signature where
  Carrier := Value.{u}
  operation
    | .inl op => Sums.algebra.operation op
    | .inr op => extraOperation op
  predicate
    | .inl p => Sums.algebra.predicate p
    | .inr p => nomatch p

theorem zeroSub_eval {V : Type} (γ : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (hΓ : γ.eval algebra ρ = .context Γ) :
    (zeroSub γ).eval algebra ρ = .substitution Γ (total (natFamily Γ)) (Presheaf.pair (𝟙 Γ) (natZero Γ)) := by
  change Source.operation .pair ![extraOperation .nat ![γ.eval algebra ρ],
    Source.operation .id ![γ.eval algebra ρ],extraOperation .zero ![γ.eval algebra ρ]] = _
  rw [hΓ,extra_nat,extra_zero]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    Value.substitutionAt_substitution]
  have ht : Value.termAt Γ (Semantics.subTy (natFamily Γ) (Semantics.idSub Γ))
      (.term Γ (natFamily Γ) (natZero Γ)) = some (natZero Γ) := Value.termAt_term _ _ _
  rw [ht]

theorem successorSub_eval {V : Type} (γ : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (hΓ : γ.eval algebra ρ = .context Γ) :
    (successorSub γ).eval algebra ρ =
      .substitution (total (natFamily Γ)) (total (natFamily Γ)) (natSuccessorSub Γ) := by
  change Source.operation .pair ![extraOperation .nat ![γ.eval algebra ρ],
    Source.operation .weaken ![γ.eval algebra ρ,extraOperation .nat ![γ.eval algebra ρ]],
    extraOperation .succ ![Source.operation .extend ![γ.eval algebra ρ,extraOperation .nat ![γ.eval algebra ρ]],
      Source.operation .generic ![γ.eval algebra ρ,extraOperation .nat ![γ.eval algebra ρ]]]] = _
  rw [hΓ,extra_nat]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    Value.familyAt_family,Value.substitutionAt_substitution]
  have hs : extraOperation .succ ![.context (Semantics.extend Γ (natFamily Γ)),
      .term (Semantics.extend Γ (natFamily Γ))
        (Semantics.subTy (natFamily Γ) (Semantics.weaken Γ (natFamily Γ)))
        (Semantics.genericVariable Γ (natFamily Γ))] =
      .term (total (natFamily Γ)) (natFamily (total (natFamily Γ)))
        (natSucc (Presheaf.generic (natFamily Γ))) := extra_succ _ _
  rw [hs]
  have ht : Value.termAt (total (natFamily Γ))
      (Semantics.subTy (natFamily Γ) (Semantics.weaken Γ (natFamily Γ)))
      (.term (total (natFamily Γ)) (natFamily (total (natFamily Γ)))
        (natSucc (Presheaf.generic (natFamily Γ)))) = some (natSucc (Presheaf.generic (natFamily Γ))) := Value.termAt_term _ _ _
  rw [ht]
  rfl

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

end SquareKit.Cubical.Source.Naturals
