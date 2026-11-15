import SquareKit.Internal.Cubical.Judgments.ProductsTheory
import Examples.CubicalConversion

/-! Source derivations, rather than direct semantic rules, retain dependent
function computation and literal conversion under a nonidentity substitution. -/
namespace Examples.CubicalSourceProducts
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Source SquareKit.GuardedTheory
open SquareKit.Cubical.Source.Products
open Examples.CubicalConversion Examples.CubicalPresheaf
set_option backward.isDefEq.respectTransparency false

/-- An annotation-free derivation with schematic Γ,A,B,b. -/
def betaSource : Derivation theory (List.ofFn betaRule.premise) betaRule.conclusion := by
  have d := Derivation.rule (T := theory) (.inr .beta) SquareKit.GuardedTheory.Term.var
    (fun i => Derivation.hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory, Theory.extend, Products.rule, Atom.subst_id] using d

/-- The same source tree can be interpreted at every dependent presheaf input. -/
theorem source_beta (Γ : Presheaf.Context) (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total A)) (b : Presheaf.Term B) :
    Presheaf.normalizedApp (Presheaf.normalizedLam b) = b := by
  let ρ : Fin 4 → Value := ![.context Γ,.family Γ A,.family (Presheaf.total A) B,
    .term (Presheaf.total A) B b]
  have h : ∀ a ∈ List.ofFn betaRule.premise, a.eval Products.algebra ρ := by
    intro a ha
    rcases List.mem_ofFn.mp ha with ⟨i,rfl⟩
    fin_cases i
    · exact ⟨Γ,A,rfl,rfl⟩
    · refine ⟨Presheaf.total A,B,b,?_,rfl,rfl⟩
      simp [SquareKit.GuardedTheory.Term.eval,Products.algebra,Source.operation,ρ]
  have he := interpret betaSource ρ h
  change extraOperation .app ![.family Γ A,.family (Presheaf.total A) B,
    extraOperation .lam ![.family Γ A,.family (Presheaf.total A) B,.term (Presheaf.total A) B b]] =
      .term (Presheaf.total A) B b at he
  rw [extra_lam,extra_app] at he
  exact eq_of_heq (Value.term.inj he).2.2

/-- Dependent output is still Fin(a.val+1), not an untyped numeric result. -/
theorem source_beta_at_two :
    (Presheaf.normalizedApp (Presheaf.normalizedLam lastArgument)).val
      ((Presheaf.total finiteFiber).elementsMk (Opposite.op ⟨0⟩)
        ⟨(3 : ℕ),(2 : Fin 4)⟩) = (2 : Fin 3) := by
  rw [source_beta]
  rfl

def piSubSource : Derivation theory (List.ofFn piSubRule.premise) piSubRule.conclusion := by
  have d := Derivation.rule (T := theory) (.inr .piSub) SquareKit.GuardedTheory.Term.var
    (fun i => Derivation.hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory, Theory.extend, Products.rule, Atom.subst_id] using d

theorem source_piSub (Γ Δ : Presheaf.Context) (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total A)) (σ : Δ ⟶ Γ) :
    Presheaf.reindex (Presheaf.normalizedPi A B) σ =
      Presheaf.normalizedPi (Presheaf.reindex A σ) (Presheaf.reindex B (Presheaf.liftSub A σ)) := by
  let ρ : Fin 5 → Value := ![.context Γ,.context Δ,.family Γ A,
    .family (Presheaf.total A) B,.substitution Δ Γ σ]
  have h : ∀ a ∈ List.ofFn piSubRule.premise, a.eval Products.algebra ρ := by
    intro a ha
    rcases List.mem_ofFn.mp ha with ⟨i,rfl⟩
    fin_cases i
    · exact ⟨Γ,A,rfl,rfl⟩
    · refine ⟨Presheaf.total A,B,?_,rfl⟩
      simp [SquareKit.GuardedTheory.Term.eval,Products.algebra,Source.operation,ρ]
    · exact ⟨Δ,Γ,σ,rfl,rfl,rfl⟩
  have he := interpret piSubSource ρ h
  have hl : (lift (.var 1) (.var 2) (.var 4) : Expression (Fin 5)).eval Products.algebra ρ =
      .substitution (Presheaf.total (Presheaf.reindex A σ)) (Presheaf.total A)
        (Presheaf.liftSub A σ) := lift_eval Γ Δ A σ
  change Source.operation .subTy ![extraOperation .pi ![.family Γ A,.family (Presheaf.total A) B],
      .substitution Δ Γ σ] =
    extraOperation .pi ![Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
      Source.operation .subTy ![.family (Presheaf.total A) B,
        (lift (.var 1) (.var 2) (.var 4)).eval Products.algebra ρ]] at he
  rw [hl,extra_pi] at he
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at he
  have hp := extra_pi Δ (Presheaf.reindex A σ) (Presheaf.reindex B (Presheaf.liftSub A σ))
  exact eq_of_heq (Value.family.inj (he.trans hp)).2

/-- The equality used for conversion is obtained from a source derivation. -/
theorem source_conversion_at_two :
    (Presheaf.normalizedApp ((chooseLast.reindex successor).convert
      (source_piSub naturals naturals finiteFiber argumentFiber successor))).val
        ((Presheaf.total (Presheaf.reindex finiteFiber successor)).elementsMk (Opposite.op ⟨0⟩)
          ⟨(2 : ℕ),(2 : Fin 4)⟩) = (2 : Fin 3) := by
  have h := Presheaf.Term.convert_independent
    (source_piSub naturals naturals finiteFiber argumentFiber successor)
    successor_formation (chooseLast.reindex successor)
  exact (congrArg (fun t => (Presheaf.normalizedApp t).val
    ((Presheaf.total (Presheaf.reindex finiteFiber successor)).elementsMk (Opposite.op ⟨0⟩)
      ⟨(2 : ℕ),(2 : Fin 4)⟩)) h).trans successor_at_two

/-- Invalid context operands cannot acquire a type through the source rules. -/
theorem reject_context_as_function_type :
    ¬ Nonempty (Derivation theory []
      (family (.var 0) (pi (.var 0) (.var 0)) : Judgment (Fin 1))) := by
  rintro ⟨d⟩
  have h := interpret d (fun _ => Value.context naturals) (by simp)
  change Source.predicate .family ![.context naturals,
    extraOperation .pi ![.context naturals,.context naturals]] at h
  have hi : extraOperation .pi ![Value.context naturals,.context naturals] = .invalid := rfl
  rw [hi] at h
  rcases h with ⟨Γ,A,hΓ,hA⟩
  cases hA

end Examples.CubicalSourceProducts
