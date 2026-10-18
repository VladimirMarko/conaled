import SquareKit.Internal.DependentSheafSoundness

/-! Experimental ordinary-display consequences of a derived source proof. -/
noncomputable section
namespace SquareKit.Internal.DependentStructural.SheafSem
open CategoryTheory Limits SquareKit
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model.{u,v,w} J)
variable {l m n : Nat} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l}

/-- The transported source term appearing on the right of pairing naturality. -/
def substitutedArgument (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (b : Base n)
    (t : Tm Δ (.family (b.sub σ.base))) : Tm Ξ (.family (b.sub (Sub.comp σ τ).base)) :=
  ⟨τ.depSub t.val, (τ.depSub_type t.val).trans
    ((congrArg (Base.sub τ.base) t.property).trans (Base.sub_comp b σ.base τ.base))⟩

/-- The interpreted equation is an equation between the existing ordinary
pullback pairings, through #69's comparison on actual natural terms. -/
theorem derived_ordinary (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (b : Base n)
    (t : Tm Δ (.family (b.sub σ.base))) :
    Family.pair (SplitSheaf.p (type M Γ (.family b))) (substitution M (Sub.comp σ τ))
      (substitution M τ ≫ substitution M (Sub.pair σ b t)) (𝟙 _)
      (by
        have h := (derived_pairing M σ τ b t).trans
          (pairing M (Sub.comp σ τ) b (substitutedArgument σ τ b t))
        exact (congrArg (fun k => k ≫ SplitSheaf.p (type M Γ (.family b))) h).trans
          ((SplitSheaf.pair_p _ _ _).trans (Category.id_comp _).symm)) =
    (SplitSheaf.terms (SplitSheaf.tySub (type M Γ (.family b)) (substitution M (Sub.comp σ τ)))
      (pairTerm M (Sub.comp σ τ) b (substitutedArgument σ τ b t))).val ≫
        (SplitSheaf.substitutionIso (type M Γ (.family b)) (substitution M (Sub.comp σ τ))).hom := by
  rw [SplitSheaf.pairing_comparison]
  congr 1
  exact (derived_pairing M σ τ b t).trans (pairing M (Sub.comp σ τ) b (substitutedArgument σ τ b t))

/-- Projection interpretation is the existing split comprehension projection. -/
theorem projection (b : Base n) :
    substitution M (Sub.p Γ b) = SplitSheaf.p (type M Γ (.family b)) := by
  apply context_ext M Γ
  · intro i
    rw [substitution_base]
    rfl
  · intro v
    rw [substitution_dep]
    rfl

/-- Ordinary pullback substitution of every interpreted dependent term. -/
theorem ordinary_term_substitution (σ : Sub Δ Γ) {A : Ty n} (t : Tm Γ A) :
    (SplitSheaf.terms (SplitSheaf.tySub (type M Γ A) (substitution M σ))
      (SplitSheaf.tmSub (term M Γ t) (substitution M σ))).val ≫
        (SplitSheaf.substitutionIso (type M Γ A) (substitution M σ)).hom =
      (Family.termSub (SplitSheaf.p (type M Γ A)) (substitution M σ)
        (SplitSheaf.terms (type M Γ A) (term M Γ t))).val :=
  SplitSheaf.term_substitution _ _ _

theorem base_pairing (σ : Sub Δ Γ) (t : Base m) :
    substitution M (Sub.pairBase σ t) =
      basePair M (substitution M σ) (evalBase M (context M Δ).base t) := rfl

theorem base_projection : substitution M (Sub.pBase Γ) = baseProjection M (context M Γ).carrier := by
  apply context_ext M Γ
  · intro i; rw [substitution_base]; rfl
  · intro v; rw [substitution_dep]; rfl

/-- The source generic dependent variable denotes the actual split variable,
with the type equality caused by weakening made explicit. -/
theorem variable_type (b : Base n) :
    SplitSheaf.tySub (type M Γ (.family b)) (SplitSheaf.p (type M Γ (.family b))) =
      type M (.family Γ b) (.family b) :=
  congrArg (SplitSheaf.tySub M.A)
    (eval_precomp M (context M Γ).base (SplitSheaf.p (type M Γ (.family b))) b).symm

theorem generic_variable (b : Base n) :
    SplitSheaf.transport (variable_type M b) (SplitSheaf.q (type M Γ (.family b))) =
      term M (.family Γ b) (Sub.q Γ b) := by
  have ht := eqRec_heq (variable_type M b) (SplitSheaf.q (type M Γ (.family b)))
  apply eq_of_heq (ht.trans ?_)
  change HEq (SplitSheaf.readTerm M.A (SplitSheaf.lift M.A (evalBase M (context M Γ).base b)) rfl)
    (SplitSheaf.readTerm M.A (SplitSheaf.lift M.A (evalBase M (context M Γ).base b))
      ((SplitSheaf.lift_p M.A _).trans (eval_precomp M (context M Γ).base (SplitSheaf.p _) b).symm))
  apply read_heq M.A rfl
  exact (eval_precomp M (context M Γ).base (SplitSheaf.p (type M Γ (.family b))) b).symm

end SquareKit.Internal.DependentStructural.SheafSem
