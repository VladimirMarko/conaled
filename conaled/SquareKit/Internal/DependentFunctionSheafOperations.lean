import SquareKit.Internal.DependentFunctionSheafTerms
import SquareKit.Internal.DependentSheafSoundness

/-! Experimental transport and substitution laws for the interpreted operations.
These laws use equality-level Pi stability from the constructed split model. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
open DependentStructural.SheafSem (evalBase)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X Y Z : Sh J}

theorem tmSub_transport_heq {A B : SplitSheaf.Ty X} (h : A = B) (t : SplitSheaf.Tm A) (s : Y ⟶ X) :
    HEq (tmSub (transport h t) s) (tmSub t s) := by cases h; rfl

theorem lam_heq (A : SplitSheaf.Ty X) {B D : SplitSheaf.Ty (Ext A)} (h : B = D)
    {t : SplitSheaf.Tm B} {u : SplitSheaf.Tm D} (ht : HEq t u) :
    HEq (SplitSheafPi.lam A t) (SplitSheafPi.lam A u) := by cases h; cases ht; rfl

theorem unlam_heq (A : SplitSheaf.Ty X) {B D : SplitSheaf.Ty (Ext A)} (h : B = D)
    {t : SplitSheaf.Tm (SplitSheafPi.pi A B)} {u : SplitSheaf.Tm (SplitSheafPi.pi A D)} (ht : HEq t u) :
    HEq (SplitSheafPi.unlam A t) (SplitSheafPi.unlam A u) := by cases h; cases ht; rfl

variable (M : Model J) {n m}
variable {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
variable {δ : Fin n → Base m} {s : Y ⟶ X}

theorem lam_natural (h : BaseRealization M ρ τ δ s) (b : Base (n+1))
    (t : SplitSheaf.Tm (result M ρ b)) (u : SplitSheaf.Tm (result M τ (b.sub (up δ))))
    (ht : HEq u (tmSub t (lift (baseType M X) s))) :
    HEq (SplitSheafPi.lam (baseType M Y) u) (tmSub (SplitSheafPi.lam (baseType M X) t) s) := by
  have h₁ := lam_heq (baseType M Y) (result_sub M h b).symm ht
  have h₂ := SplitSheafPi.lam_substitution (baseType M X) t s
  exact h₁.trans ((heq_of_eq h₂.symm).trans (transport_heq _ _))

theorem unlam_natural (h : BaseRealization M ρ τ δ s) (b : Base (n+1))
    (t : SplitSheaf.Tm (function M ρ b)) (u : SplitSheaf.Tm (function M τ (b.sub (up δ))))
    (ht : HEq u (tmSub t s)) :
    HEq (SplitSheafPi.unlam (baseType M Y) u)
      (tmSub (SplitSheafPi.unlam (baseType M X) t) (lift (baseType M X) s)) := by
  have h₁ := unlam_heq (baseType M Y) (result_sub M h b).symm
    (ht.trans (transport_heq (SplitSheafPi.substitution (baseType M X) (result M ρ b) s) (tmSub t s)).symm)
  exact h₁.trans (heq_of_eq (SplitSheafPi.unlam_substitution (baseType M X) t s))

theorem argument_natural (h : BaseRealization M ρ τ δ s) (a : Base n) :
    constantPair M.B (𝟙 Y) (evalBase M τ (a.sub δ)) ≫ lift (baseType M X) s =
      s ≫ constantPair M.B (𝟙 X) (evalBase M ρ a) := by
  apply constant_ext M.B
  · rfl
  · change evalBase M τ (a.sub δ) = s ≫ evalBase M ρ a
    exact base_realization M h a

theorem app_natural (h : BaseRealization M ρ τ δ s) (b : Base (n+1))
    (t : SplitSheaf.Tm (function M ρ b)) (u : SplitSheaf.Tm (function M τ (b.sub (up δ))))
    (ht : HEq u (tmSub t s)) (a : Base n) :
    HEq (applyTerm M τ u (a.sub δ)) (tmSub (applyTerm M ρ t a) s) := by
  have h₁ := tmSub_heq (result_sub M h b).symm (unlam_natural M h b t u ht)
    (constantPair M.B (𝟙 Y) (evalBase M τ (a.sub δ)))
  have h₂ : HEq (tmSub (tmSub (SplitSheafPi.unlam (baseType M X) t) (lift (baseType M X) s))
      (constantPair M.B (𝟙 Y) (evalBase M τ (a.sub δ))))
      (tmSub (tmSub (SplitSheafPi.unlam (baseType M X) t)
        (constantPair M.B (𝟙 X) (evalBase M ρ a))) s) := by
    change HEq (tmSub (SplitSheafPi.unlam (baseType M X) t)
      (constantPair M.B (𝟙 Y) (evalBase M τ (a.sub δ)) ≫ lift (baseType M X) s))
      (tmSub (SplitSheafPi.unlam (baseType M X) t)
        (s ≫ constantPair M.B (𝟙 X) (evalBase M ρ a)))
    rw [argument_natural M h a]
  exact (transport_heq _ _).trans (h₁.trans (h₂.trans
    (tmSub_transport_heq (result_plug M ρ b a) _ s).symm))


theorem lam_natural_index (h : BaseRealization M ρ τ δ s) {b : Base (n+1)} {b' : Base (m+1)}
    (hb : b' = b.sub (up δ)) (t : SplitSheaf.Tm (result M ρ b))
    (u : SplitSheaf.Tm (result M τ b'))
    (ht : HEq u (tmSub t (lift (baseType M X) s))) :
    HEq (SplitSheafPi.lam (baseType M Y) u) (tmSub (SplitSheafPi.lam (baseType M X) t) s) := by
  subst b'; exact lam_natural M h b t u ht

theorem app_natural_index (h : BaseRealization M ρ τ δ s) {b : Base (n+1)} {b' : Base (m+1)}
    (hb : b' = b.sub (up δ)) (t : SplitSheaf.Tm (function M ρ b))
    (u : SplitSheaf.Tm (function M τ b')) (ht : HEq u (tmSub t s)) (a : Base n) :
    HEq (applyTerm M τ u (a.sub δ)) (tmSub (applyTerm M ρ t a) s) := by
  subst b'; exact app_natural M h b t u ht a

end SquareKit.Internal.DependentFunctions.SheafSem
