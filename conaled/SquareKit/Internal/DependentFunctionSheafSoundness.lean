import SquareKit.Internal.DependentFunctionSheafSubstitution

/-! Experimental soundness of every dependent-function equality rule. The proof
interprets derivations; neither beta/eta nor substitution soundness is a model
field. Semantic values are independent of derivation proofs. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
open DependentStructural.SheafSem (evalBase)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model J) {n} {Γ : Ctx n} {X : Sh J}

theorem apply_heq (ρ : Fin n → (X ⟶ M.B)) {b c : Base (n+1)} (h : b = c)
    {t : SplitSheaf.Tm (function M ρ b)} {u : SplitSheaf.Tm (function M ρ c)} (ht : HEq t u) (a : Base n) :
    HEq (applyTerm M ρ t a) (applyTerm M ρ u a) := by cases h; cases ht; rfl

theorem beta_sound (E : Env M Γ) (t : Dep (.base Γ)) (a : Base n) :
    HEq (evalDep M E (.app (.lam t) a)) (evalDep M E ((Sub.plug Γ a).depSub t)) := by
  have h := evalDep_sub M (plugRealization M E a) t
  dsimp only [evalDep, evalFunc, applyTerm]
  erw [SplitSheafPi.app_beta]
  exact (transport_heq _ _).trans h.symm

theorem unlam_natural_index {m} {Y : Sh J} {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
    {δ : Fin n → Base m} {s : Y ⟶ X} (h : BaseRealization M ρ τ δ s)
    {b : Base (n+1)} {b' : Base (m+1)} (hb : b' = b.sub (up δ))
    (t : SplitSheaf.Tm (function M ρ b)) (u : SplitSheaf.Tm (function M τ b'))
    (ht : HEq u (tmSub t s)) :
    HEq (SplitSheafPi.unlam (baseType M Y) u)
      (tmSub (SplitSheafPi.unlam (baseType M X) t) (lift (baseType M X) s)) := by
  subst b'; exact unlam_natural M h b t u ht

theorem eta_body (E : Env M Γ) (f : Func Γ) :
    HEq (evalDep M (baseEnv M E) (.app ((Ren.weaken Γ).funcMap f) (.var 0)))
      (SplitSheafPi.unlam (baseType M E.carrier) (evalFunc M E f)) := by
  let u := evalFunc M (baseEnv M E) ((Ren.weaken Γ).funcMap f)
  have ht := unlam_natural_index M (weakening M E.base)
    (Ren.funcMap_type _ (Ren.typed_weaken Γ) f) (evalFunc M E f) u (evalFunc_weaken M E f)
  have hb : result M (extend M E.base) ((Ren.weaken Γ).funcMap f).type =
      tySub (result M E.base f.type) (lift (baseType M E.carrier) (p (baseType M E.carrier))) :=
    (congrArg (result M (extend M E.base)) (Ren.funcMap_type _ (Ren.typed_weaken Γ) f)).trans
      (result_sub M (weakening M E.base) f.type).symm
  have hs := tmSub_heq hb ht
    (constantPair M.B (𝟙 (baseExt M E.carrier)) (constantValue M.B))
  exact (transport_heq _ _).trans hs

theorem eta_sound (E : Env M Γ) (f : Func Γ) :
    HEq (evalFunc M E (.lam (.app ((Ren.weaken Γ).funcMap f) (.var 0)))) (evalFunc M E f) := by
  have h := lam_heq (baseType M E.carrier) (congrArg (result M E.base) (eta_type f)) (eta_body M E f)
  exact h.trans (heq_of_eq (SplitSheafPi.eta _ _))

mutual
 theorem dep_sound : {n : Nat} → {Γ : Ctx n} → {t u : Dep Γ} →
     DepEq t u → (E : Env M Γ) → HEq (evalDep M E t) (evalDep M E u)
   | _, _, _, _, .refl _, _ => HEq.rfl
   | _, _, _, _, .symm h, E => (dep_sound h E).symm
   | _, _, _, _, .trans h k, E => (dep_sound h E).trans (dep_sound k E)
   | _, _, _, _, .app h a, E => apply_heq M E.base h.type (func_sound h E) a
   | _, _, _, _, .beta t a, E => beta_sound M E t a
   | _, _, _, _, .sub σ hs h, E =>
       (evalDep_sub M (assignmentRealization M E σ hs) _).trans
         ((dep_sound h (assignmentEnv M E σ hs)).trans
           (evalDep_sub M (assignmentRealization M E σ hs) _).symm)
 theorem func_sound : {n : Nat} → {Γ : Ctx n} → {f g : Func Γ} →
     FuncEq f g → (E : Env M Γ) → HEq (evalFunc M E f) (evalFunc M E g)
   | _, _, _, _, .refl _, _ => HEq.rfl
   | _, _, _, _, .symm h, E => (func_sound h E).symm
   | _, _, _, _, .trans h k, E => (func_sound h E).trans (func_sound k E)
   | _, _, _, _, .lam h, E => lam_heq (baseType M E.carrier)
       (congrArg (result M E.base) h.type) (dep_sound h (baseEnv M E))
   | _, _, _, _, .eta f, E => eta_sound M E f
   | _, _, _, _, .sub σ hs h, E =>
       (evalFunc_sub M (assignmentRealization M E σ hs) _).trans
         ((func_sound h (assignmentEnv M E σ hs)).trans
           (evalFunc_sub M (assignmentRealization M E σ hs) _).symm)
end

end SquareKit.Internal.DependentFunctions.SheafSem
