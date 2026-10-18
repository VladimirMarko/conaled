import SquareKit.Internal.DependentFunctionEmbedding

/-! Experimental source-to-ordinary dependent-product comparison. Source function
names are carried to actual ordinary displays, and their bodies use the actual
pullback adjunction counit. The derived source beta proof feeds this comparison. -/
noncomputable section
namespace SquareKit.Internal.DependentFunctions.SheafSem
open CategoryTheory Limits SquareKit SplitSheaf
open DependentStructural (Base)
open DependentStructural.SheafSem (evalBase)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model J) {n m} {Γ : Ctx n} {Δ : Ctx m}

def depValue (E : Env M Γ) (t : Dep Γ) : E.carrier ⟶ Ext M.A :=
  pair M.A (evalBase M E.base t.type) (evalDep M E t)

private theorem value_heq {X : Sh J} (ρ : Fin n → (X ⟶ M.B)) {b c : Base n} (h : b = c)
    {t : SplitSheaf.Tm (family M ρ b)} {u : SplitSheaf.Tm (family M ρ c)} (ht : HEq t u) :
    pair M.A (evalBase M ρ b) t = pair M.A (evalBase M ρ c) u := by cases h; cases ht; rfl

theorem value_sound (E : Env M Γ) {t u : Dep Γ} (h : DepEq t u) :
    depValue M E t = depValue M E u := value_heq M E.base h.type (dep_sound M h E)

def functionName (E : Env M Γ) (f : Func Γ) :
    Over.mk (𝟙 E.carrier) ⟶ Over.mk (p (function M E.base f.type)) :=
  Over.homMk (pair (function M E.base f.type) (𝟙 E.carrier) (evalFunc M E f)) rfl

def ordinaryName (E : Env M Γ) (f : Func Γ) :
    Over.mk (𝟙 E.carrier) ⟶
      (SheafDependentProduct.pi (p (baseType M E.carrier))).obj (Over.mk (p (result M E.base f.type))) :=
  functionName M E f ≫ (SplitSheafPi.displayIso (baseType M E.carrier) (result M E.base f.type)).hom

def ordinaryBody (E : Env M Γ) (f : Func Γ) :
    (Over.pullback (p (baseType M E.carrier))).obj (Over.mk (𝟙 E.carrier)) ⟶
      Over.mk (p (result M E.base f.type)) :=
  (Over.pullback (p (baseType M E.carrier))).map (ordinaryName M E f) ≫
    SheafDependentProduct.evaluation (p (baseType M E.carrier)) (Over.mk (p (result M E.base f.type)))

theorem ordinaryBody_eq (E : Env M Γ) (f : Func Γ) :
    ordinaryBody M E f =
      (SplitSheafPi.homEquiv (baseType M E.carrier) (result M E.base f.type) _).symm (functionName M E f) := by
  unfold ordinaryBody ordinaryName
  erw [← SheafDependentProduct.uncurry_evaluation, SplitSheafPi.displayIso_apply, SheafDependentProduct.beta]

theorem ordinaryBody_term (E : Env M Γ) (f : Func Γ) :
    SplitSheafPi.inputTerms (baseType M E.carrier) (result M E.base f.type) (𝟙 E.carrier) (ordinaryBody M E f) =
      SplitSheafPi.unlam (baseType M E.carrier) (evalFunc M E f) := by
  rw [ordinaryBody_eq]
  change (SplitSheafPi.inputTerms (baseType M E.carrier) (result M E.base f.type) (𝟙 E.carrier))
    ((SplitSheafPi.inputTerms (baseType M E.carrier) (result M E.base f.type) (𝟙 E.carrier)).symm
      (SplitSheafPi.unlam (baseType M E.carrier) (evalFunc M E f))) = _
  exact Equiv.apply_symm_apply _ _

theorem lambda_body (E : Env M Γ) (t : Dep (.base Γ)) :
    SplitSheafPi.inputTerms (baseType M E.carrier) (result M E.base t.type) (𝟙 E.carrier)
      (ordinaryBody M E (.lam t)) = evalDep M (baseEnv M E) t := by
  exact (ordinaryBody_term M E (.lam t)).trans (SplitSheafPi.beta _ _)

theorem ordinary_curry (E : Env M Γ) (f : Func Γ) :
    SheafDependentProduct.curry (p (baseType M E.carrier)) (ordinaryBody M E f) = ordinaryName M E f :=
  (congrArg (SheafDependentProduct.curry (p (baseType M E.carrier)))
    (SheafDependentProduct.uncurry_evaluation (p (baseType M E.carrier)) (ordinaryName M E f))).symm.trans
    (SheafDependentProduct.eta _ _)

/-- Apply the actual counit after identifying its ordinary pullback domain with
split comprehension, then substitute the source argument into the result. -/
def ordinaryApplication (E : Env M Γ) (f : Func Γ) (a : Base n) :
    SplitSheaf.Tm (family M E.base (instantiate f.type a)) :=
  transport (result_plug M E.base f.type a)
    (tmSub (SplitSheafPi.inputTerms (baseType M E.carrier) (result M E.base f.type)
      (𝟙 E.carrier) (ordinaryBody M E f))
      (constantPair M.B (𝟙 E.carrier) (evalBase M E.base a)))

theorem ordinary_application (E : Env M Γ) (f : Func Γ) (a : Base n) :
    ordinaryApplication M E f a = evalDep M E (.app f a) := by
  unfold ordinaryApplication
  erw [ordinaryBody_term]
  rfl

/-- Source derivation, full-language soundness, and the actual ordinary counit.
No semantic beta proof is substituted for the source derivation in this chain. -/
theorem derived_ordinary (E : Env M Δ) (σ : Sub Δ Γ) (hs : σ.Typed)
    (t : Dep (.base Γ)) (a : Base n) :
    HEq (ordinaryApplication M E (.lam (σ.lift.depSub t)) (a.sub σ.base))
      (evalDep M E (σ.depSub ((Sub.plug Γ a).depSub t))) :=
  (heq_of_eq (ordinary_application M E _ _)).trans (dep_sound M (substituted_beta σ hs t a) E)

/-- The actual canonical mate agrees with the split equality comparison used in
function substitution. The remaining index adapter is the proved result_sub. -/
theorem substitution_mate {X Y : Sh J} (ρ : Fin n → (X ⟶ M.B)) (b : Base (n+1)) (s : Y ⟶ X) :
    SplitSheafPi.canonicalBaseChange (baseType M X) (result M ρ b) s =
      SplitSheafPi.splitBaseChange (baseType M X) (result M ρ b) s :=
  SplitSheafPi.baseChange_eq _ _ _


theorem typeIso_trans {X : Sh J} {A B D : SplitSheaf.Ty X} (h : A = B) (k : B = D) :
    SplitSheafPi.typeIso h ≪≫ SplitSheafPi.typeIso k = SplitSheafPi.typeIso (h.trans k) := by
  cases h; cases k; rfl

/-- Include the source index substitution in the ordinary comparison. This is
the canonical mate followed by the constructed result-family equality adapter. -/
theorem source_substitution_mate {X Y : Sh J} {ρ : Fin n → (X ⟶ M.B)} {τ : Fin m → (Y ⟶ M.B)}
    {δ : Fin n → Base m} {s : Y ⟶ X} (h : BaseRealization M ρ τ δ s) (b : Base (n+1)) :
    SplitSheafPi.canonicalBaseChange (baseType M X) (result M ρ b) s ≪≫
      SplitSheafPi.typeIso (congrArg (SplitSheafPi.pi (baseType M Y)) (result_sub M h b)) =
    (SplitSheafPi.displaySubIso (function M ρ b) s).symm ≪≫
      SplitSheafPi.typeIso (function_sub M h b) := by
  rw [SplitSheafPi.baseChange_eq]
  change ((_ ≪≫ SplitSheafPi.typeIso (SplitSheafPi.substitution (baseType M X) (result M ρ b) s)) ≪≫ _) = _
  rw [Iso.trans_assoc]
  exact congrArg (fun i => (SplitSheafPi.displaySubIso (function M ρ b) s).symm ≪≫ i)
    (typeIso_trans (SplitSheafPi.substitution (baseType M X) (result M ρ b) s)
      (congrArg (SplitSheafPi.pi (baseType M Y)) (result_sub M h b)))

end SquareKit.Internal.DependentFunctions.SheafSem
