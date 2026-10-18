import SquareKit.Internal.DependentSheafContext

/-! Experimental construction of the interpretation of finite source
assignments. Variable equations are proved by recursion on the target telescope;
they are outputs of the construction, not model assumptions. -/
noncomputable section
namespace SquareKit.Internal.DependentStructural.SheafSem
open CategoryTheory Limits SquareKit
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model.{u,v,w} J)

structure Realization {m n} {Δ : Ctx m} {Γ : Ctx n} (E : Env M Δ) (F : Env M Γ) (σ : Sub Δ Γ) where
  map : E.carrier ⟶ F.carrier
  base_eq : ∀ i, map ≫ F.base i = evalBase M E.base (σ.base i)
  dep_eq : ∀ v, map ≫ F.dep v = evalDep M E (σ.dep v)

theorem realized_base {m n} {Δ : Ctx m} {Γ : Ctx n} {E : Env M Δ} {F : Env M Γ} {σ : Sub Δ Γ}
    (r : Realization M E F σ) (b : Base n) :
    r.map ≫ evalBase M F.base b = evalBase M E.base (b.sub σ.base) := by
  rw [eval_sub, ← eval_precomp]
  exact congrArg (fun ρ => evalBase M ρ b) (funext r.base_eq)

theorem realized_dep {m n} {Δ : Ctx m} {Γ : Ctx n} {E : Env M Δ} {F : Env M Γ} {σ : Sub Δ Γ}
    (r : Realization M E F σ) (t : Dep Γ) :
    r.map ≫ evalDep M F t = evalDep M E (σ.depSub t) := by
  cases t with
  | var v => exact r.dep_eq v
  | point =>
    change r.map ≫ (terminal.from F.carrier ≫ M.point) = terminal.from E.carrier ≫ M.point
    rw [← Category.assoc]
    exact congrArg (fun k => k ≫ M.point) (terminal.hom_ext _ _)

/-- Every well-typed finite source assignment has a constructed sheaf map. -/
def realize {m} {Δ : Ctx m} (E : Env M Δ) {n} (Γ : Ctx n) : (σ : Sub Δ Γ) →
    Realization M E (context M Γ) σ := by
  induction Γ with
  | nil =>
    intro σ
    exact {
      map := terminal.from E.carrier
      base_eq := fun i => Fin.elim0 i
      dep_eq := fun v => nomatch v }
  | base Γ ih =>
      intro σ
      let r := ih (Sub.comp (Sub.pBase Γ) σ)
      refine ⟨basePair M r.map (evalBase M E.base (σ.base 0)), ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact basePair_value M _ _
        · change _ ≫ (baseProjection M _ ≫ (context M Γ).base j) = _
          rw [← Category.assoc, basePair_projection]
          exact r.base_eq j
      · intro v
        cases v with
        | base v =>
          change _ ≫ (baseProjection M _ ≫ (context M Γ).dep v) = _
          rw [← Category.assoc, basePair_projection]
          exact r.dep_eq v
  | family Γ b ih =>
      intro σ
      let r := ih (Sub.comp (Sub.p Γ b) σ)
      have ht : evalDep M E (σ.dep .top) ≫ SplitSheaf.p M.A =
          r.map ≫ evalBase M (context M Γ).base b :=
        (evalDep_type M E (σ.dep .top)).trans
          ((congrArg (evalBase M E.base) (σ.typed .top)).trans (realized_base M r b).symm)
      let t := SplitSheaf.readTerm M.A (evalDep M E (σ.dep .top)) ht
      refine ⟨SplitSheaf.pair (SplitSheaf.tySub M.A (evalBase M (context M Γ).base b)) r.map t, ?_, ?_⟩
      · intro i
        change _ ≫ (SplitSheaf.p _ ≫ (context M Γ).base i) = _
        exact r.base_eq i
      · exact fun
          | .top => SplitSheaf.pair_read M.A _ ht
          | .family v => r.dep_eq v

/-- Maps into a constructed context are determined by their source variables. -/
theorem context_ext {n} (Γ : Ctx n) {X : Sh.{u,v,w} J} (f g : X ⟶ (context M Γ).carrier)
    (hb : ∀ i, f ≫ (context M Γ).base i = g ≫ (context M Γ).base i)
    (hd : ∀ v, f ≫ (context M Γ).dep v = g ≫ (context M Γ).dep v) : f = g := by
  induction Γ with
  | nil => exact terminal.hom_ext _ _
  | base Γ ih =>
    apply base_ext M
    · apply ih
      · intro i; exact (Category.assoc _ _ _).trans ((hb i.succ).trans (Category.assoc _ _ _).symm)
      · intro v; exact (Category.assoc _ _ _).trans ((hd (.base v)).trans (Category.assoc _ _ _).symm)
    · exact hb 0
  | family Γ b ih =>
    apply (SplitSheaf.extension_pullback M.A (evalBase M (context M Γ).base b)).hom_ext
    · exact hd .top
    · apply ih
      · intro i; exact (Category.assoc _ _ _).trans ((hb i).trans (Category.assoc _ _ _).symm)
      · intro v; exact (Category.assoc _ _ _).trans ((hd (.family v)).trans (Category.assoc _ _ _).symm)

def substitution {m n} {Δ : Ctx m} {Γ : Ctx n} (σ : Sub Δ Γ) :
    (context M Δ).carrier ⟶ (context M Γ).carrier := (realize M (context M Δ) Γ σ).map

@[simp] theorem substitution_base {m n} {Δ : Ctx m} {Γ : Ctx n} (σ : Sub Δ Γ) (i : Fin n) :
    substitution M σ ≫ (context M Γ).base i = evalBase M (context M Δ).base (σ.base i) :=
  (realize M (context M Δ) Γ σ).base_eq i
@[simp] theorem substitution_dep {m n} {Δ : Ctx m} {Γ : Ctx n} (σ : Sub Δ Γ) (v : DVar Γ) :
    substitution M σ ≫ (context M Γ).dep v = evalDep M (context M Δ) (σ.dep v) :=
  (realize M (context M Δ) Γ σ).dep_eq v

abbrev base_substitution {m n} {Δ : Ctx m} {Γ : Ctx n} (σ : Sub Δ Γ) :=
  realized_base M (realize M (context M Δ) Γ σ)
abbrev dep_substitution {m n} {Δ : Ctx m} {Γ : Ctx n} (σ : Sub Δ Γ) :=
  realized_dep M (realize M (context M Δ) Γ σ)

@[simp] theorem substitution_id {n} (Γ : Ctx n) : substitution M (Sub.id Γ) = 𝟙 _ := by
  apply context_ext M Γ <;> intro i <;> simp [evalBase, evalDep, Sub.id]

theorem substitution_comp {l m n} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l} (σ : Sub Δ Γ) (τ : Sub Ξ Δ) :
    substitution M (Sub.comp σ τ) = substitution M τ ≫ substitution M σ := by
  apply context_ext M Γ
  · intro i
    rw [Category.assoc, substitution_base, substitution_base]
    exact (base_substitution M τ (σ.base i)).symm
  · intro v
    rw [Category.assoc, substitution_dep, substitution_dep]
    exact (dep_substitution M τ (σ.dep v)).symm

/-- Soundness for every source equality constructor. The intermediate literal
lemma concerns algebraic source expressions only, never supplied model equations. -/
theorem sound {m n} {Δ : Ctx m} {Γ : Ctx n} {σ τ : Sub Δ Γ} (h : SubEq σ τ) :
    substitution M σ = substitution M τ := congrArg (substitution M) h.literal

end SquareKit.Internal.DependentStructural.SheafSem
