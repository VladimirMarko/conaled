import SquareKit.Internal.DependentFunctionSheafContext

/-! Experimental embedding of the previous normalized structural fragment.
The old syntax and old canonical sheaf contexts retain their existing clients.
Their valuations embed with exactly the old carrier and interpreted variables. -/
namespace SquareKit.Internal.DependentFunctions
namespace StructuralEmbedding
open DependentStructural (Base)
abbrev Old := DependentStructural.Ctx

def context : {n : Nat} → Old n → Ctx n
  | _, .nil => .nil
  | _, .base Γ => .base (context Γ)
  | _, .family Γ b => .family (context Γ) b

def embedVar : {n : Nat} → {Γ : Old n} → DependentStructural.DVar Γ → DVar (context Γ)
  | _, _, .top => .top
  | _, _, .family v => .family (embedVar v)
  | _, _, .base v => .base (embedVar v)

def recover : {n : Nat} → (Γ : Old n) → DVar (context Γ) → DependentStructural.DVar Γ
  | _, .nil, v => nomatch v
  | _, .base Γ, v => match v with | .base w => .base (recover Γ w)
  | _, .family Γ _, v => match v with
    | .top => .top
    | .family w => .family (recover Γ w)

theorem recover_variable {n} {Γ : Old n} (v : DependentStructural.DVar Γ) : recover Γ (embedVar v) = v := by
  induction v with
  | top => rfl
  | base v ih => exact congrArg DependentStructural.DVar.base ih
  | family v ih => exact congrArg DependentStructural.DVar.family ih

theorem variable_type {n} {Γ : Old n} (v : DependentStructural.DVar Γ) : (embedVar v).type = v.type := by
  induction v with
  | top => rfl
  | base v ih => exact congrArg Base.wk ih
  | family v ih => exact ih

theorem recover_type : {n : Nat} → (Γ : Old n) → (v : DVar (context Γ)) → (recover Γ v).type = v.type
  | _, .nil, v => nomatch v
  | _, .base Γ, v => match v with | .base w => congrArg Base.wk (recover_type Γ w)
  | _, .family Γ _, v => match v with
    | .top => rfl
    | .family w => recover_type Γ w

theorem noFunction : {n : Nat} → (Γ : Old n) → FVar (context Γ) → False
  | _, .nil, v => nomatch v
  | _, .base Γ, v => match v with | .base w => noFunction Γ w
  | _, .family Γ _, v => match v with | .family w => noFunction Γ w

def dep {n} {Γ : Old n} : DependentStructural.Dep Γ → Dep (context Γ)
  | .var v => .var (embedVar v)
  | .point => .point

theorem dep_type {n} {Γ : Old n} (t : DependentStructural.Dep Γ) : (dep t).type = t.type := by
  cases t with
  | var v => exact variable_type v
  | point => rfl

def type {n} : DependentStructural.Ty n → Ty n
  | .base => .base
  | .family b => .family b

def term {n} {Γ : Old n} : {A : DependentStructural.Ty n} → DependentStructural.Tm Γ A → Tm (context Γ) (type A)
  | .base, t => t
  | .family _, t => ⟨dep t.val, (dep_type t.val).trans t.property⟩

def substitution {n m} {Γ : Old n} {Δ : Old m} (σ : DependentStructural.Sub Δ Γ) : Sub (context Δ) (context Γ) where
  base := σ.base
  dep v := dep (σ.dep (recover Γ v))
  func v := False.elim (noFunction Γ v)

theorem substitution_typed {n m} {Γ : Old n} {Δ : Old m} (σ : DependentStructural.Sub Δ Γ) :
    (substitution σ).Typed where
  dep v := (dep_type _).trans ((σ.typed (recover Γ v)).trans
    (congrArg (Base.sub σ.base) (recover_type Γ v)))
  func v := False.elim (noFunction Γ v)

theorem substitution_dep {n m} {Γ : Old n} {Δ : Old m} (σ : DependentStructural.Sub Δ Γ) (t : DependentStructural.Dep Γ) :
    (substitution σ).depSub (dep t) = dep (σ.depSub t) := by
  cases t with
  | point => rfl
  | var v => exact congrArg (fun w => dep (σ.dep w)) (recover_variable v)

theorem equality {n} {Γ : Old n} {t u : DependentStructural.Dep Γ} (h : DependentStructural.DepEq t u) :
    DepEq (dep t) (dep u) := by
  cases h.literal
  exact .refl _

noncomputable section
open CategoryTheory SquareKit SplitSheaf
open DependentStructural.SheafSem (evalBase evalDep evalDep_type)
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : SheafSem.Model J) {n} {Γ : Old n}

def environment (E : DependentStructural.SheafSem.Env M Γ) : SheafSem.Env M (context Γ) where
  carrier := E.carrier
  base := E.base
  dep v := readTerm M.A (E.dep (recover Γ v))
    ((E.typed (recover Γ v)).trans (congrArg (evalBase M E.base) (recover_type Γ v)))
  func v := False.elim (noFunction Γ v)

theorem interpretation (E : DependentStructural.SheafSem.Env M Γ) (t : DependentStructural.Dep Γ) :
    HEq (SheafSem.evalDep M (environment M E) (dep t))
      (readTerm M.A (evalDep M E t) (evalDep_type M E t)) := by
  cases t with
  | point => rfl
  | var v =>
    dsimp only [dep, SheafSem.evalDep, environment, evalDep]
    apply DependentStructural.SheafSem.read_heq
    · exact congrArg E.dep (recover_variable v)
    · exact congrArg (evalBase M E.base) (variable_type v)

/-- In particular the embedding uses each already-constructed old context,
with no replacement of its carrier or representation for existing callers. -/
theorem canonical_interpretation (t : DependentStructural.Dep Γ) :
    HEq (SheafSem.evalDep M (environment M (DependentStructural.SheafSem.context M Γ)) (dep t))
      (DependentStructural.SheafSem.term M Γ (A := .family t.type) ⟨t, rfl⟩) :=
  interpretation M (DependentStructural.SheafSem.context M Γ) t

/-- Base expressions agree as ordinary maps after the old display adapter;
the new strict constant family does not replace the old representation. -/
theorem base_interpretation (b : Base n) :
    SplitSheaf.constantPair M.B (𝟙 (DependentStructural.SheafSem.context M Γ).carrier)
      (evalBase M (DependentStructural.SheafSem.context M Γ).base b) ≫ SplitSheaf.constantValue M.B =
    SplitSheaf.pair (DependentStructural.SheafSem.baseType M) (Limits.terminal.from _)
      (DependentStructural.SheafSem.term M Γ (A := .base) b) ≫
        (SplitSheaf.displayIso (Limits.terminal.from M.B)).hom := by
  change evalBase M (DependentStructural.SheafSem.context M Γ).base b = _
  dsimp only [DependentStructural.SheafSem.term]
  erw [SplitSheaf.pair_read]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end
end StructuralEmbedding
end SquareKit.Internal.DependentFunctions
