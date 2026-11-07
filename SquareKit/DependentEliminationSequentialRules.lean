import SquareKit.DependentSequentialRules
import SquareKit.DependentPairTemplates
import SquareKit.DependentPairEliminationJudgments

/-! Empty-context rule templates for the independent eliminator presentation. -/
namespace SquareKit.DependentEliminationSequentialRules
open DependentTheoryMaps DependentPairJudgments DependentPairPresentations
open DependentSequentialRules
open Templates

abbrev formationMetavariables : Metavariables := ⟨2, fun i => match i.val with | 1 => 1 | _ => 0⟩
abbrev packMetavariables : Metavariables := ⟨4, fun i => match i.val with | 1 => 1 | _ => 0⟩
abbrev splitMetavariables : Metavariables := ⟨5, fun i => match i.val with | 1 | 2 => 1 | 3 => 2 | _ => 0⟩
abbrev betaMetavariables : Metavariables := ⟨6, fun i => match i.val with | 1 | 2 => 1 | 3 => 2 | _ => 0⟩
abbrev etaMetavariables : Metavariables := ⟨3, fun i => match i.val with | 1 => 1 | _ => 0⟩

private def family (A : Raw M Empty) (B : Raw M (Fin 1 ⊕ Empty)) :
    List (RelativeJudgment (extend eliminationSignature M)) :=
  [⟨0, .empty, .type A⟩, ⟨1, .extend .empty A, .type B⟩]

private def branchPair (A : Raw M Empty) (B : Raw M (Fin 1 ⊕ Empty)) :
    Raw M (Scope 2 Empty) :=
  Templates.pack (Expr.rename (Sum.inr ∘ Sum.inr) A)
    (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) B)
    (.var (.inr (.inl 0))) (.var (.inl 0))

private def branchType (A : Raw M Empty) (B D : Raw M (Fin 1 ⊕ Empty)) :
    Raw M (Scope 2 Empty) :=
  Elimination.instantiate (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) D) (branchPair A B)

private def motiveBranch (A : Raw M Empty) (B D : Raw M (Fin 1 ⊕ Empty))
    (e : Raw M (Fin 2 ⊕ Empty)) : List (RelativeJudgment (extend eliminationSignature M)) :=
  family A B ++ [⟨1, .extend .empty (Templates.S A B), .type D⟩,
    ⟨2, .extend (.extend .empty A) B, .term (Expr.rename flattenToNested e) (branchType A B D)⟩]

def formationRule : Rule eliminationSignature formationMetavariables :=
  let A := unzero (generic 0); let B := generic 1
  ⟨family A B, .type (Templates.S A B)⟩

def packRule : Rule eliminationSignature packMetavariables :=
  let A := unzero (generic 0); let B := generic 1
  let a := unzero (generic 2); let b := unzero (generic 3)
  ⟨family A B ++ [⟨0, .empty, .term a A⟩, ⟨0, .empty, .term b (Elimination.instantiate B a)⟩],
    .term (Templates.pack A B a b) (Templates.S A B)⟩

def splitRule : Rule eliminationSignature splitMetavariables :=
  let A := unzero (generic 0); let B := generic 1; let D := generic 2
  let e := generic 3; let p := unzero (generic 4)
  ⟨motiveBranch A B D e ++ [⟨0, .empty, .term p (Templates.S A B)⟩],
    .term (Templates.split A B D e p) (Elimination.instantiate D p)⟩

def betaRule : Rule eliminationSignature betaMetavariables :=
  let A := unzero (generic 0); let B := generic 1; let D := generic 2
  let e := generic 3; let a := unzero (generic 4); let b := unzero (generic 5)
  ⟨motiveBranch A B D e ++ [⟨0, .empty, .term a A⟩,
      ⟨0, .empty, .term b (Elimination.instantiate B a)⟩],
    .termEq (Templates.split A B D e (Templates.pack A B a b))
      (Expr.subst (Sum.elim (fun i : Fin 2 => if i.val = 0 then a else b) Expr.var) e)
      (Elimination.instantiate D (Templates.pack A B a b))⟩

def etaRule : Rule eliminationSignature etaMetavariables :=
  let A := unzero (generic 0); let B := generic 1; let p := unzero (generic 2)
  ⟨family A B ++ [⟨0, .empty, .term p (Templates.S A B)⟩],
    .termEq (Templates.pack A B (Templates.first A B p) (Templates.second A B p)) p (Templates.S A B)⟩
private theorem eval_reassociate (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (e : Raw M (Fin 2 ⊕ X)) :
    instantiate (Expr.lift (Expr.lift ρ)) ((a.weaken 1).weaken 1) (Expr.rename flattenToNested e) =
      Expr.rename flattenToNested (instantiate (Expr.lift ρ) (a.weaken 2) e) := by
  rw [instantiate_rename, ← Expr.subst_vars, instantiate_subst]
  congr 1
  · funext v
    cases v with
    | inl i => fin_cases i <;> rfl
    | inr v =>
      simp only [Function.comp_apply, flattenToNested, Expr.lift, Expr.subst_rename, Expr.rename_comp]
      rw [← Expr.subst_vars]
      rfl
  · funext m
    simp only [Assignment.weaken, Assignment.subst, Expr.subst_rename, Expr.rename_comp]
    rw [← Expr.subst_vars]
    congr 1
    funext v
    cases v <;> rfl

private theorem eval_doubleShift (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (B : Raw M (Fin 1 ⊕ X)) :
    instantiate (Expr.lift (Expr.lift (Expr.lift ρ))) (((a.weaken 1).weaken 1).weaken 1)
      (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) B) =
      Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) (instantiate (Expr.lift ρ) (a.weaken 1) B) := by
  rw [instantiate_rename, ← Expr.subst_vars, instantiate_subst]
  congr 1
  · funext x
    cases x with
    | inl => rfl
    | inr x => simp [Expr.lift, Expr.subst_vars, Expr.rename_comp, Function.comp_def]
  · funext i
    simp only [Assignment.subst, Assignment.weaken, Expr.subst_rename, Expr.rename_comp]
    rw [← Expr.subst_vars]
    congr 1
    funext x
    cases x <;> rfl

private theorem eval_branchType (a : Assignment eliminationSignature M V)
    (A : Raw M Empty) (B D : Raw M (Fin 1 ⊕ Empty)) :
    expression a 2 (branchType A B D) =
      DependentPairJudgments.branchType (expression a 0 A) (expression a 1 B) (expression a 1 D) := by
  dsimp only [expression, boundVariables, assignment, Scope]
  unfold branchType branchPair Elimination.instantiate
  dsimp only [Scope]
  rw [instantiate_bound, eval_doubleShift]
  simp only [eval_pack, instantiate]
  change Elimination.instantiate
    (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) (instantiate (Expr.lift Empty.elim) (a.weaken 1) D))
    (Elimination.pack (instantiate (Expr.lift (Expr.lift Empty.elim)) ((a.weaken 1).weaken 1) (Expr.rename (Sum.inr ∘ Sum.inr) A))
      (instantiate (Expr.lift (Expr.lift (Expr.lift Empty.elim))) (((a.weaken 1).weaken 1).weaken 1)
        (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) B))
      (.var (.inr (.inl 0))) (.var (.inl 0))) = _
  rw [eval_doubleShift]
  have ha : instantiate (Expr.lift (Expr.lift Empty.elim)) ((a.weaken 1).weaken 1)
      (Expr.rename (Sum.inr ∘ Sum.inr) A) = Expr.rename (Sum.inr ∘ Sum.inr) (instantiate Empty.elim a A) := by
    rw [← Expr.rename_comp, instantiate_weaken, instantiate_weaken, Expr.rename_comp]
  rw [ha]
  rfl

def formationAssignment (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    Assignment eliminationSignature formationMetavariables V :=
  Fin.cases (zero A) (Fin.cases B (fun i => nomatch i))

theorem formation_instance (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    formationRule.instantiate Γ (formationAssignment A B) = EliminationRule.schema (.formation Γ A B) := by
  have ha : instantiate Empty.elim (formationAssignment A B) (unzero (generic (M := formationMetavariables) 0)) = A := by
    have h := eval_generic_free (formationAssignment A B) 0 rfl
    change instantiate Empty.elim (formationAssignment A B) (unzero (generic 0)) = unzero (zero A) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  have hb : instantiate (Expr.lift Empty.elim) ((formationAssignment A B).weaken 1) (generic (M := formationMetavariables) 1) = B :=
    eval_generic_bound (formationAssignment A B) 1
  dsimp [List.map, formationRule, Rule.instantiate, family, RelativeJudgment.instantiate,
    Telescope.instantiate, form, expression, assignment, boundVariables, Scope,
    EliminationRule.schema, EliminationRule.family]
  simp only [eval_S, ha, hb]
  rfl

private theorem eval_instantiate (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (B : Raw M (Fin 1 ⊕ X)) (x : Raw M X) :
    instantiate ρ a (Elimination.instantiate B x) =
      Elimination.instantiate (instantiate (Expr.lift ρ) (a.weaken 1) B) (instantiate ρ a x) :=
  instantiate_bound ρ a B (fun _ => x)

private theorem eval_branchSubst (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (e : Raw M (Fin 2 ⊕ X)) (x y : Raw M X) :
    instantiate ρ a (Expr.subst (Sum.elim (fun i : Fin 2 => if i.val = 0 then x else y) Expr.var) e) =
      DependentPairJudgments.branchAt (instantiate (Expr.lift ρ) (a.weaken 2) e) (instantiate ρ a x) (instantiate ρ a y) := by
  rw [instantiate_bound]
  unfold DependentPairJudgments.branchAt
  congr 2
  funext i
  split <;> rfl

def packAssignment (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (a b : EExpr V) :
    Assignment eliminationSignature packMetavariables V :=
  Fin.cases (zero A) (Fin.cases B (Fin.cases (zero a) (Fin.cases (zero b) (fun i => nomatch i))))

theorem pack_instance (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
    (a b : EExpr V) :
    packRule.instantiate Γ (packAssignment A B a b) = EliminationRule.schema (.pack Γ A B a b) := by
  have h0 : instantiate Empty.elim (packAssignment A B a b) (unzero (generic (M := packMetavariables) 0)) = A := by
    have h := eval_generic_free (packAssignment A B a b) 0 rfl
    change instantiate Empty.elim (packAssignment A B a b) (unzero (generic 0)) = unzero (zero A) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  have h1 : instantiate (Expr.lift Empty.elim) ((packAssignment A B a b).weaken 1)
      (generic (M := packMetavariables) 1) = B := eval_generic_bound (packAssignment A B a b) 1
  have h2 : instantiate Empty.elim (packAssignment A B a b) (unzero (generic (M := packMetavariables) 2)) = a := by
    have h := eval_generic_free (packAssignment A B a b) 2 rfl
    change instantiate Empty.elim (packAssignment A B a b) (unzero (generic 2)) = unzero (zero a) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  have h3 : instantiate Empty.elim (packAssignment A B a b) (unzero (generic (M := packMetavariables) 3)) = b := by
    have h := eval_generic_free (packAssignment A B a b) 3 rfl
    change instantiate Empty.elim (packAssignment A B a b) (unzero (generic 3)) = unzero (zero b) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  simp only [packRule, Rule.instantiate, family, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, RelativeJudgment.instantiate, Telescope.instantiate, form]
  dsimp only [expression, assignment, boundVariables, Scope]
  simp only [eval_S, eval_pack, eval_instantiate, h0, h1, h2, h3]
  rfl

def splitAssignment (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) (p : EExpr V) :
    Assignment eliminationSignature splitMetavariables V :=
  Fin.cases (zero A) (Fin.cases B (Fin.cases D (Fin.cases e (Fin.cases (zero p) (fun i => nomatch i)))))

theorem split_instance (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
    (D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) (p : EExpr V) :
    splitRule.instantiate Γ (splitAssignment A B D e p) = EliminationRule.schema (.split Γ A B D e p) := by
  have h0 : instantiate Empty.elim (splitAssignment A B D e p) (unzero (generic (M := splitMetavariables) 0)) = A := by
    have h := eval_generic_free (splitAssignment A B D e p) 0 rfl
    change instantiate Empty.elim (splitAssignment A B D e p) (unzero (generic 0)) = unzero (zero A) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  have h1 : instantiate (Expr.lift Empty.elim) ((splitAssignment A B D e p).weaken 1)
      (generic (M := splitMetavariables) 1) = B := eval_generic_bound (splitAssignment A B D e p) 1
  have h2 : instantiate (Expr.lift Empty.elim) ((splitAssignment A B D e p).weaken 1)
      (generic (M := splitMetavariables) 2) = D := eval_generic_bound (splitAssignment A B D e p) 2
  have h3 : instantiate (Expr.lift Empty.elim) ((splitAssignment A B D e p).weaken 2)
      (generic (M := splitMetavariables) 3) = e := eval_generic_bound (splitAssignment A B D e p) 3
  have h4 : instantiate Empty.elim (splitAssignment A B D e p) (unzero (generic (M := splitMetavariables) 4)) = p := by
    have h := eval_generic_free (splitAssignment A B D e p) 4 rfl
    change instantiate Empty.elim (splitAssignment A B D e p) (unzero (generic 4)) = unzero (zero p) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  simp only [splitRule, Rule.instantiate, motiveBranch, family, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, RelativeJudgment.instantiate, Telescope.instantiate, form]
  simp only [eval_branchType]
  dsimp only [expression, assignment, boundVariables, Scope]
  simp only [eval_S, eval_split, eval_instantiate, eval_reassociate, h0, h1, h2, h3, h4]
  rfl

def betaAssignment (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) (a b : EExpr V) :
    Assignment eliminationSignature betaMetavariables V :=
  Fin.cases (zero A) (Fin.cases B (Fin.cases D (Fin.cases e (Fin.cases (zero a) (Fin.cases (zero b) (fun i => nomatch i))))))

theorem beta_instance (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
    (D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) (a b : EExpr V) :
    betaRule.instantiate Γ (betaAssignment A B D e a b) = EliminationRule.schema (.splitBeta Γ A B D e a b) := by
  have h0 : instantiate Empty.elim (betaAssignment A B D e a b) (unzero (generic (M := betaMetavariables) 0)) = A := by
    have h := eval_generic_free (betaAssignment A B D e a b) 0 rfl
    change instantiate Empty.elim (betaAssignment A B D e a b) (unzero (generic 0)) = unzero (zero A) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  have h1 : instantiate (Expr.lift Empty.elim) ((betaAssignment A B D e a b).weaken 1)
      (generic (M := betaMetavariables) 1) = B := eval_generic_bound (betaAssignment A B D e a b) 1
  have h2 : instantiate (Expr.lift Empty.elim) ((betaAssignment A B D e a b).weaken 1)
      (generic (M := betaMetavariables) 2) = D := eval_generic_bound (betaAssignment A B D e a b) 2
  have h3 : instantiate (Expr.lift Empty.elim) ((betaAssignment A B D e a b).weaken 2)
      (generic (M := betaMetavariables) 3) = e := eval_generic_bound (betaAssignment A B D e a b) 3
  have h4 : instantiate Empty.elim (betaAssignment A B D e a b) (unzero (generic (M := betaMetavariables) 4)) = a := by
    have h := eval_generic_free (betaAssignment A B D e a b) 4 rfl
    change instantiate Empty.elim (betaAssignment A B D e a b) (unzero (generic 4)) = unzero (zero a) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  have h5 : instantiate Empty.elim (betaAssignment A B D e a b) (unzero (generic (M := betaMetavariables) 5)) = b := by
    have h := eval_generic_free (betaAssignment A B D e a b) 5 rfl
    change instantiate Empty.elim (betaAssignment A B D e a b) (unzero (generic 5)) = unzero (zero b) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  simp only [betaRule, Rule.instantiate, motiveBranch, family, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, RelativeJudgment.instantiate, Telescope.instantiate, form]
  simp only [eval_branchType]
  dsimp only [expression, assignment, boundVariables, Scope]
  simp only [eval_S, eval_pack, eval_split, eval_instantiate, eval_branchSubst, eval_reassociate, h0, h1, h2, h3, h4, h5]
  rfl

def etaAssignment (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (p : EExpr V) :
    Assignment eliminationSignature etaMetavariables V :=
  Fin.cases (zero A) (Fin.cases B (Fin.cases (zero p) (fun i => nomatch i)))

theorem eta_instance (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
    (p : EExpr V) :
    etaRule.instantiate Γ (etaAssignment A B p) = EliminationRule.schema (.eta Γ A B p) := by
  have h0 : instantiate Empty.elim (etaAssignment A B p) (unzero (generic (M := etaMetavariables) 0)) = A := by
    have h := eval_generic_free (etaAssignment A B p) 0 rfl
    change instantiate Empty.elim (etaAssignment A B p) (unzero (generic 0)) = unzero (zero A) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  have h1 : instantiate (Expr.lift Empty.elim) ((etaAssignment A B p).weaken 1)
      (generic (M := etaMetavariables) 1) = B := eval_generic_bound (etaAssignment A B p) 1
  have h2 : instantiate Empty.elim (etaAssignment A B p) (unzero (generic (M := etaMetavariables) 2)) = p := by
    have h := eval_generic_free (etaAssignment A B p) 2 rfl
    change instantiate Empty.elim (etaAssignment A B p) (unzero (generic 2)) = unzero (zero p) at h
    simpa only [unzero, zero, Expr.rename_comp, Function.comp_def, Sum.elim_inr, Expr.rename_id] using h
  simp only [etaRule, Rule.instantiate, family, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, RelativeJudgment.instantiate, Telescope.instantiate, form]
  dsimp only [expression, assignment, boundVariables, Scope]
  simp only [eval_S, eval_pack, eval_first, eval_second, h0, h1, h2]
  rfl

/-- Every contextual eliminator primitive is an instance of an empty-context rule. -/
structure Encoding (r : EliminationRule) where
  metas : Metavariables
  rule : Rule eliminationSignature metas
  values : Assignment eliminationSignature metas (EliminationRule.schema r).conclusion.Scope
  instance_eq : rule.instantiate (EliminationRule.schema r).conclusion.context values = EliminationRule.schema r

def encode (r : EliminationRule) : Encoding r := by
  cases r with
  | formation Γ A B => exact ⟨formationMetavariables, formationRule, formationAssignment A B, formation_instance Γ A B⟩
  | pack Γ A B a b => exact ⟨packMetavariables, packRule, packAssignment A B a b, pack_instance Γ A B a b⟩
  | split Γ A B D e p => exact ⟨splitMetavariables, splitRule, splitAssignment A B D e p, split_instance Γ A B D e p⟩
  | splitBeta Γ A B D e a b => exact ⟨betaMetavariables, betaRule, betaAssignment A B D e a b, beta_instance Γ A B D e a b⟩
  | eta Γ A B p => exact ⟨etaMetavariables, etaRule, etaAssignment A B p, eta_instance Γ A B p⟩

end SquareKit.DependentEliminationSequentialRules
