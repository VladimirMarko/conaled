import SquareKit.DependentSequentialRules

/-! Closed sequential presentations of all projection-pair primitive rules.
Their ambient instances recover the independently declared contextual schemas. -/
namespace SquareKit.DependentProjectionSequentialRules
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments
open DependentSequentialRules

abbrev Raw (M : Metavariables) := Expr (extend projectionSignature M)

namespace Raw
variable {M : Metavariables} {X V : Type}

def P (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) : Raw M X :=
  .app (.inl .P) (Fin.cases (zero A) (Fin.cases B (fun i => nomatch i)))
def pair (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (a b : Raw M X) : Raw M X :=
  .app (.inl .pair) (Fin.cases (zero A) (Fin.cases B
    (Fin.cases (zero a) (Fin.cases (zero b) (fun i => nomatch i)))))
def fst (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) : Raw M X :=
  .app (.inl .fst) (Fin.cases (zero A) (Fin.cases B (Fin.cases (zero p) (fun i => nomatch i))))
def snd (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) : Raw M X :=
  .app (.inl .snd) (Fin.cases (zero A) (Fin.cases B (Fin.cases (zero p) (fun i => nomatch i))))

@[simp] theorem eval_P (ρ : X → PExpr V) (a : Assignment projectionSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) :
    instantiate ρ a (P A B) = Projection.P (instantiate ρ a A)
      (instantiate (Expr.lift ρ) (a.weaken 1) B) := by
  simp only [P, instantiate, Projection.P]
  congr 1
  funext i
  change Fin 2 at i
  fin_cases i <;> first | exact instantiate_weaken ρ a _ | rfl

@[simp] theorem eval_pair (ρ : X → PExpr V) (a : Assignment projectionSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (x y : Raw M X) :
    instantiate ρ a (pair A B x y) = Projection.pair (instantiate ρ a A)
      (instantiate (Expr.lift ρ) (a.weaken 1) B) (instantiate ρ a x) (instantiate ρ a y) := by
  simp only [pair, instantiate, Projection.pair]
  congr 1
  funext i
  change Fin 4 at i
  fin_cases i <;> first | exact instantiate_weaken ρ a _ | rfl

@[simp] theorem eval_fst (ρ : X → PExpr V) (a : Assignment projectionSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) :
    instantiate ρ a (fst A B p) = Projection.fst (instantiate ρ a A)
      (instantiate (Expr.lift ρ) (a.weaken 1) B) (instantiate ρ a p) := by
  simp only [fst, instantiate, Projection.fst]
  congr 1
  funext i
  change Fin 3 at i
  fin_cases i <;> first | exact instantiate_weaken ρ a _ | rfl

@[simp] theorem eval_snd (ρ : X → PExpr V) (a : Assignment projectionSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) :
    instantiate ρ a (snd A B p) = Projection.snd (instantiate ρ a A)
      (instantiate (Expr.lift ρ) (a.weaken 1) B) (instantiate ρ a p) := by
  simp only [snd, instantiate, Projection.snd]
  congr 1
  funext i
  change Fin 3 at i
  fin_cases i <;> first | exact instantiate_weaken ρ a _ | rfl

@[simp] theorem eval_apply (ρ : X → PExpr V) (a : Assignment projectionSignature M V)
    (B : Raw M (Fin 1 ⊕ X)) (x : Raw M X) :
    instantiate ρ a (Elimination.instantiate B x) =
      Elimination.instantiate (instantiate (Expr.lift ρ) (a.weaken 1) B)
        (instantiate ρ a x) := instantiate_bound ρ a B (fun _ => x)

end Raw

abbrev familyMetas := symbolMetavariables projectionSignature .P
abbrev componentMetas := symbolMetavariables projectionSignature .pair
abbrev argumentMetas := symbolMetavariables projectionSignature .fst

def family {M : Metavariables} (A : Raw M Empty) (B : Raw M (Fin 1 ⊕ Empty)) :
    List (RelativeJudgment (extend projectionSignature M)) :=
  [⟨0, .empty, .type A⟩, ⟨1, .extend .empty A, .type B⟩]

def components {M : Metavariables} (A : Raw M Empty) (B : Raw M (Fin 1 ⊕ Empty))
    (a b : Raw M Empty) : List (RelativeJudgment (extend projectionSignature M)) :=
  family A B ++ [⟨0, .empty, .term a A⟩,
    ⟨0, .empty, .term b (Elimination.instantiate B a)⟩]

def argument {M : Metavariables} (A : Raw M Empty) (B : Raw M (Fin 1 ⊕ Empty))
    (p : Raw M Empty) : List (RelativeJudgment (extend projectionSignature M)) :=
  family A B ++ [⟨0, .empty, .term p (Raw.P A B)⟩]

def formation : Rule projectionSignature familyMetas :=
  let A := unzero (metaApplication 0)
  let B := metaApplication 1
  ⟨family A B, .type (Raw.P A B)⟩

inductive ComponentRule where | pair | firstBeta | secondBeta
inductive ArgumentRule where | first | second | eta

def componentRule (r : ComponentRule) : Rule projectionSignature componentMetas :=
  let A := unzero (metaApplication 0)
  let B := metaApplication 1
  let a := unzero (metaApplication 2)
  let b := unzero (metaApplication 3)
  ⟨components A B a b, match r with
    | .pair => .term (Raw.pair A B a b) (Raw.P A B)
    | .firstBeta => .termEq (Raw.fst A B (Raw.pair A B a b)) a A
    | .secondBeta => .termEq (Raw.snd A B (Raw.pair A B a b)) b (Elimination.instantiate B a)⟩

def argumentRule (r : ArgumentRule) : Rule projectionSignature argumentMetas :=
  let A := unzero (metaApplication 0)
  let B := metaApplication 1
  let p := unzero (metaApplication 2)
  ⟨argument A B p, match r with
    | .first => .term (Raw.fst A B p) A
    | .second => .term (Raw.snd A B p) (Elimination.instantiate B (Raw.fst A B p))
    | .eta => .termEq (Raw.pair A B (Raw.fst A B p) (Raw.snd A B p)) p (Raw.P A B)⟩

def familyAssignment (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) :
    Assignment projectionSignature familyMetas V :=
  Fin.cases (zero A) (Fin.cases B (fun i => nomatch i))
def componentAssignment (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (a b : PExpr V) :
    Assignment projectionSignature componentMetas V :=
  Fin.cases (zero A) (Fin.cases B (Fin.cases (zero a) (Fin.cases (zero b) (fun i => nomatch i))))
def argumentAssignment (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (p : PExpr V) :
    Assignment projectionSignature argumentMetas V :=
  Fin.cases (zero A) (Fin.cases B (Fin.cases (zero p) (fun i => nomatch i)))

@[simp] theorem eval_unzero_meta {S : Signature} {M : Metavariables}
    (a : Assignment S M V) (m : Fin M.count) (h : M.arguments m = 0) :
    instantiate Empty.elim a
      (Expr.rename (Sum.elim (fun i => (h ▸ i).elim0) id) (metaApplication m)) =
      Expr.rename (Sum.elim (fun i => (h ▸ i).elim0) id) (a m) := by
  simp only [instantiate_rename, metaApplication, instantiate]
  rw [← Expr.subst_vars]
  congr 1
  funext v
  cases v with
  | inl i =>
    change Fin (M.arguments m) at i
    exact (h ▸ i).elim0
  | inr => rfl

theorem instantiate_formation {eta : Bool} (Γ : Context projectionSignature V)
    (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) :
    formation.instantiate Γ (familyAssignment A B) =
      ProjectionRule.schema (.formation (eta := eta) Γ A B) := by
  have ha : instantiate Empty.elim (familyAssignment A B)
      (unzero (metaApplication (M := familyMetas) 0)) = A := by
    have h := eval_unzero_meta (familyAssignment A B) 0 rfl
    change instantiate Empty.elim (familyAssignment A B) (unzero (metaApplication 0)) = unzero (zero A) at h
    simpa only [unzero_zero] using h
  have hb : instantiate (Expr.lift (n := 1) Empty.elim)
      ((familyAssignment A B).weaken 1) (metaApplication 1) = B :=
    instantiate_metaApplication (familyAssignment A B) 1
  dsimp [formation, Rule.instantiate, family, List.map,
    RelativeJudgment.instantiate, Telescope.instantiate, form, expression,
    assignment, boundVariables, Scope]
  simp only [Raw.eval_P, ha, hb]
  rfl

def ComponentRule.contextual {eta : Bool} (r : ComponentRule)
    (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (a b : PExpr V) : ProjectionRule eta :=
  match r with
  | .pair => .pair Γ A B a b
  | .firstBeta => .firstBeta Γ A B a b
  | .secondBeta => .secondBeta Γ A B a b

theorem instantiate_component {eta : Bool} (r : ComponentRule)
    (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (a b : PExpr V) :
    (componentRule r).instantiate Γ (componentAssignment A B a b) =
      ProjectionRule.schema (r.contextual (eta := eta) Γ A B a b) := by
  have ha : instantiate Empty.elim (componentAssignment A B a b)
      (unzero (metaApplication (M := componentMetas) 0)) = A := by
    have h := eval_unzero_meta (componentAssignment A B a b) 0 rfl
    change instantiate Empty.elim (componentAssignment A B a b)
      (unzero (metaApplication 0)) = unzero (zero A) at h
    simpa only [unzero_zero] using h
  have hb : instantiate (Expr.lift (n := 1) Empty.elim)
      ((componentAssignment A B a b).weaken 1) (metaApplication 1) = B :=
    instantiate_metaApplication (componentAssignment A B a b) 1
  have hx : instantiate Empty.elim (componentAssignment A B a b)
      (unzero (metaApplication (M := componentMetas) 2)) = a := by
    have h := eval_unzero_meta (componentAssignment A B a b) 2 rfl
    change instantiate Empty.elim (componentAssignment A B a b)
      (unzero (metaApplication 2)) = unzero (zero a) at h
    simpa only [unzero_zero] using h
  have hy : instantiate Empty.elim (componentAssignment A B a b)
      (unzero (metaApplication (M := componentMetas) 3)) = b := by
    have h := eval_unzero_meta (componentAssignment A B a b) 3 rfl
    change instantiate Empty.elim (componentAssignment A B a b)
      (unzero (metaApplication 3)) = unzero (zero b) at h
    simpa only [unzero_zero] using h
  cases r <;>
    dsimp [componentRule, Rule.instantiate, components, family, List.map,
      RelativeJudgment.instantiate, Telescope.instantiate, form, expression,
      assignment, boundVariables, Scope] <;>
    simp only [Raw.eval_P, Raw.eval_pair, Raw.eval_fst, Raw.eval_snd,
      Raw.eval_apply, ha, hb, hx, hy] <;> rfl

def ArgumentRule.contextual (r : ArgumentRule)
    (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (p : PExpr V) : ProjectionRule true :=
  match r with
  | .first => .first Γ A B p
  | .second => .second Γ A B p
  | .eta => .eta rfl Γ A B p

theorem instantiate_argument (r : ArgumentRule)
    (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (p : PExpr V) :
    (argumentRule r).instantiate Γ (argumentAssignment A B p) =
      ProjectionRule.schema (r.contextual Γ A B p) := by
  have ha : instantiate Empty.elim (argumentAssignment A B p)
      (unzero (metaApplication (M := argumentMetas) 0)) = A := by
    have h := eval_unzero_meta (argumentAssignment A B p) 0 rfl
    change instantiate Empty.elim (argumentAssignment A B p)
      (unzero (metaApplication 0)) = unzero (zero A) at h
    simpa only [unzero_zero] using h
  have hb : instantiate (Expr.lift (n := 1) Empty.elim)
      ((argumentAssignment A B p).weaken 1) (metaApplication 1) = B :=
    instantiate_metaApplication (argumentAssignment A B p) 1
  have hp : instantiate Empty.elim (argumentAssignment A B p)
      (unzero (metaApplication (M := argumentMetas) 2)) = p := by
    have h := eval_unzero_meta (argumentAssignment A B p) 2 rfl
    change instantiate Empty.elim (argumentAssignment A B p)
      (unzero (metaApplication 2)) = unzero (zero p) at h
    simpa only [unzero_zero] using h
  cases r <;>
    dsimp [argumentRule, Rule.instantiate, argument, family, List.map,
      RelativeJudgment.instantiate, Telescope.instantiate, form, expression,
      assignment, boundVariables, Scope] <;>
    simp only [Raw.eval_P, Raw.eval_pair, Raw.eval_fst, Raw.eval_snd,
      Raw.eval_apply, ha, hb, hp] <;> rfl

/-- Each contextual primitive is an instance of a closed rule. This records
the actual metavariable assignment, not an assumed correspondence property. -/
structure Encoding {eta : Bool} (r : ProjectionRule eta) where
  metas : Metavariables
  rule : Rule projectionSignature metas
  values : Assignment projectionSignature metas (ProjectionRule.schema r).conclusion.Scope
  instance_eq : rule.instantiate (ProjectionRule.schema r).conclusion.context values =
    ProjectionRule.schema r

def encode {eta : Bool} (r : ProjectionRule eta) : Encoding r := by
  cases r with
  | formation Γ A B =>
    exact ⟨familyMetas, formation, familyAssignment A B, instantiate_formation Γ A B⟩
  | pair Γ A B a b =>
    exact ⟨componentMetas, componentRule .pair, componentAssignment A B a b,
      instantiate_component .pair Γ A B a b⟩
  | first Γ A B p =>
    exact ⟨argumentMetas, argumentRule .first, argumentAssignment A B p,
      instantiate_argument .first Γ A B p⟩
  | second Γ A B p =>
    exact ⟨argumentMetas, argumentRule .second, argumentAssignment A B p,
      instantiate_argument .second Γ A B p⟩
  | firstBeta Γ A B a b =>
    exact ⟨componentMetas, componentRule .firstBeta, componentAssignment A B a b,
      instantiate_component .firstBeta Γ A B a b⟩
  | secondBeta Γ A B a b =>
    exact ⟨componentMetas, componentRule .secondBeta, componentAssignment A B a b,
      instantiate_component .secondBeta Γ A B a b⟩
  | eta allowed Γ A B p =>
    exact ⟨argumentMetas, argumentRule .eta, argumentAssignment A B p,
      instantiate_argument .eta Γ A B p⟩

end SquareKit.DependentProjectionSequentialRules
