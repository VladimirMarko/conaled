import SquareKit.DependentPairJudgments

/-! The independent dependent-eliminator presentation and its rule boundaries. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations
open Elimination

/-- Two simultaneously bound branch variables become two successive telescope entries.
The first variable is x and the second y; y is the newest context entry. -/
def flattenToNested : Fin 2 ⊕ V → Fin 1 ⊕ (Fin 1 ⊕ V)
  | .inl i => if i.val = 0 then .inr (.inl 0) else .inl 0
  | .inr v => .inr (.inr v)

def branchContext (Γ : Context eliminationSignature V) (A : EExpr V)
    (B : EExpr (Fin 1 ⊕ V)) := (Γ.extend A).extend B

def branchPair (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) : EExpr (Fin 1 ⊕ (Fin 1 ⊕ V)) :=
  pack (Expr.rename (Sum.inr ∘ Sum.inr) A)
    (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) B)
    (.var (.inr (.inl 0))) (.var (.inl 0))

def branchType (A : EExpr V) (B D : EExpr (Fin 1 ⊕ V)) : EExpr (Fin 1 ⊕ (Fin 1 ⊕ V)) :=
  instantiate (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) D) (branchPair A B)

def branchAt (e : EExpr (Fin 2 ⊕ V)) (a b : EExpr V) : EExpr V :=
  Expr.subst (Sum.elim (fun i => if i.val = 0 then a else b) Expr.var) e

inductive EliminationRule where
  | formation {V} (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
  | pack {V} (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
      (a b : EExpr V)
  | split {V} (Γ : Context eliminationSignature V) (A : EExpr V)
      (B D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) (p : EExpr V)
  | splitBeta {V} (Γ : Context eliminationSignature V) (A : EExpr V)
      (B D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) (a b : EExpr V)
  | eta {V} (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
      (p : EExpr V)

namespace EliminationRule
open Judgment

def family (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :=
  [ctx Γ, type Γ A, type (.extend Γ A) B]

def motiveBranch (Γ : Context eliminationSignature V) (A : EExpr V)
    (B D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) :=
  family Γ A B ++ [type (.extend Γ (S A B)) D,
    term (branchContext Γ A B) (Expr.rename flattenToNested e) (branchType A B D)]

def schema : EliminationRule → Schema eliminationSignature
  | .formation Γ A B => ⟨family Γ A B, type Γ (S A B)⟩
  | .pack Γ A B a b =>
      ⟨family Γ A B ++ [term Γ a A, term Γ b (instantiate B a)], term Γ (Elimination.pack A B a b) (S A B)⟩
  | .split Γ A B D e p =>
      ⟨motiveBranch Γ A B D e ++ [term Γ p (S A B)],
        term Γ (Elimination.split A B D e p) (instantiate D p)⟩
  | .splitBeta Γ A B D e a b =>
      ⟨motiveBranch Γ A B D e ++ [term Γ a A, term Γ b (instantiate B a)],
        termEq Γ (Elimination.split A B D e (Elimination.pack A B a b)) (branchAt e a b)
          (instantiate D (Elimination.pack A B a b))⟩
  | .eta Γ A B p =>
      ⟨family Γ A B ++ [term Γ p (S A B)],
        termEq Γ (Elimination.pack A B (first A B p) (second A B p)) p (S A B)⟩
end EliminationRule

def eliminationRules := rulesOf EliminationRule.schema

@[simp] theorem instantiate_constant (A p : Expr T V) :
    instantiate (Expr.rename Sum.inr A) p = A := by
  simp only [instantiate, Expr.subst_rename]
  exact Expr.subst_id A

@[simp] theorem first_branch_type (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    branchType A B (Expr.rename Sum.inr A) = Expr.rename (Sum.inr ∘ Sum.inr) A := by
  simp only [branchType, Expr.rename_comp, instantiate, Expr.subst_rename]
  exact Expr.subst_vars (Sum.inr ∘ Sum.inr) A

@[simp] theorem branch_first (a b : EExpr V) : branchAt (.var (.inl 0)) a b = a := rfl
@[simp] theorem branch_second (a b : EExpr V) : branchAt (.var (.inl 1)) a b = b := rfl

@[simp] theorem branch_B_at_x (B : EExpr (Fin 1 ⊕ V)) :
    instantiate (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) B)
      (.var (.inr (.inl 0))) = Expr.rename (Sum.inr (α := Fin 1)) B := by
  simp only [instantiate, Expr.subst_rename]
  rw [← Expr.subst_vars]
  congr 1
  funext v
  cases v with
  | inl i => have : i = 0 := Subsingleton.elim _ _; subst i; rfl
  | inr => rfl

def secondMotive (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) : EExpr (Fin 1 ⊕ V) :=
  instantiate (Expr.rename (Sum.map id Sum.inr) B)
    (first (Expr.rename Sum.inr A) (Expr.rename (Sum.map id Sum.inr) B) (.var (.inl 0)))

@[simp] theorem secondMotive_at (A p : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    instantiate (secondMotive A B) p = instantiate B (first A B p) := by
  change Expr.subst (Sum.elim (fun _ : Fin 1 => p) Expr.var)
    (instantiate (Expr.rename (Sum.map id Sum.inr) B)
      (first (Expr.rename Sum.inr A) (Expr.rename (Sum.map id Sum.inr) B) (.var (.inl 0)))) = _
  rw [subst_instantiate, subst_first]
  simp only [Expr.subst_rename]
  have h : Expr.lift (Sum.elim (fun _ : Fin 1 => p) Expr.var) ∘ Sum.map id Sum.inr =
      (Expr.var : Fin 1 ⊕ V → _) := by funext v; cases v <;> rfl
  have hc : Sum.elim (fun _ : Fin 1 => p) Expr.var ∘ Sum.inr = (Expr.var : V → _) := rfl
  rw [h, hc, Expr.subst_id, Expr.subst_id]
  rfl

def Eη := closedRules EliminationRule.schema

namespace EDerivation
open Judgment
variable {H : Judgment eliminationSignature → Type} {Γ : Context eliminationSignature V}
  {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)}

def extend (hΓ : Derivation Eη H (ctx Γ)) (hA : Derivation Eη H (type Γ A)) :
    Derivation Eη H (ctx (Γ.extend A)) :=
  Derivation.rule (R := Eη) (.inl (.extend Γ A)) (Fin.cases hΓ (Fin.cases hA (fun i => nomatch i)))

def variableTerm (hΓ : Derivation Eη H (ctx Γ)) (v : V) :
    Derivation Eη H (term Γ (.var v) (Γ.lookup v)) :=
  Derivation.rule (R := Eη) (.inl (.variable Γ v)) (Fin.cases hΓ (fun i => nomatch i))

def weaken (φ : Form eliminationSignature V) (hΓ : Derivation Eη H (ctx Γ))
    (hA : Derivation Eη H (type Γ A)) (hφ : Derivation Eη H ⟨_, Γ, φ⟩) :
    Derivation Eη H ⟨_, Γ.extend A, φ.rename Sum.inr⟩ :=
  Derivation.rule (R := Eη) (.inl (.weaken Γ A φ)) (Fin.cases hΓ (Fin.cases hA (Fin.cases hφ (fun i => nomatch i))))

def formation (hΓ : Derivation Eη H (ctx Γ)) (hA : Derivation Eη H (type Γ A))
    (hB : Derivation Eη H (type (Γ.extend A) B)) : Derivation Eη H (type Γ (S A B)) :=
  Derivation.rule (R := Eη) (.inr (.formation Γ A B)) (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (fun i => nomatch i))))

/-- The first projection is derived from split, not added as a primitive rule. -/
def first (hΓ : Derivation Eη H (ctx Γ)) (hA : Derivation Eη H (type Γ A))
    (hB : Derivation Eη H (type (Γ.extend A) B)) (p : EExpr V)
    (hp : Derivation Eη H (term Γ p (S A B))) :
    Derivation Eη H (term Γ (Elimination.first A B p) A) := by
  have hP := formation hΓ hA hB
  have hΓA := extend hΓ hA
  have hΓAB := extend hΓA hB
  have hD : Derivation Eη H (type (Γ.extend (S A B)) (Expr.rename Sum.inr A)) :=
    weaken (.type A) hΓ hP hA
  have hx : Derivation Eη H (term (branchContext Γ A B)
      (Expr.rename flattenToNested (.var (.inl 0)))
      (branchType A B (Expr.rename Sum.inr A))) := by
    rw [first_branch_type]
    change Derivation Eη H (term ((Γ.extend A).extend B)
      (.var (.inr (.inl 0))) (Expr.rename (Sum.inr ∘ Sum.inr) A))
    simpa only [Context.lookup, Expr.rename_comp]
      using variableTerm hΓAB (Sum.inr (Sum.inl (0 : Fin 1)))
  have hs : Derivation Eη H (term Γ
      (Elimination.split A B (Expr.rename Sum.inr A) (.var (.inl 0)) p)
      (instantiate (Expr.rename Sum.inr A) p)) :=
    Derivation.rule (R := Eη) (.inr (.split Γ A B _ _ p))
      (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hD
        (Fin.cases hx (Fin.cases hp (fun i => nomatch i)))))))
  simpa only [instantiate_constant, Elimination.first] using hs
def pack (hΓ : Derivation Eη H (ctx Γ)) (hA : Derivation Eη H (type Γ A))
    (hB : Derivation Eη H (type (Γ.extend A) B)) (a b : EExpr V)
    (ha : Derivation Eη H (term Γ a A)) (hb : Derivation Eη H (term Γ b (instantiate B a))) :
    Derivation Eη H (term Γ (Elimination.pack A B a b) (S A B)) :=
  Derivation.rule (R := Eη) (.inr (.pack Γ A B a b))
    (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases ha (Fin.cases hb (fun i => nomatch i))))))

/-- The first beta certificate is a split-beta proof with the variable branch. -/
def firstBeta (hΓ : Derivation Eη H (ctx Γ)) (hA : Derivation Eη H (type Γ A))
    (hB : Derivation Eη H (type (Γ.extend A) B)) (a b : EExpr V)
    (ha : Derivation Eη H (term Γ a A)) (hb : Derivation Eη H (term Γ b (instantiate B a))) :
    Derivation Eη H (termEq Γ (Elimination.first A B (Elimination.pack A B a b)) a A) := by
  have hP := formation hΓ hA hB
  have hΓAB := extend (extend hΓ hA) hB
  have hD : Derivation Eη H (type (Γ.extend (S A B)) (Expr.rename Sum.inr A)) :=
    weaken (.type A) hΓ hP hA
  have hx : Derivation Eη H (term (branchContext Γ A B)
      (Expr.rename flattenToNested (.var (.inl 0)))
      (branchType A B (Expr.rename Sum.inr A))) := by
    rw [first_branch_type]
    change Derivation Eη H (term ((Γ.extend A).extend B)
      (.var (.inr (.inl 0))) (Expr.rename (Sum.inr ∘ Sum.inr) A))
    simpa only [Context.lookup, Expr.rename_comp]
      using variableTerm hΓAB (Sum.inr (Sum.inl (0 : Fin 1)))
  have hs : Derivation Eη H (termEq Γ
      (Elimination.split A B (Expr.rename Sum.inr A) (.var (.inl 0)) (Elimination.pack A B a b))
      (branchAt (.var (.inl 0)) a b)
      (instantiate (Expr.rename Sum.inr A) (Elimination.pack A B a b))) :=
    Derivation.rule (R := Eη) (.inr (.splitBeta Γ A B _ _ a b))
      (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hD
        (Fin.cases hx (Fin.cases ha (Fin.cases hb (fun i => nomatch i))))))))
  simpa only [instantiate_constant, branch_first, Elimination.first] using hs
end EDerivation

end SquareKit.DependentPairJudgments
