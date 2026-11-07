import Mathlib.Data.Fintype.Fin
import SquareKit.DependentTheoryMaps
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Raw pair presentation templates. Bound variables use finite scopes. -/
namespace SquareKit.DependentPairPresentations
open DependentTheoryMaps

inductive Declaration where
  | N | B | C | s | d | t | u
  deriving DecidableEq

abbrev Declaration.bindings : Declaration → List Nat
  | .N => []
  | .C => [0, 0]
  | _ => [0]

inductive ProjectionSymbol where
  | P | pair | fst | snd | declaration (decl : Declaration)
  deriving DecidableEq

abbrev ProjectionSymbol.bindings : ProjectionSymbol → List Nat
  | .P => [0, 1]
  | .pair => [0, 1, 0, 0]
  | .fst | .snd => [0, 1, 0]
  | .declaration decl => decl.bindings

inductive EliminationSymbol where
  | S | pack | split | declaration (decl : Declaration)
  deriving DecidableEq

abbrev EliminationSymbol.bindings : EliminationSymbol → List Nat
  | .S => [0, 1]
  | .pack => [0, 1, 0, 0]
  | .split => [0, 1, 1, 2, 0]
  | .declaration decl => decl.bindings

abbrev fromBindings (S : Type) (binding : S → List Nat) : Signature where
  Symbol := S
  arity := fun s => (binding s).length
  binds := fun s i => (binding s).get i

abbrev projectionSignature := fromBindings ProjectionSymbol ProjectionSymbol.bindings
abbrev eliminationSignature := fromBindings EliminationSymbol EliminationSymbol.bindings

abbrev PExpr := Expr projectionSignature
abbrev EExpr := Expr eliminationSignature

def zero (e : Expr S V) : Expr S (Fin 0 ⊕ V) := Expr.rename Sum.inr e

def unzero (e : Expr S (Fin 0 ⊕ V)) : Expr S V :=
  Expr.rename (Sum.elim Fin.elim0 id) e

@[simp] theorem unzero_zero (e : Expr S V) : unzero (zero e) = e := by
  simp only [unzero, zero, Expr.rename_comp]
  exact Expr.rename_id e

@[simp] theorem zero_unzero (e : Expr S (Fin 0 ⊕ V)) : zero (unzero e) = e := by
  simp only [zero, unzero, Expr.rename_comp]
  convert Expr.rename_id e using 1
  congr 1
  funext v
  cases v with
  | inl v => exact Fin.elim0 v
  | inr => rfl

namespace Projection
variable {V : Type}

def P (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) : PExpr V :=
  .app .P (Fin.cases (zero A) (Fin.cases B (fun i => nomatch i)))

def pair (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (a b : PExpr V) : PExpr V :=
  .app .pair (Fin.cases (zero A) (Fin.cases B
    (Fin.cases (zero a) (Fin.cases (zero b) (fun i => nomatch i)))))

def fst (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (p : PExpr V) : PExpr V :=
  .app .fst (Fin.cases (zero A) (Fin.cases B (Fin.cases (zero p) (fun i => nomatch i))))

def snd (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (p : PExpr V) : PExpr V :=
  .app .snd (Fin.cases (zero A) (Fin.cases B (Fin.cases (zero p) (fun i => nomatch i))))
end Projection

namespace Elimination
variable {V : Type}

def S (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) : EExpr V :=
  .app .S (Fin.cases (zero A) (Fin.cases B (fun i => nomatch i)))

def pack (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (a b : EExpr V) : EExpr V :=
  .app .pack (Fin.cases (zero A) (Fin.cases B
    (Fin.cases (zero a) (Fin.cases (zero b) (fun i => nomatch i)))))

def split (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (D : EExpr (Fin 1 ⊕ V))
    (e : EExpr (Fin 2 ⊕ V)) (p : EExpr V) : EExpr V :=
  .app .split (Fin.cases (zero A) (Fin.cases B (Fin.cases D
    (Fin.cases e (Fin.cases (zero p) (fun i => nomatch i))))))

def first (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (p : EExpr V) : EExpr V :=
  split A B (Expr.rename Sum.inr A) (.var (.inl 0)) p

/-- Instantiate the one bound variable; outer variables remain free. -/
def instantiate (B : Expr T (Fin 1 ⊕ V)) (a : Expr T V) : Expr T V :=
  Expr.subst (Sum.elim (fun _ => a) Expr.var) B

def second (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) (p : EExpr V) : EExpr V :=
  split A B
    (instantiate (Expr.rename (Sum.map id Sum.inr) B)
      (first (Expr.rename Sum.inr A) (Expr.rename (Sum.map id Sum.inr) B) (.var (.inl 0))))
    (.var (.inl 1)) p
@[simp] theorem subst_instantiate (f : V → Expr T W) (B : Expr T (Fin 1 ⊕ V))
    (a : Expr T V) :
    Expr.subst f (instantiate B a) =
      instantiate (Expr.subst (Expr.lift f) B) (Expr.subst f a) := by
  simp only [instantiate, Expr.subst_comp]
  congr 1
  funext v
  cases v with
  | inl => rfl
  | inr v =>
    simp only [Expr.lift, Expr.subst_rename]
    change f v = Expr.subst Expr.var (f v)
    exact (Expr.subst_id _).symm

@[simp] theorem subst_zero (f : V → Expr T W) (e : Expr T V) :
    Expr.subst (Expr.lift (n := 0) f) (zero e) = zero (Expr.subst f e) := by
  simp [zero, Expr.subst_rename, Expr.rename_subst, Expr.lift, Function.comp_def]

@[simp] theorem subst_split (f : V → EExpr W) (A : EExpr V)
    (B D : EExpr (Fin 1 ⊕ V)) (e : EExpr (Fin 2 ⊕ V)) (p : EExpr V) :
    Expr.subst f (split A B D e p) =
      split (Expr.subst f A) (Expr.subst (Expr.lift f) B)
        (Expr.subst (Expr.lift f) D) (Expr.subst (Expr.lift f) e) (Expr.subst f p) := by
  simp only [split, Expr.subst]
  congr 1
  funext i
  change Fin 5 at i
  fin_cases i <;> first | exact subst_zero f _ | rfl

@[simp] theorem subst_first (f : V → EExpr W) (A : EExpr V)
    (B : EExpr (Fin 1 ⊕ V)) (p : EExpr V) :
    Expr.subst f (first A B p) =
      first (Expr.subst f A) (Expr.subst (Expr.lift f) B) (Expr.subst f p) := by
  simp [first, Expr.subst_rename, Expr.rename_subst, Expr.lift, Function.comp_def]

@[simp] theorem lift_rename (f : V → Expr T W) (B : Expr T (Fin 1 ⊕ V)) :
    Expr.subst (Expr.lift (Expr.lift (n := 1) f))
      (Expr.rename (Sum.map id Sum.inr) B) =
    Expr.rename (Sum.map id Sum.inr) (Expr.subst (Expr.lift f) B) := by
  simp only [Expr.subst_rename, Expr.rename_subst]
  congr 1
  funext v
  cases v with
  | inl => rfl
  | inr => simp [Expr.lift, Expr.rename_comp, Function.comp_def]

@[simp] theorem subst_second (f : V → EExpr W) (A : EExpr V)
    (B : EExpr (Fin 1 ⊕ V)) (p : EExpr V) :
    Expr.subst f (second A B p) =
      second (Expr.subst f A) (Expr.subst (Expr.lift f) B) (Expr.subst f p) := by
  simp only [second, subst_split, subst_instantiate, subst_first, lift_rename]
  congr 2
  simp [Expr.subst_rename, Expr.rename_subst, Expr.lift, Function.comp_def]

@[simp] theorem subst_S (f : V → EExpr W) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    Expr.subst f (S A B) = S (Expr.subst f A) (Expr.subst (Expr.lift f) B) := by
  simp only [S, Expr.subst]
  congr 1
  funext i
  change Fin 2 at i
  fin_cases i <;> first | exact subst_zero f _ | rfl

@[simp] theorem subst_pack (f : V → EExpr W) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V))
    (a b : EExpr V) :
    Expr.subst f (pack A B a b) = pack (Expr.subst f A) (Expr.subst (Expr.lift f) B)
      (Expr.subst f a) (Expr.subst f b) := by
  simp only [pack, Expr.subst]
  congr 1
  funext i
  change Fin 4 at i
  fin_cases i <;> first | exact subst_zero f _ | rfl
end Elimination

@[simp] theorem unzero_subst (f : V → Expr T W) (e : Expr T (Fin 0 ⊕ V)) :
    unzero (Expr.subst (Expr.lift f) e) = Expr.subst f (unzero e) := by
  simp only [unzero, Expr.rename_subst, Expr.subst_rename]
  congr 1
  funext v
  cases v with
  | inl i => exact Fin.elim0 i
  | inr v => exact unzero_zero (f v)

/-- The symbol image for G is the actual first/second binding template above. -/
def Goperation {V : Type} (s : ProjectionSymbol)
    (a : (i : Fin (projectionSignature.arity s)) →
      EExpr (Fin (projectionSignature.binds s i) ⊕ V)) : EExpr V :=
  match s with
  | .P => Elimination.S (unzero (a 0)) (a 1)
  | .pair => Elimination.pack (unzero (a 0)) (a 1) (unzero (a 2)) (unzero (a 3))
  | .fst => Elimination.first (unzero (a 0)) (a 1) (unzero (a 2))
  | .snd => Elimination.second (unzero (a 0)) (a 1) (unzero (a 2))
  | .declaration decl => .app (.declaration decl) a

def Goperations : OperationMap projectionSignature eliminationSignature where
  operation := Goperation
  natural := by
    intro V W f s a
    cases s <;> simp [Goperation, Expr.subst]

def G : SyntaxMap projectionSignature eliminationSignature := .ofOperations Goperations

theorem G_two_substitutions (e : PExpr V) (σ : V → PExpr W) (τ : W → PExpr X) :
    Expr.subst (fun w => G.act (τ w)) (G.act (Expr.subst σ e)) =
      G.act (Expr.subst (fun v => Expr.subst τ (σ v)) e) := by
  rw [G.substitution, Expr.subst_comp, G.substitution]
  simp only [G.substitution]

@[simp] theorem G_pair (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (a b : PExpr V) :
    G.act (Projection.pair A B a b) =
      Elimination.pack (G.act A) (G.act B) (G.act a) (G.act b) := by
  change Elimination.pack (unzero (G.act (zero A))) (G.act B)
    (unzero (G.act (zero a))) (unzero (G.act (zero b))) = _
  simp [zero, G.rename, unzero]

@[simp] theorem G_first (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (p : PExpr V) :
    G.act (Projection.fst A B p) = Elimination.first (G.act A) (G.act B) (G.act p) := by
  change Elimination.first (unzero (G.act (zero A))) (G.act B)
    (unzero (G.act (zero p))) = _
  simp [zero, G.rename, unzero]

@[simp] theorem G_second (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (p : PExpr V) :
    G.act (Projection.snd A B p) = Elimination.second (G.act A) (G.act B) (G.act p) := by
  change Elimination.second (unzero (G.act (zero A))) (G.act B)
    (unzero (G.act (zero p))) = _
  simp [zero, G.rename, unzero]

/-- The selected source component remains the same raw variable, including after
both substitutions; the family expression is translated independently. -/
theorem selected_variable (z : V) (σ : V → PExpr W) (τ : W → PExpr X) :
    Expr.subst (fun w => G.act (τ w)) (G.act (Expr.subst σ (.var z))) =
      G.act (Expr.subst τ (σ z)) := G_two_substitutions (.var z) σ τ

end SquareKit.DependentPairPresentations
