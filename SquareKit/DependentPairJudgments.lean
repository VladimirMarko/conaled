import SquareKit.DependentPairPresentations

/-! Contextual rule boundaries for the independently specified pair presentations.
Contexts are finite telescopes, not arbitrary raw assumption families. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations
open Elimination (instantiate)

inductive Context (S : Signature) : Type → Type 1 where
  | empty : Context S Empty
  | extend {V : Type} : Context S V → Expr S V → Context S (Fin 1 ⊕ V)

namespace Context
variable {S T : Signature}

def lookup : {V : Type} → Context S V → V → Expr S V
  | _, .empty, v => nomatch v
  | _, .extend _ A, .inl _ => Expr.rename Sum.inr A
  | _, .extend Γ _, .inr v => Expr.rename Sum.inr (lookup Γ v)

def map (F : SyntaxMap S T) : {V : Type} → Context S V → Context T V
  | _, .empty => .empty
  | _, .extend Γ A => .extend (map F Γ) (F.act A)

@[simp] theorem map_lookup (F : SyntaxMap S T) (Γ : Context S V) (v : V) :
    (Γ.map F).lookup v = F.act (Γ.lookup v) := by
  induction Γ with
  | empty => exact Empty.elim v
  | extend Γ A ih =>
    cases v with
    | inl => simp only [lookup, map, F.rename]
    | inr v => simp only [lookup, map, F.rename, ih v]

@[simp] theorem map_identity (Γ : Context S V) : Γ.map (.identity S) = Γ := by
  induction Γ with
  | empty => rfl
  | extend Γ A ih =>
    change Context.extend (Γ.map (.identity S)) A = Context.extend Γ A
    rw [ih]

@[simp] theorem map_comp (F : SyntaxMap S T) (G : SyntaxMap T U) (Γ : Context S V) :
    (Γ.map F).map G = Γ.map (F.comp G) := by
  induction Γ with
  | empty => rfl
  | extend Γ A ih => simp only [map, SyntaxMap.comp_act, ih]
end Context

inductive Form (S : Signature) (V : Type) where
  | ctx
  | type (A : Expr S V)
  | term (a A : Expr S V)
  | typeEq (A B : Expr S V)
  | termEq (a b A : Expr S V)

structure Judgment (S : Signature) where
  Scope : Type
  context : Context S Scope
  form : Form S Scope

namespace Judgment
variable {S T : Signature}
def ctx (Γ : Context S V) : Judgment S := ⟨V, Γ, .ctx⟩
def type (Γ : Context S V) (A : Expr S V) : Judgment S := ⟨V, Γ, .type A⟩
def term (Γ : Context S V) (a A : Expr S V) : Judgment S := ⟨V, Γ, .term a A⟩
def typeEq (Γ : Context S V) (A B : Expr S V) : Judgment S := ⟨V, Γ, .typeEq A B⟩
def termEq (Γ : Context S V) (a b A : Expr S V) : Judgment S := ⟨V, Γ, .termEq a b A⟩

def mapForm (F : SyntaxMap S T) : Form S V → Form T V
  | .ctx => .ctx
  | .type A => .type (F.act A)
  | .term a A => .term (F.act a) (F.act A)
  | .typeEq A B => .typeEq (F.act A) (F.act B)
  | .termEq a b A => .termEq (F.act a) (F.act b) (F.act A)

def map (F : SyntaxMap S T) (j : Judgment S) : Judgment T :=
  ⟨j.Scope, j.context.map F, mapForm F j.form⟩
end Judgment

structure Schema (S : Signature) where
  premises : List (Judgment S)
  conclusion : Judgment S

def rulesOf {S : Signature} {L : Type 1} (schema : L → Schema S) : Rules (Judgment S) where
  Label := L
  count := fun l => (schema l).premises.length
  premise := fun l i => (schema l).premises.get i
  conclusion := fun l => (schema l).conclusion

/-- The pair-specific table is selected independently for each presentation.
The parameter admits an eta rule, not derivations from another theory. -/
inductive ProjectionRule (eta : Bool) where
  | formation {V} (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
  | pair {V} (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
      (a b : PExpr V)
  | first {V} (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
      (p : PExpr V)
  | second {V} (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
      (p : PExpr V)
  | firstBeta {V} (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
      (a b : PExpr V)
  | secondBeta {V} (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
      (a b : PExpr V)
  | eta {V} (allowed : eta = true) (Γ : Context projectionSignature V)
      (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) (p : PExpr V)

namespace ProjectionRule
open Judgment Projection

def family (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) :=
  [ctx Γ, type Γ A, type (.extend Γ A) B]

def components (Γ : Context projectionSignature V) (A : PExpr V)
    (B : PExpr (Fin 1 ⊕ V)) (a b : PExpr V) :=
  family Γ A B ++ [term Γ a A, term Γ b (instantiate B a)]

def argument (Γ : Context projectionSignature V) (A : PExpr V)
    (B : PExpr (Fin 1 ⊕ V)) (p : PExpr V) :=
  family Γ A B ++ [term Γ p (P A B)]

def schema {hasEta : Bool} : ProjectionRule hasEta → Schema projectionSignature
  | .formation Γ A B => ⟨family Γ A B, type Γ (P A B)⟩
  | .pair Γ A B a b => ⟨components Γ A B a b, term Γ (Projection.pair A B a b) (P A B)⟩
  | .first Γ A B p => ⟨argument Γ A B p, term Γ (fst A B p) A⟩
  | .second Γ A B p => ⟨argument Γ A B p, term Γ (snd A B p) (instantiate B (fst A B p))⟩
  | .firstBeta Γ A B a b =>
      ⟨components Γ A B a b, termEq Γ (fst A B (Projection.pair A B a b)) a A⟩
  | .secondBeta Γ A B a b =>
      ⟨components Γ A B a b, termEq Γ (snd A B (Projection.pair A B a b)) b (instantiate B a)⟩
  | .eta _ Γ A B p =>
      ⟨argument Γ A B p, termEq Γ (Projection.pair A B (fst A B p) (snd A B p)) p (P A B)⟩

def inclusion : ProjectionRule false → ProjectionRule true
  | .formation Γ A B => .formation Γ A B
  | .pair Γ A B a b => .pair Γ A B a b
  | .first Γ A B p => .first Γ A B p
  | .second Γ A B p => .second Γ A B p
  | .firstBeta Γ A B a b => .firstBeta Γ A B a b
  | .secondBeta Γ A B a b => .secondBeta Γ A B a b
  | .eta h _ _ _ _ => Bool.noConfusion h

@[simp] theorem include_schema (r : ProjectionRule false) : schema (inclusion r) = schema r := by
  cases r <;> first | rfl | contradiction
end ProjectionRule

/-- These are the primitive pair rules; structural closure is specified separately. -/
def projectionBetaRules := rulesOf (ProjectionRule.schema (hasEta := false))
def projectionEtaRules := rulesOf (ProjectionRule.schema (hasEta := true))

def Fprimitive : TheoryMap projectionBetaRules projectionEtaRules id where
  certificate r := by
    cases r with
    | formation Γ A B => exact Derivation.rule (R := projectionEtaRules) (ProjectionRule.formation Γ A B) (fun i => .hyp ⟨i, rfl⟩)
    | pair Γ A B a b => exact Derivation.rule (R := projectionEtaRules) (ProjectionRule.pair Γ A B a b) (fun i => .hyp ⟨i, rfl⟩)
    | first Γ A B p => exact Derivation.rule (R := projectionEtaRules) (ProjectionRule.first Γ A B p) (fun i => .hyp ⟨i, rfl⟩)
    | second Γ A B p => exact Derivation.rule (R := projectionEtaRules) (ProjectionRule.second Γ A B p) (fun i => .hyp ⟨i, rfl⟩)
    | firstBeta Γ A B a b => exact Derivation.rule (R := projectionEtaRules) (ProjectionRule.firstBeta Γ A B a b) (fun i => .hyp ⟨i, rfl⟩)
    | secondBeta Γ A B a b => exact Derivation.rule (R := projectionEtaRules) (ProjectionRule.secondBeta Γ A B a b) (fun i => .hyp ⟨i, rfl⟩)
    | eta h => contradiction

end SquareKit.DependentPairJudgments
