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

namespace Form
def rename (f : V → W) : Form S V → Form S W
  | .ctx => .ctx
  | .type A => .type (Expr.rename f A)
  | .term a A => .term (Expr.rename f a) (Expr.rename f A)
  | .typeEq A B => .typeEq (Expr.rename f A) (Expr.rename f B)
  | .termEq a b A => .termEq (Expr.rename f a) (Expr.rename f b) (Expr.rename f A)
end Form

/-- Structural rules retain the common type of an equation. Family congruence
substitutes equal typed terms in a separately formed dependent family. -/
inductive StructuralRule (S : Signature) where
  | empty
  | extend {V} (Γ : Context S V) (A : Expr S V)
  | variable {V} (Γ : Context S V) (v : V)
  | weaken {V} (Γ : Context S V) (A : Expr S V) (φ : Form S V)
  | typeRefl {V} (Γ : Context S V) (A : Expr S V)
  | typeSymm {V} (Γ : Context S V) (A B : Expr S V)
  | typeTrans {V} (Γ : Context S V) (A B C : Expr S V)
  | termRefl {V} (Γ : Context S V) (a A : Expr S V)
  | termSymm {V} (Γ : Context S V) (a b A : Expr S V)
  | termTrans {V} (Γ : Context S V) (a b c A : Expr S V)
  | convert {V} (Γ : Context S V) (a A B : Expr S V)
  | convertEq {V} (Γ : Context S V) (a b A B : Expr S V)
  | familyCong {V} (Γ : Context S V) (A : Expr S V)
      (B : Expr S (Fin 1 ⊕ V)) (a b : Expr S V)

namespace StructuralRule
open Judgment
def schema : StructuralRule S → Schema S
  | .empty => ⟨[], ctx .empty⟩
  | .extend Γ A => ⟨[ctx Γ, type Γ A], ctx (.extend Γ A)⟩
  | .variable Γ v => ⟨[ctx Γ], term Γ (.var v) (Γ.lookup v)⟩
  | .weaken Γ A φ => ⟨[ctx Γ, type Γ A, ⟨_, Γ, φ⟩],
      ⟨_, .extend Γ A, φ.rename Sum.inr⟩⟩
  | .typeRefl Γ A => ⟨[type Γ A], typeEq Γ A A⟩
  | .typeSymm Γ A B => ⟨[typeEq Γ A B], typeEq Γ B A⟩
  | .typeTrans Γ A B C => ⟨[typeEq Γ A B, typeEq Γ B C], typeEq Γ A C⟩
  | .termRefl Γ a A => ⟨[term Γ a A], termEq Γ a a A⟩
  | .termSymm Γ a b A => ⟨[termEq Γ a b A], termEq Γ b a A⟩
  | .termTrans Γ a b c A => ⟨[termEq Γ a b A, termEq Γ b c A], termEq Γ a c A⟩
  | .convert Γ a A B => ⟨[term Γ a A, typeEq Γ A B], term Γ a B⟩
  | .convertEq Γ a b A B => ⟨[termEq Γ a b A, typeEq Γ A B], termEq Γ a b B⟩
  | .familyCong Γ A B a b =>
      ⟨[ctx Γ, type Γ A, type (.extend Γ A) B, termEq Γ a b A],
        typeEq Γ (instantiate B a) (instantiate B b)⟩
end StructuralRule

/-- Structural closure is shared machinery; the primitive rule tables stay independent. -/
def closedRules {S : Signature} {L : Type 1} (primitive : L → Schema S) : Rules (Judgment S) :=
  rulesOf (Sum.elim StructuralRule.schema primitive)

def Pβ := closedRules (ProjectionRule.schema (hasEta := false))
def Pη := closedRules (ProjectionRule.schema (hasEta := true))

/-- Replay structural rules and the independently specified source table. -/
def F : TheoryMap Pβ Pη id where
  certificate r := by
    cases r with
    | inl s => exact Derivation.rule (R := Pη) (.inl s) (fun i => .hyp ⟨i, rfl⟩)
    | inr r =>
      cases r with
      | formation Γ A B => exact Derivation.rule (R := Pη) (.inr (.formation Γ A B)) (fun i => .hyp ⟨i, rfl⟩)
      | pair Γ A B a b => exact Derivation.rule (R := Pη) (.inr (.pair Γ A B a b)) (fun i => .hyp ⟨i, rfl⟩)
      | first Γ A B p => exact Derivation.rule (R := Pη) (.inr (.first Γ A B p)) (fun i => .hyp ⟨i, rfl⟩)
      | second Γ A B p => exact Derivation.rule (R := Pη) (.inr (.second Γ A B p)) (fun i => .hyp ⟨i, rfl⟩)
      | firstBeta Γ A B a b => exact Derivation.rule (R := Pη) (.inr (.firstBeta Γ A B a b)) (fun i => .hyp ⟨i, rfl⟩)
      | secondBeta Γ A B a b => exact Derivation.rule (R := Pη) (.inr (.secondBeta Γ A B a b)) (fun i => .hyp ⟨i, rfl⟩)
      | eta h => contradiction

namespace ProjectionBoundary
open Judgment Projection

/-- This boundary proof uses first beta to convert the natural type of snd.
It does not use the second beta equation whose left endpoint is being checked. -/
def secondBetaLeft {H : Judgment projectionSignature → Type}
    (Γ : Context projectionSignature V) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (a b : PExpr V)
    (hΓ : Derivation Pβ H (ctx Γ)) (hA : Derivation Pβ H (type Γ A))
    (hB : Derivation Pβ H (type (.extend Γ A) B))
    (ha : Derivation Pβ H (term Γ a A))
    (hb : Derivation Pβ H (term Γ b (instantiate B a))) :
    Derivation Pβ H (term Γ (snd A B (pair A B a b)) (instantiate B a)) := by
  have hp : Derivation Pβ H (term Γ (pair A B a b) (P A B)) := by
    apply Derivation.rule (R := Pβ) (.inr (.pair Γ A B a b))
    exact Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases ha (Fin.cases hb (fun i => Fin.elim0 i)))))
  have hs : Derivation Pβ H
      (term Γ (snd A B (pair A B a b)) (instantiate B (fst A B (pair A B a b)))) := by
    apply Derivation.rule (R := Pβ) (.inr (.second Γ A B (pair A B a b)))
    exact Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hp (fun i => Fin.elim0 i))))
  have hfst : Derivation Pβ H (termEq Γ (fst A B (pair A B a b)) a A) := by
    apply Derivation.rule (R := Pβ) (.inr (.firstBeta Γ A B a b))
    exact Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases ha (Fin.cases hb (fun i => Fin.elim0 i)))))
  have hfamily : Derivation Pβ H
      (typeEq Γ (instantiate B (fst A B (pair A B a b))) (instantiate B a)) := by
    apply Derivation.rule (R := Pβ) (.inl (.familyCong Γ A B (fst A B (pair A B a b)) a))
    exact Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hfst (fun i => Fin.elim0 i))))
  apply Derivation.rule (R := Pβ) (.inl (.convert Γ (snd A B (pair A B a b))
    (instantiate B (fst A B (pair A B a b))) (instantiate B a)))
  exact Fin.cases hs (Fin.cases hfamily (fun i => Fin.elim0 i))
end ProjectionBoundary

end SquareKit.DependentPairJudgments


