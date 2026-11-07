import SquareKit.DependentTheoryTemplates
import SquareKit.DependentPairJudgments

/-! Closed sequential rule syntax and its ambient contextual instances. -/
namespace SquareKit.DependentSequentialRules
open DependentTheoryMaps DependentPairJudgments

/-- Iterated extension by one bound variable, with a separate ambient scope. -/
def Scope : Nat → Type → Type
  | 0, V => V
  | n + 1, V => Fin 1 ⊕ Scope n V

/-- A rule's local telescope has no ambient free boundVariables. -/
inductive Telescope (S : Signature) : Nat → Type 1
  | empty : Telescope S 0
  | extend {n} : Telescope S n → Expr S (Scope n Empty) → Telescope S (n + 1)

def boundVariables (S : Signature) (V : Type) : (n : Nat) → Scope n Empty → Expr S (Scope n V)
  | 0 => Empty.elim
  | n + 1 => Expr.lift (boundVariables S V n)

def assignment (a : Assignment S M V) : (n : Nat) → Assignment S M (Scope n V)
  | 0 => a
  | n + 1 => (assignment a n).weaken 1

def expression (a : Assignment S M V) (n : Nat) (e : Expr (extend S M) (Scope n Empty)) :
    Expr S (Scope n V) := instantiate (boundVariables S V n) (assignment a n) e

@[simp] theorem expression_weaken (a : Assignment S M V) (n : Nat)
    (e : Expr (extend S M) (Scope n Empty)) :
    expression a (n + 1) (Expr.rename Sum.inr e) = Expr.rename Sum.inr (expression a n e) :=
  instantiate_weaken _ _ _

/-- Instantiation adds the local telescope to the arbitrary ambient context. -/
def Telescope.instantiate (Γ : Context S V) (a : Assignment S M V) :
    {n : Nat} → Telescope (DependentTheoryMaps.extend S M) n → Context S (Scope n V)
  | _, .empty => Γ
  | _, .extend Δ A => (Δ.instantiate Γ a).extend (expression a _ A)

def form (a : Assignment S M V) (n : Nat) :
    Form (extend S M) (Scope n Empty) → Form S (Scope n V)
  | .ctx => .ctx
  | .type A => .type (expression a n A)
  | .term t A => .term (expression a n t) (expression a n A)
  | .typeEq A B => .typeEq (expression a n A) (expression a n B)
  | .termEq t u A => .termEq (expression a n t) (expression a n u) (expression a n A)

structure RelativeJudgment (S : Signature) where
  depth : Nat
  telescope : Telescope S depth
  form : Form S (Scope depth Empty)

def RelativeJudgment.instantiate (Γ : Context S V) (a : Assignment S M V)
    (j : RelativeJudgment (extend S M)) : Judgment S :=
  ⟨Scope j.depth V, j.telescope.instantiate Γ a, DependentSequentialRules.form a j.depth j.form⟩

/-- A raw rule has ordered abstracted premises and an empty conclusion context.
The ambient context is supplied only when interpreting the rule. -/
structure Rule (S : Signature) (M : Metavariables) where
  premises : List (RelativeJudgment (extend S M))
  conclusion : Form (extend S M) Empty

def Rule.instantiate (Γ : Context S V) (a : Assignment S M V) (r : Rule S M) : Schema S :=
  ⟨Judgment.ctx Γ :: r.premises.map (RelativeJudgment.instantiate Γ a),
    ⟨V, Γ, form a 0 r.conclusion⟩⟩

end SquareKit.DependentSequentialRules
