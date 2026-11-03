import Applications.Sequences.AbstractFIFO
import SquareKit.STLCRelations
import SquareKit.STLCSubstitution

/-! Optional compiler surface for the same operation-only client. The compiler's
single base type represents the queue; endpoint observations stay outside syntax.
The direct client imports no compiler machinery. -/
namespace Sequences.AbstractFIFO.Syntax
open CategoricalCompiler Relational
variable {α Q : Type}

inductive Prim (α : Type) : Ty → Ty → Type where
  | command : Command α → Prim α .base .base

def meaning (ops : Ops α Q) : {a b : Ty} → Prim α a b → Val Q a → Val Q b
  | _, _, .command c => step ops c

/-- Fill a state-expression hole with an ordered word of operations. -/
def plug (cs : List (Command α)) (t : Term (Prim α) Γ .base) : Term (Prim α) Γ .base :=
  match cs with
  | [] => t
  | c :: cs => plug cs (.prim (.command c) t)

/-- Interpretation commutes with substitution of any well-typed state expression. -/
theorem eval_plug (ops : Ops α Q) (cs : List (Command α)) (t : Term (Prim α) Γ .base)
    (ρ : Val Q (context Γ)) :
    eval (meaning ops) (plug cs t) ρ = run ops cs (eval (meaning ops) t ρ) := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem plug_append (xs ys : List (Command α)) (t : Term (Prim α) Γ .base) :
    plug (xs ++ ys) t = plug ys (plug xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons c cs ih => exact ih _

/-- General capture-avoiding source substitution commutes with a word context. -/
theorem subst_plug (s : Term.Sub (Prim α) Γ Δ) (cs : List (Command α))
    (t : Term (Prim α) Γ .base) :
    Term.subst s (plug cs t) = plug cs (Term.subst s t) := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih => exact ih _

def program (cs : List (Command α)) : Term (Prim α) [.base] .base := plug cs (.var .here)

def primitives (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) :
    STLCRelations.Primitives ⟨Q, List α, rel⟩ (Prim α) (meaning (lists α)) where
  impl p := match p with | .command c => step ops c
  correct p := by
    cases p with
    | command c => exact (h.stepSquare c).preserves

/-- Compiler preservation is reused for arbitrary source state expressions. -/
theorem compile_preserves (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (t : Term (Prim α) Γ .base)
    {r : (STLCRelations.encoding ⟨Q,List α,rel⟩ (context Γ)).R}
    {s : Val (List α) (context Γ)}
    (related : (STLCRelations.encoding ⟨Q,List α,rel⟩ (context Γ)).Rel r s) :
    rel ((compile (STLCRelations.target _ (primitives ops rel h)) t).impl r)
      (eval (meaning (lists α)) t s) :=
  STLCRelations.compile_preserves _ _ t related

/-- The optional compiler surface runs the unchanged ordinary client operations. -/
theorem compile_plug (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (cs : List (Command α))
    (t : Term (Prim α) Γ .base)
    (ρ : (STLCRelations.encoding ⟨Q,List α,rel⟩ (context Γ)).R) :
    (compile (STLCRelations.target _ (primitives ops rel h)) (plug cs t)).impl ρ =
      run ops cs ((compile (STLCRelations.target _ (primitives ops rel h)) t).impl ρ) := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem program_runs (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (cs : List (Command α)) (q : Q) :
    (compile (STLCRelations.target _ (primitives ops rel h)) (program cs)).impl ((),q) =
      run ops cs q := compile_plug ops rel h cs _ _

/-- One endpoint theorem applies to either implementation's compiled client. -/
theorem observe_program (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (cs : List (Command α)) {q xs} (related : rel q xs) :
    ops.head ((compile (STLCRelations.target _ (primitives ops rel h)) (program cs)).impl ((),q)) =
      client (lists α) cs xs := by
  apply h.head
  have hp := compile_preserves ops rel h (program cs) (r := ((),q)) (s := ((),xs)) (show True ∧ rel q xs from ⟨trivial,related⟩)
  simpa only [program, eval_plug, eval, lookup] using hp

end Sequences.AbstractFIFO.Syntax
