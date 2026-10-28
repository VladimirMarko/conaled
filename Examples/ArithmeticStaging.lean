import Applications.Stack.Staging

/-! Configure the existing shared polynomial, then run its residual stack code. -/
namespace Examples.ArithmeticStaging
open FirstOrderCompiler Arithmetic.Staging

def inputs : Term.Sub Arithmetic.Prim [.prod .base .base] [.base,.base]
  | _, .here => .pair (.var .here) (.var (.there .here))
  | _, .there v => nomatch v

/-- Reuse the existing source body and its let-bound common subexpression. -/
def body : Term Arithmetic.Prim [.base,.base] .base := Term.subst inputs Arithmetic.shared

def configured (c : Term Arithmetic.Prim Δ .base) : Program Δ [.base] .base := ⟨c,body⟩

theorem body_value (a b : Int) : eval (@Arithmetic.meaning Int _) body (((),b),a) = (a*b)*(a*b)+a := by
  exact (Term.eval_subst Arithmetic.meaning Arithmetic.shared inputs ((),(a,b)) (((),b),a)
    (fun v => by cases v with | here => rfl | there v => cases v)).trans
    (Arithmetic.eval_shared a b)

/-- The ordinary client remains a direct Lean function. -/
def ordinary (a b : Int) := (a*b)*(a*b)+a

theorem residual_value (c : Term Arithmetic.Prim Δ .base) (σ : Val Int (context Δ)) (b : Int) :
    eval (@Arithmetic.meaning Int _) (specialize (configured c) σ) ((),b) =
      ordinary (eval (@Arithmetic.meaning Int _) c σ) b :=
  (specialize_correct (configured c) σ ((),b)).trans (body_value _ b)

def configuration : Term Arithmetic.Prim [] .base := .prim .add (.pair (quote 1) (quote 2))
def residual := specialize (configured configuration) ()

/-- Exact residual syntax, with a literal replacing the static addition. -/
example : residual = Term.subst (Term.single (quote 3)) body := rfl
example : eval (@Arithmetic.meaning Int _) residual ((),4) = 147 := residual_value configuration () 4
example : eval (@Arithmetic.meaning Int _) (specialize (configured (quote (Γ := []) (-2))) ()) ((),3) = 34 :=
  residual_value (quote (Γ := []) (-2)) () 3
example : eval (@Arithmetic.meaning Int _) (specialize (configured (quote (Γ := []) 0)) ()) ((),9) = 0 :=
  residual_value (quote (Γ := []) 0) () 9

def code := (compile (StackMachine.target Arithmetic.Prim (@Arithmetic.meaning Int _)) residual).code []
example : StackMachine.run (@Arithmetic.meaning Int _) code (((),4),()) = (147,()) :=
  (stack_correct (configured configuration) () [] ((),4) ()).trans
    (congrArg (fun n : Int => (n,())) (body_value 3 4))

/- This is a typed instruction artifact, not a host-core declaration emitter. -/
#eval StackMachine.run (@Arithmetic.meaning Int _) code (((),4),())
#eval StackMachine.listing Arithmetic.name code

/-- Literal specialization removes static ADD instructions from the residual artifact. -/
def unspecialized : Term Arithmetic.Prim [.base] .base :=
  Term.subst (Term.single (Term.rename (fun {a} (v : Var [] a) => nomatch v) configuration)) body
def unspecializedCode :=
  (compile (StackMachine.target Arithmetic.Prim (@Arithmetic.meaning Int _)) unspecialized).code []
example : ((StackMachine.listing Arithmetic.name code).filter (· == "ADD")).length = 1 := by decide
example : ((StackMachine.listing Arithmetic.name unspecializedCode).filter (· == "ADD")).length > 1 := by decide
example : StackMachine.run (@Arithmetic.meaning Int _) unspecializedCode (((),4),()) = (147,()) := by decide

/-- Substituting static configuration input commutes with specialization exactly. -/
def staticInput : Program [.base] [.base] .base := configured (.var .here)
example : specialize ⟨Term.subst (Term.single (quote 3)) staticInput.configuration, staticInput.body⟩ () =
    specialize staticInput ((),3) :=
  static_substitution staticInput (Term.single (quote 3)) ((),3) ()
    (fun v => by cases v with | here => rfl | there v => cases v)

/-- Runtime substitution reaches through the existing let binder without capture. -/
example : eval (@Arithmetic.meaning Int _) (Term.subst (Term.single (quote 4)) residual) () = 147 :=
  (runtime_substitution (configured configuration) () (Term.single (quote 4)) ((),4) ()
    (fun v => by cases v with | here => rfl | there v => cases v)).trans (body_value 3 4)

/-- A free replacement variable remains free beneath a let-bound 99. -/
def underLet : Term Arithmetic.Prim [.base,.base] .base :=
  .letE (quote 99) (.var (.there .here))
example : eval (@Arithmetic.meaning Int _)
    (Term.subst (Term.single (.var .here)) underLet) ((),4) = 4 :=
  Term.eval_single Arithmetic.meaning underLet (.var .here) ((),4)
example : eval (@Arithmetic.meaning Int _)
    (.letE (quote 99) (.var .here) : Term Arithmetic.Prim [.base] .base) ((),4) ≠ 4 := by decide

example : IsEmpty (Var [] .base) := no_static_variable
example : ¬ ∃ c : Term Arithmetic.Prim [] .base, ∀ x : Int, eval (@Arithmetic.meaning Int _) c () = x :=
  no_runtime_dependency

end Examples.ArithmeticStaging
