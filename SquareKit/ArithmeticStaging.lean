import SquareKit.Arithmetic
import SquareKit.FirstOrderSubstitution
import Mathlib.Algebra.Ring.Int.Defs

/-! Two compilation phases over existing arithmetic syntax. Static configuration
has only its own context; residual code retains the separate runtime context. -/
namespace Arithmetic.Staging
open FirstOrderCompiler

structure Program (Δ Γ : Ctx) (a : Ty) where
  configuration : Term Prim Δ .base
  body : Term Prim (.base :: Γ) a

def quote (n : Int) : Term Prim Γ .base := .prim (.literal n) .unit

@[simp] theorem eval_quote (n : Int) (ρ : Val Int (context Γ)) :
    eval (@Arithmetic.meaning Int _) (quote n) ρ = n := rfl

/-- Phase one receives no runtime environment. The result is ordinary typed syntax. -/
def specialize (p : Program Δ Γ a) (σ : Val Int (context Δ)) : Term Prim Γ a :=
  Term.subst (Term.single (quote (eval (@Arithmetic.meaning Int _) p.configuration σ))) p.body

def meaning (p : Program Δ Γ a) (σ : Val Int (context Δ)) (ρ : Val Int (context Γ)) : Val Int a :=
  eval Arithmetic.meaning p.body (ρ, eval Arithmetic.meaning p.configuration σ)

/-- Stage-respecting residual correctness, for every runtime environment. -/
theorem specialize_correct (p : Program Δ Γ a) (σ : Val Int (context Δ)) (ρ : Val Int (context Γ)) :
    eval Arithmetic.meaning (specialize p σ) ρ = meaning p σ ρ :=
  Term.eval_single Arithmetic.meaning p.body _ ρ

/-- Substitution in static inputs agrees with specialization itself, as syntax equality. -/
theorem static_substitution (p : Program Δ Γ a) (s : Term.Sub Prim Δ Δ')
    (σ : Val Int (context Δ)) (τ : Val Int (context Δ'))
    (h : ∀ {b} (v : Var Δ b), eval Arithmetic.meaning (s v) τ = lookup v σ) :
    specialize ⟨Term.subst s p.configuration, p.body⟩ τ = specialize p σ := by
  unfold specialize
  rw [Term.eval_subst Arithmetic.meaning p.configuration s σ τ h]

/-- Runtime substitution preserves the residual interpretation without changing phase one. -/
theorem runtime_substitution (p : Program Δ Γ a) (σ : Val Int (context Δ))
    (s : Term.Sub Prim Γ Γ') (ρ : Val Int (context Γ)) (τ : Val Int (context Γ'))
    (h : ∀ {b} (v : Var Γ b), eval Arithmetic.meaning (s v) τ = lookup v ρ) :
    eval Arithmetic.meaning (Term.subst s (specialize p σ)) τ = meaning p σ ρ :=
  (Term.eval_subst _ _ s ρ τ h).trans (specialize_correct p σ ρ)

/-- Any existing sound target can interpret the residual code. -/
theorem compile_correct (p : Program Δ Γ a) (σ : Val Int (context Δ))
    (K : Target Prim) (S : Sound Int K Arithmetic.meaning) (ρ : Val Int (context Γ)) :
    S.denote (compile K (specialize p σ)) ρ = meaning p σ ρ :=
  (FirstOrderCompiler.compile_sound K S _ ρ).trans (specialize_correct p σ ρ)

/-- An empty static context has no variable referring to a runtime input. -/
theorem no_static_variable : IsEmpty (Var [] .base) := ⟨fun v => nomatch v⟩

/-- No closed static configuration can implement the runtime identity dependency. -/
theorem no_runtime_dependency : ¬ ∃ t : Term Prim [] .base,
    ∀ x : Int, eval Arithmetic.meaning t () = x := by
  rintro ⟨t,h⟩
  have bad := (h 0).symm.trans (h 1)
  exact (by decide : (0 : Int) ≠ 1) bad

end Arithmetic.Staging
