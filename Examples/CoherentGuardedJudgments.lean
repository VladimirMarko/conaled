import Examples.GuardedContextualJudgments
import SquareKit.Internal.DependentJudgments.CoherentTypePresentations
import SquareKit.Internal.DependentJudgments.TypedMaps

/-! A single authored contextual command is interpreted in two unequal family
presentations. The comparison transports the context, both dependent binders,
the motive, branch and selected result. -/
namespace Examples.CoherentGuardedJudgments
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.CoherentTypePresentations
open SquareKit.Internal.PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

variable (Base : Type u) (Fiber : Base → Type u)
local notation "M" => NativeType.model Base Fiber
local notation "S" => NativeType.structuralModel Base Fiber

noncomputable def evaluated (p : Problem S) : Value S :=
  (GuardedContextualJudgments.command p.length).expression.eval (Contextual.algebra M)
    (problemEnvironment S p)

theorem evaluated_value (p : Problem S) :
    evaluated Base Fiber p = .term p.telescope.total p.motive
      ((M).j p.family p.term p.telescope p.motive p.branch) := by
  rcases p with ⟨⟨⟨Γ, A, x⟩, n, T⟩, C, d⟩
  simp [evaluated, GuardedContextualJudgments.command, Command.expression,
    Term.eval, Contextual.algebra, Contextual.operation, problemEnvironment, NativeType.model]

/-- Definedness is also inherited from the authored typing derivation, so the
comparison below cannot be an equality between two failed decodings. -/
theorem evaluated_defined (p : Problem S) : evaluated Base Fiber p ≠ .invalid :=
  (Defined.term (GuardedContextualJudgments.command p.length).typing).sound M
    (problemEnvironment S p) (GuardedContextualJudgments.inputs M p)

section Comparison
variable {Γ Δ : Type u} {e : Γ ≃ Δ} {A : Γ → Type u} {B : Δ → Type u}
variable (f : FamilyComparison e A B) (x : (γ : Γ) → A γ) {n : Nat}
variable {T : Telescope (NativeType.structuralModel Base Fiber) ((NativeType.structuralModel Base Fiber).pathContext A ⟨x⟩) n}
variable {U : Telescope (NativeType.structuralModel Base Fiber) ((NativeType.structuralModel Base Fiber).pathContext B ⟨f.term x⟩) n}
variable (tails : TelescopeComparison Base Fiber (f.path x) T U)
variable {C : T.total → Type u} {D : U.total → Type u}
variable (motives : FamilyComparison tails.total C D)

def sourceProblem (branch : (γ : (Telescope.pullback S T ((S).rootSub A ⟨x⟩)).total) → C (((S).rootTail A ⟨x⟩ T).down γ)) : Problem S :=
  ⟨⟨⟨Γ, A, ⟨x⟩⟩, n, T⟩, C, ⟨branch⟩⟩
def targetProblem (branch : (γ : (Telescope.pullback S T ((S).rootSub A ⟨x⟩)).total) → C (((S).rootTail A ⟨x⟩ T).down γ)) : Problem S :=
  ⟨⟨⟨Δ, B, ⟨f.term x⟩⟩, n, U⟩, D, jBranch f x tails motives ⟨branch⟩⟩

/-- The two valuations are assembled from the chosen presentation comparison.
The caller supplies fiber equivalences; the branch and final comparison are
constructed by the native model builders. -/
theorem interpreted_command_comparison (branch : (γ : (Telescope.pullback S T ((S).rootSub A ⟨x⟩)).total) → C (((S).rootTail A ⟨x⟩ T).down γ)) :
    Option.map (fun t => motives.term t.down)
      ((evaluated Base Fiber (sourceProblem Base Fiber x branch)).termAt T.total C) =
    Option.map (fun t => t.down)
      ((evaluated Base Fiber (targetProblem Base Fiber f x tails motives branch)).termAt U.total D) := by
  rw [evaluated_value, evaluated_value]
  simp only [sourceProblem, targetProblem, Value.termAt_term, Option.map_some]
  exact congrArg some (contextualJ_compare f x tails motives ⟨branch⟩)

end Comparison

namespace FiniteOptionExample
open CoherentTypePresentations.FiniteOption
local notation "N" => NativeType.model Nat (fun n => Fin (n + 1))
local notation "S₀" => NativeType.structuralModel Nat (fun n => Fin (n + 1))

def source : Problem S₀ :=
  ⟨⟨⟨FiniteOption.Base, direct, ⟨zero⟩⟩, 2, sourceTail⟩, sourceMotive, sourceBranch⟩
def target : Problem S₀ :=
  ⟨⟨⟨FiniteOption.Base, coded, ⟨comparison.term zero⟩⟩, 2, targetTail⟩, targetMotive, targetBranch⟩

/-- The same source command at the two constructed assignments compares the
retained dependent value; its two tail families and result family differ. -/
theorem source_recipe_comparison :
    Option.map (fun t => motives.term t.down)
      ((evaluated Nat (fun n => Fin (n + 1)) source).termAt sourceTail.total sourceMotive) =
    Option.map (fun t => t.down)
      ((evaluated Nat (fun n => Fin (n + 1)) target).termAt targetTail.total targetMotive) :=
  interpreted_command_comparison Nat (fun n => Fin (n + 1)) comparison zero tails motives sourceBranch.down

/-- The selected result is read from the interpreted source recipe. -/
theorem source_recipe_selected :
    Option.map (fun t => (t.down sampleSource).val)
      ((evaluated Nat (fun n => Fin (n + 1)) source).termAt sourceTail.total sourceMotive) = some 2 := by
  rw [evaluated_value]
  simp only [source, Value.termAt_term, Option.map_some]
  exact congrArg some source_selected_two

/-- The target observation follows from the constructed comparison, preserving
2 as its specified code some 1. -/
theorem target_recipe_selected :
    Option.map (fun t => t.down (tails.total sampleSource))
      ((evaluated Nat (fun n => Fin (n + 1)) target).termAt targetTail.total targetMotive) =
      some (some (⟨1, by decide⟩ : Fin 3)) := by
  have h := congrArg (Option.map (fun t => t (tails.total sampleSource))) source_recipe_comparison
  rw [evaluated_value, evaluated_value] at h
  rw [evaluated_value]
  simp only [source, target, Value.termAt_term, Option.map_some] at h ⊢
  apply h.symm.trans
  rw [FamilyComparison.term_apply]
  have hs : sourceResult.down sampleSource = (⟨2, by decide⟩ : Fin 4) := Fin.ext source_selected_two
  change some (motives sampleSource (sourceResult.down sampleSource)) = _
  rw [hs]
  rfl

end FiniteOptionExample
end Examples.CoherentGuardedJudgments
