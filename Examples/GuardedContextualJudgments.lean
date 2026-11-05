import SquareKit.Internal.DependentJudgments.Templates
import SquareKit.Internal.PathTransport.GroupoidSoundness

/-! The same generated command is checked before a model is selected. Its
interpretation can subsequently use any full contextual model. -/
namespace Examples.GuardedContextualJudgments
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u

abbrev assumptions (n : Nat) : List (Contextual.Judgment (Fin 6)) := List.ofFn (jRule n).premise

def command (n : Nat) : Command (assumptions n) (.var 0) (.var 1) (.var 2) where
  point := .hypothesis (List.mem_ofFn.mpr ⟨0, rfl⟩)
  length := n
  tail := .var 3
  tailTyping := .hypothesis (List.mem_ofFn.mpr ⟨1, rfl⟩)
  motive := .var 4
  motiveTyping := .hypothesis (List.mem_ofFn.mpr ⟨2, rfl⟩)
  branch := .var 5
  branchTyping := .hypothesis (List.mem_ofFn.mpr ⟨3, rfl⟩)

def beta (n : Nat) : Equal (Ω := assumptions n)
    (Contextual.subTm (command n).expression (Contextual.rootTail (.var 1) (.var 2) (.var 3))) (.var 5) :=
  (command n).point.jBeta (command n).tailTyping (command n).motiveTyping (command n).branchTyping

theorem inputs (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
    (p : Problem M.toStructuralModel) :
    ∀ a ∈ assumptions p.length, a.eval (Contextual.algebra M) (problemEnvironment M.toStructuralModel p) := by
  intro a ha
  rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
  rcases p with ⟨⟨⟨Γ, A, x⟩, n, T⟩, D, d⟩
  change Fin 4 at i
  fin_cases i
  · exact ⟨Γ, A, x, rfl, rfl, rfl⟩
  · refine ⟨M.toStructuralModel.pathContext A x, T, ?_, rfl⟩
    simp [Term.eval, Contextual.algebra, Contextual.operation, problemEnvironment]
  · exact ⟨T.total, D, rfl, rfl⟩
  · refine ⟨_, _, d, ?_, ?_, rfl⟩ <;>
      simp [Term.eval, Contextual.algebra, Contextual.operation, SquareKit.Internal.DependentJudgments.operation, problemEnvironment]

/-- This equality is obtained by interpreting the generated source proof. Its
motive and branch are genuinely dependent inputs over the complete telescope. -/
theorem interpreted_beta (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
    (p : Problem M.toStructuralModel) :
    Value.term (StructuralModel.Telescope.pullback M.toStructuralModel p.telescope
      (M.toStructuralModel.rootSub p.family p.term)).total
      (M.subTy p.motive (M.toStructuralModel.rootTail p.family p.term p.telescope))
      (M.subTm (M.j p.family p.term p.telescope p.motive p.branch)
        (M.toStructuralModel.rootTail p.family p.term p.telescope)) =
    Value.term (StructuralModel.Telescope.pullback M.toStructuralModel p.telescope
      (M.toStructuralModel.rootSub p.family p.term)).total
      (M.subTy p.motive (M.toStructuralModel.rootTail p.family p.term p.telescope)) p.branch := by
  have h := Contextual.interpret (beta p.length) M (problemEnvironment M.toStructuralModel p) (inputs M p)
  rcases p with ⟨⟨⟨Γ, A, x⟩, n, T⟩, D, d⟩
  simpa [Atom.eval, Term.eval, Command.expression, command, Contextual.algebra,
    Contextual.operation, SquareKit.Internal.DependentJudgments.operation, problemEnvironment] using h

end Examples.GuardedContextualJudgments
