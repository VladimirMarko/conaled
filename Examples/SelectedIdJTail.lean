import Examples.ReferenceDependentCalculus
import SquareKit.Internal.DependentJudgments.SelectedIdJRealization
import SquareKit.Internal.DependentJudgments.ReferenceSelectedMeaning

/-! A two-entry dependent tail exercises selected J realization and a second
composition. The final family and returned value depend on the preceding entry. -/
noncomputable section
namespace Examples.SelectedIdJTail
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.PathTransport.Typed
open StructuralModel
open ReferenceDependentCalculus.Native SelectedRealization
set_option backward.isDefEq.respectTransparency false

abbrev T : Telescope M.toStructuralModel (M.pathContext a point) 2 := .cons b (.cons c .nil)
abbrev D : M.Family T.total := fun z => Fin (z.1.2 + 1)
abbrev branch : M.Section (Telescope.pullback M.toStructuralModel T (M.rootSub a point)).total
    (M.subTy D (M.rootTail a point T)) := ⟨fun z => z.2⟩

def environment : Fin 5 → Value M.toStructuralModel :=
  ![.family M.empty a, .term M.empty a point, .telescope (M.pathContext a point) 2 T,
    .family T.total D,
    .term (Telescope.pullback M.toStructuralModel T (M.rootSub a point)).total
      (M.subTy D (M.rootTail a point T)) branch]

/-- No final J value is an input: quotation correctness comes from the local J law. -/
def code : Code M environment (.term T.total D (M.j a point T D branch)) :=
  Code.j ⟨.var 0, rfl⟩ ⟨.var 1, rfl⟩ ⟨.var 2, rfl⟩ ⟨.var 3, rfl⟩ ⟨.var 4, rfl⟩

/-- Reflexivity is realized locally at the chosen native point. -/
def reflexiveCode := Code.reflexivity (M := M) (ρ := environment)
  (Γ := M.empty) (A := a) (x := point)
  ⟨.var 0, rfl⟩ ⟨.var 1, rfl⟩

def identityCode : Code M environment (.substitution T.total T.total (M.idSub T.total)) :=
  ⟨Contextual.identitySub (Contextual.total (.var 2)), by
    simp [Term.eval, Contextual.algebra, Contextual.operation,
      SquareKit.Internal.DependentJudgments.operation, environment]⟩

def reindexedCode := Code.subTm code identityCode

def sample : T.total := ⟨⟨(M.rootSub a point).down PUnit.unit, 2⟩, ⟨2, by decide⟩⟩

theorem identity_selected :
    reindexedCode.quote.eval (algebra M) environment =
      code.quote.eval (algebra M) environment := by
  rw [reindexedCode.realizes, code.realizes]
  rfl

theorem chosen_value : ((M.j a point T D branch).down sample).val = 2 := rfl

theorem decoded : (code.quote.eval (algebra M) environment).termAt T.total D =
    some (M.j a point T D branch) := by
  rw [code.realizes]
  exact Value.termAt_term _ _ _

theorem selected_observation :
    ((code.quote.eval (algebra M) environment).termAt T.total D).map
      (fun t => (t.down sample).val) = some 2 := by
  rw [decoded]
  rfl

/-- Two genuine compiler-template uses: expand a leaf to J, then rename its
five typed inputs. This is not a phase-only map on a precomputed result. -/
def expand : Unit → Contextual.Expression (Fin 5) := fun _ => code.quote
def rename : Fin 5 → Contextual.Expression (Fin 5) := ![.var 1, .var 0, .var 2, .var 4, .var 3]
def renamedEnvironment : Fin 5 → Value M.toStructuralModel :=
  ![environment 1, environment 0, environment 2, environment 4, environment 3]

theorem input_roundtrip :
    (fun i => (rename i).eval (algebra M) renamedEnvironment) = environment := by
  funext i
  fin_cases i <;> rfl

theorem two_stage_observation :
    (((((.var () : Contextual.Expression Unit).subst expand).subst rename).eval
      (algebra M) renamedEnvironment).termAt T.total D).map
        (fun t => (t.down sample).val) = some 2 := by
  rw [Reference.SelectedMeaning.selected_preserved]
  change ((code.quote.eval (algebra M)
    (fun i => (rename i).eval (algebra M) renamedEnvironment)).termAt T.total D).map _ = _
  rw [input_roundtrip]
  exact selected_observation

end Examples.SelectedIdJTail
