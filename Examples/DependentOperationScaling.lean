import SquareKit.DependentOperation.Lowering
import Examples.IncrementalDependentNativeTrial
import Examples.IncrementalDependentCompositionalTrial

/-! Selected position applications for #358. This setup fixture is not a trial
submission or an empirical scaling result. -/
namespace Examples.DependentOperationScaling
open SquareKit.DependentOperation
open SquareKit.DependentOperation.Selector
open SquareKit.DependentBranchTheoryMaps

abbrev Context := Position

def input : ∀ n, Context n → Position n := fun _ => id

def client : Term Op Context 6 :=
  app (.reflect 6) (app (.pad 4) (app (.insert 3) (.hyp (1 : Position 3))))

def first : Substitution Op Context Context := fun n i => app (.reflect n) (.hyp i)
def second : Substitution Op Context Context := fun n i => app (.reset n) (.hyp i)

example : eval @operate input client = (3 : Position 6) := rfl
example : eval @operate input (client.graft first) = (2 : Position 6) := rfl
example : eval @operate input ((client.graft first).graft second) = (1 : Position 6) := rfl

/-- Actual target word, including the expansion of symmetric padding. -/
theorem selected_quote :
    (emit @lowInstructions (compile lowering client)).instructions =
      [.left,.left,.right,.mirror] := by
  rw [lowering_quote]
  rfl

theorem selected_total : (bytecode client).run runTotal (fun n v => total n (input n v)) = (6,3) := by
  rw [total_sound]
  rfl

theorem selected_distances :
    (bytecode ((client.graft first).graft second)).run runDistances
      (fun n v => distances n (input n v)) = (1,5) := by
  rw [distances_sound, eval_twice]
  rfl

abbrev Answer (n) := (i : Position n) × Fin (i.val+1)
def selected {n} (i : Position n) : Answer n := ⟨i,Fin.last i.val⟩

/-- The dependent selected tail follows the chosen output; it is not replaced
by an arbitrary inhabitant with the same bound. -/
theorem selected_twice {V W X : Nat → Type} (ρ : ∀ n, X n → Position n)
    (σ : Substitution Op V W) (τ : Substitution Op W X) {n} (t : Term Op V n) :
    selected (eval @lowOperate ρ (compile lowering ((t.graft σ).graft τ))) =
      selected (eval @operate
        (fun n v => eval @operate (fun k w => eval @operate ρ (τ k w)) (σ n v)) t) :=
  congrArg selected (lowering_twice ρ σ τ t)

example : selected (eval @lowOperate input
    (compile lowering ((client.graft first).graft second))) =
      (⟨1,1⟩ : Answer 6) := by
  rw [selected_twice]
  rfl

theorem wrong_selection_rejected :
    (bytecode ((client.graft first).graft second)).run runDistances
      (fun n v => distances n (input n v)) ≠ (0,6) := by
  rw [selected_distances]
  decide

/-- The local rule laws cannot justify reversing the two source operations. -/
example : operate (.reflect 3) (operate (.insert 2) (0 : Position 2)) ≠
    operate (.insert 2) (operate (.reflect 2) (0 : Position 2)) := reflect_insert_fails

/-- Retain the former native and shared selected-result contracts. These are
regressions, not held-out operations in the new trial. -/
example : (IncrementalNative.translate
    (IncrementalNative.program Examples.IncrementalDependentTrialSpec.demo)).exec 3 =
      Examples.IncrementalDependentTrialSpec.demoAnswer := IncrementalNative.demo_value

example : (IncrementalCompositional.targetCode Examples.IncrementalDependentTrialSpec.demo).run
    (IncrementalCompositional.env 3) = Examples.IncrementalDependentTrialSpec.demoAnswer :=
  IncrementalCompositional.demo_execution

end Examples.DependentOperationScaling
