import Lean.Util.CollectAxioms
import Lean.DeclarationRange
import SquareKit.DependentOperation.Lowering
import Examples.DependentOperationTrialSpec
namespace Shared358
open SquareKit.DependentOperation
open SquareKit.DependentOperation.Selector (Position)
inductive Op : Signature where
  | old {n m} : SquareKit.DependentOperation.Selector.Op n m → Op n m
  | rotate (n) : Op n n

def operate : ∀ {n m}, Op n m → Position n → Position m
  | _, _, .old o, i => SquareKit.DependentOperation.Selector.operate o i
  | n, _, .rotate _, i => Examples.DependentOperationTrialSpec.rotate n i
inductive Word where
  | old : SquareKit.DependentOperation.Selector.Low → Word
  | rotate
  deriving DecidableEq, Repr
inductive Macro where
  | old : SquareKit.DependentOperation.Selector.Macro → Macro
  | rotate
  deriving DecidableEq, Repr

def instructions : ∀ {n m}, Op n m → List Macro
  | _, _, .old o => (SquareKit.DependentOperation.Selector.instructions o).map Macro.old
  | _, _, .rotate _ => [.rotate]
def lower : Macro → List Word
  | .old m => (SquareKit.DependentOperation.Selector.lower m).map Word.old
  | .rotate => [.rotate]
def runTotal : Word → Nat × Nat → Nat × Nat
  | .old w, s => SquareKit.DependentOperation.Selector.runTotal w s
  | .rotate, (n,i) => (n,(i+1) % (n+1))
def bytecode {V : Nat → Type} {n} (t : Term Op V n) : Code Word V :=
  (emit @instructions t).lower lower

theorem quotation {V : Nat → Type} {n} (t : Term Op V n) :
    bytecode t = emit (fun o => (instructions o).flatMap lower) t :=
  emit_lower @instructions lower t

theorem total_local {n m} (o : Op n m) (i : Position n) :
    ((instructions o).flatMap lower).foldl (fun s k => runTotal k s) (SquareKit.DependentOperation.Selector.total n i) =
      SquareKit.DependentOperation.Selector.total m (operate o i) := by
  cases o with
  | old o => cases o <;> simp [instructions, lower, runTotal, operate, SquareKit.DependentOperation.Selector.instructions, SquareKit.DependentOperation.Selector.lower, SquareKit.DependentOperation.Selector.runTotal, SquareKit.DependentOperation.Selector.total, SquareKit.DependentOperation.Selector.operate, Fin.rev]
  | rotate => rfl

theorem total_sound {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    (bytecode t).run runTotal (fun n v => SquareKit.DependentOperation.Selector.total n (ρ n v)) =
      SquareKit.DependentOperation.Selector.total n (eval @operate ρ t) := by
  rw [quotation]
  exact emit_sound @operate (fun o => (instructions o).flatMap lower)
    runTotal SquareKit.DependentOperation.Selector.total total_local ρ t

abbrev Context (_ : Nat) := Unit
def env (n) (_ : Context n) : Position n := ⟨min 3 n, by omega⟩
def stageOne : Term Op Context 4 := app (.rotate 4) (.hyp ())
theorem stageOne_meaning : eval @operate env stageOne = Examples.DependentOperationTrialSpec.stageOne 3 := rfl
theorem stageOne_quote : (bytecode stageOne).instructions = [.rotate] := rfl
theorem stageOne_result : (bytecode stageOne).run runTotal
    (fun n v => SquareKit.DependentOperation.Selector.total n (env n v)) = (4,4) := rfl
theorem empty_result {n} (i : Position n) :
    (bytecode (.hyp () : Term Op Context n)).run runTotal
      (fun _ _ => SquareKit.DependentOperation.Selector.total n i) = SquareKit.DependentOperation.Selector.total n i := rfl
theorem wraparound (n) : operate (.rotate n) (Fin.last n) = 0 := by
  apply Fin.ext
  simp [operate, Examples.DependentOperationTrialSpec.rotate]
end Shared358


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := env.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) (#[] : Array (Name × ConstantInfo))
  let mut checked : Nat := 0
  let mut runtime : Nat := 0
  for (n, ci) in roots do
    if (env.getModuleIdxFor? n).isSome then continue
    if ci.isUnsafe then
      if (Lean.declRangeExt.find? env n).isSome then
        throwError "AUDIT FAIL source unsafe {n}"
      runtime := runtime + 1
      continue
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless a == `propext || a == `Classical.choice || a == `Quot.sound do
        throwError "AUDIT FAIL {n}: {a}"
    logInfo m!"AUDIT ROOT {n}: {axioms}"
    checked := checked + 1
  if checked == 0 then throwError "AUDIT EMPTY"
  logInfo m!"AUDIT PASSED {checked} logical declarations; {runtime} generated unsafe runtime declarations excluded"
