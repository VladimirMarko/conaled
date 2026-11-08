import SquareKit.DependentOperation.Lowering
import Examples.DependentOperationTrialSpec
namespace Shared358
open SquareKit.DependentOperation
open SquareKit.DependentOperation.Selector (Position)
namespace Base := SquareKit.DependentOperation.Selector
namespace Spec := Examples.DependentOperationTrialSpec
inductive Op : Signature where
  | old {n m} : Base.Op n m → Op n m
  | rotate (n) : Op n n

def operate : ∀ {n m}, Op n m → Position n → Position m
  | _, _, .old o, i => Base.operate o i
  | n, _, .rotate _, i => Spec.rotate n i
inductive Word where
  | old : Base.Low → Word
  | rotate
  deriving DecidableEq, Repr
inductive Macro where
  | old : Base.Macro → Macro
  | rotate
  deriving DecidableEq, Repr

def instructions : ∀ {n m}, Op n m → List Macro
  | _, _, .old o => (Base.instructions o).map Macro.old
  | _, _, .rotate _ => [.rotate]
def lower : Macro → List Word
  | .old m => (Base.lower m).map Word.old
  | .rotate => [.rotate]
def runTotal : Word → Nat × Nat → Nat × Nat
  | .old w, s => Base.runTotal w s
  | .rotate, (n,i) => (n,(i+1) % (n+1))
def bytecode {V : Nat → Type} {n} (t : Term Op V n) : Code Word V :=
  (emit @instructions t).lower lower

theorem quotation {V : Nat → Type} {n} (t : Term Op V n) :
    bytecode t = emit (fun o => (instructions o).flatMap lower) t :=
  emit_lower @instructions lower t

theorem total_local {n m} (o : Op n m) (i : Position n) :
    ((instructions o).flatMap lower).foldl (fun s k => runTotal k s) (Base.total n i) =
      Base.total m (operate o i) := by
  cases o with
  | old o => cases o <;> rfl
  | rotate => rfl

theorem total_sound {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    (bytecode t).run runTotal (fun n v => Base.total n (ρ n v)) =
      Base.total n (eval @operate ρ t) := by
  rw [quotation]
  exact emit_sound @operate (fun o => (instructions o).flatMap lower)
    runTotal Base.total total_local ρ t

abbrev Context (_ : Nat) := Unit
def env (n) (_ : Context n) : Position n := ⟨min 3 n, by omega⟩
def stageOne : Term Op Context 4 := app (.rotate 4) (.hyp ())
theorem stageOne_meaning : eval @operate env stageOne = Spec.stageOne 3 := rfl
theorem stageOne_quote : (bytecode stageOne).instructions = [.rotate] := rfl
theorem stageOne_result : (bytecode stageOne).run runTotal
    (fun n v => Base.total n (env n v)) = (4,4) := rfl
theorem empty_result {n} (i : Position n) :
    (bytecode (.hyp () : Term Op Context n)).run runTotal
      (fun _ _ => Base.total n i) = Base.total n i := rfl
theorem wraparound (n) : operate (.rotate n) (Fin.last n) = 0 := by
  apply Fin.ext
  simp [operate, Spec.rotate]
end Shared358
