import Lean.Util.CollectAxioms
import Lean.DeclarationRange
import SquareKit.DependentOperation.Lowering
import Examples.DependentOperationTrialSpec
namespace Shared358
open SquareKit.DependentOperation
open SquareKit.DependentOperation.Selector (Position)

-- Repaired independent client compositions: only Spec.backward replaces rotate.
def repairedStageOne (i : Position 4) := Examples.DependentOperationTrialSpec.backward 4 i
def repairedStageTwo (i : Position 5) :=
  Examples.DependentOperationTrialSpec.half 5 (Examples.DependentOperationTrialSpec.backward 5
    (Examples.DependentOperationTrialSpec.half 5 (Examples.DependentOperationTrialSpec.backward 5 i)))
def repairedStageThree (i : Position 8) : Position 7 :=
  SquareKit.DependentOperation.Selector.operate (.insert 6)
    (SquareKit.DependentOperation.Selector.operate (.reflect 6)
      (Examples.DependentOperationTrialSpec.backward 6
        (SquareKit.DependentOperation.Selector.operate (.pad 4)
          (SquareKit.DependentOperation.Selector.operate (.reflect 4)
            (Examples.DependentOperationTrialSpec.compress 9
              (SquareKit.DependentOperation.Selector.operate (.insert 8)
                (Examples.DependentOperationTrialSpec.half 8
                  (Examples.DependentOperationTrialSpec.backward 8 i))))))))
theorem repaired_oracles :
    repairedStageOne 3 = 2 ∧ repairedStageTwo 4 = 0 ∧
    repairedStageThree 6 = 4 ∧ repairedStageThree (Fin.rev 6) = 3 ∧
    repairedStageThree (Fin.rev 0) = 5 := by decide

inductive Op : Signature where
  | old {n m} : SquareKit.DependentOperation.Selector.Op n m → Op n m
  | rotate (n) : Op n n
  | half (n) : Op n n
  | compress (n) : Op n (n/2)

def operate : ∀ {n m}, Op n m → Position n → Position m
  | _, _, .old o, i => SquareKit.DependentOperation.Selector.operate o i
  | n, _, .rotate _, i => Examples.DependentOperationTrialSpec.backward n i
  | n, _, .half _, i => Examples.DependentOperationTrialSpec.half n i
  | n, _, .compress _, i => Examples.DependentOperationTrialSpec.compress n i
inductive Word where
  | old : SquareKit.DependentOperation.Selector.Low → Word
  | rotate
  | half
  | compress
  deriving DecidableEq, Repr
inductive Macro where
  | old : SquareKit.DependentOperation.Selector.Macro → Macro
  | rotate
  | half
  | compress
  deriving DecidableEq, Repr

def instructions : ∀ {n m}, Op n m → List Macro
  | _, _, .old o => (SquareKit.DependentOperation.Selector.instructions o).map Macro.old
  | _, _, .rotate _ => [.rotate]
  | _, _, .half _ => [.half]
  | _, _, .compress _ => [.compress]
def lower : Macro → List Word
  | .old m => (SquareKit.DependentOperation.Selector.lower m).map Word.old
  | .rotate => [.rotate]
  | .half => [.half]
  | .compress => [.compress]
def runTotal : Word → Nat × Nat → Nat × Nat
  | .old w, s => SquareKit.DependentOperation.Selector.runTotal w s
  | .rotate, (n,i) => (n,(i+n) % (n+1))
  | .half, (n,i) => (n,i/2)
  | .compress, (n,i) => (n/2,i/2)
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
  | half => rfl
  | compress => rfl

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
theorem stageOne_meaning : eval @operate env stageOne = repairedStageOne 3 := rfl
theorem stageOne_quote : (bytecode stageOne).instructions = [.rotate] := rfl
theorem stageOne_result : (bytecode stageOne).run runTotal
    (fun n v => SquareKit.DependentOperation.Selector.total n (env n v)) = (4,2) := rfl
theorem empty_result {n} (i : Position n) :
    (bytecode (.hyp () : Term Op Context n)).run runTotal
      (fun _ _ => SquareKit.DependentOperation.Selector.total n i) = SquareKit.DependentOperation.Selector.total n i := rfl
theorem wraparound (n) : operate (.rotate n) (0 : Position n) = Fin.last n := by
  apply Fin.ext
  simp [operate, Examples.DependentOperationTrialSpec.backward]

def runDistances : Word → Nat × Nat → Nat × Nat
  | .old w, s => SquareKit.DependentOperation.Selector.runDistances w s
  | .rotate, (l,r) => let j := (l+(l+r)) % (l+r+1); (j,l+r-j)
  | .half, (l,r) => (l/2,l+r-l/2)
  | .compress, (l,r) => (l/2,(l+r)/2-l/2)
theorem distances_local {n m} (o : Op n m) (i : Position n) :
    ((instructions o).flatMap lower).foldl (fun s k => runDistances k s)
      (SquareKit.DependentOperation.Selector.distances n i) =
      SquareKit.DependentOperation.Selector.distances m (operate o i) := by
  have hi := i.isLt
  have hn : i.val + (n-i.val) = n := by omega
  cases o with
  | old o =>
    cases o <;> simp [instructions, lower, runDistances, operate,
      SquareKit.DependentOperation.Selector.instructions,
      SquareKit.DependentOperation.Selector.lower,
      SquareKit.DependentOperation.Selector.runDistances,
      SquareKit.DependentOperation.Selector.distances,
      SquareKit.DependentOperation.Selector.operate, Fin.rev] <;> omega
  | rotate => simp [instructions, lower, runDistances, operate,
      SquareKit.DependentOperation.Selector.distances,
      Examples.DependentOperationTrialSpec.backward, hn]
  | half => simp [instructions, lower, runDistances, operate,
      SquareKit.DependentOperation.Selector.distances,
      Examples.DependentOperationTrialSpec.half, hn]
  | compress => simp [instructions, lower, runDistances, operate,
      SquareKit.DependentOperation.Selector.distances,
      Examples.DependentOperationTrialSpec.compress, hn]
theorem distances_sound {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    (bytecode t).run runDistances
      (fun n v => SquareKit.DependentOperation.Selector.distances n (ρ n v)) =
      SquareKit.DependentOperation.Selector.distances n (eval @operate ρ t) := by
  rw [quotation]
  exact emit_sound @operate (fun o => (instructions o).flatMap lower)
    runDistances SquareKit.DependentOperation.Selector.distances distances_local ρ t

def envFour (n) (_ : Context n) : Position n := ⟨min 4 n, by omega⟩
def stageTwo : Term Op Context 5 :=
  app (.half 5) (app (.rotate 5) (app (.half 5) (app (.rotate 5) (.hyp ()))))
theorem stageTwo_meaning : eval @operate envFour stageTwo =
    repairedStageTwo 4 := rfl
theorem stageTwo_quote : (bytecode stageTwo).instructions =
    [.rotate,.half,.rotate,.half] := rfl
theorem stageTwo_total : (bytecode stageTwo).run runTotal
    (fun n v => SquareKit.DependentOperation.Selector.total n (envFour n v)) = (5,0) := rfl
theorem stageTwo_distances : (bytecode stageTwo).run runDistances
    (fun n v => SquareKit.DependentOperation.Selector.distances n (envFour n v)) = (0,5) := rfl
-- Local correctness relates each primitive to its executor; it does not assert
-- equality between two different orders of source operations.
theorem rotate_half_do_not_commute :
    operate (.half 5) (operate (.rotate 5) (0 : Position 5)) ≠
    operate (.rotate 5) (operate (.half 5) (0 : Position 5)) := by decide



abbrev Unary := List Unit × List Unit
def unary (n) (i : Position n) : Unary :=
  (List.replicate i.val (), List.replicate (n-i.val) ())
def runUnary : Word → Unary → Unary
  | .old .mirror, (l,r) => (r,l)
  | .old .left, (l,r) => (() :: l,r)
  | .old .right, (l,r) => (l,() :: r)
  | .old .origin, (l,r) => ([],List.replicate (l.length+r.length) ())
  | .rotate, (l,r) => let j := (l.length+(l.length+r.length)) % (l.length+r.length+1)
                    (List.replicate j (),List.replicate (l.length+r.length-j) ())
  | .half, (l,r) => (List.replicate (l.length/2) (),
                     List.replicate (l.length+r.length-l.length/2) ())
  | .compress, (l,r) => (List.replicate (l.length/2) (),
                         List.replicate ((l.length+r.length)/2-l.length/2) ())
theorem unary_local {n m} (o : Op n m) (i : Position n) :
    ((instructions o).flatMap lower).foldl (fun s k => runUnary k s) (unary n i) =
      unary m (operate o i) := by
  have hi := i.isLt
  have hn : i.val + (n-i.val) = n := by omega
  cases o with
  | old o =>
    cases o <;> simp [instructions, lower, runUnary, unary, operate,
      SquareKit.DependentOperation.Selector.instructions,
      SquareKit.DependentOperation.Selector.lower,
      SquareKit.DependentOperation.Selector.operate, Fin.rev,
      List.replicate_succ, hn,
      show n - (n-i.val) = i.val by omega,
      show n+1-(i.val+1) = n-i.val by omega,
      show n+2-(i.val+1) = n-i.val+1 by omega]
  | rotate => simp [instructions, lower, runUnary, unary, operate,
      Examples.DependentOperationTrialSpec.backward, hn]
  | half => simp [instructions, lower, runUnary, unary, operate,
      Examples.DependentOperationTrialSpec.half, hn]
  | compress => simp [instructions, lower, runUnary, unary, operate,
      Examples.DependentOperationTrialSpec.compress, hn]
theorem unary_sound {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    (bytecode t).run runUnary (fun n v => unary n (ρ n v)) =
      unary n (eval @operate ρ t) := by
  rw [quotation]
  exact emit_sound @operate (fun o => (instructions o).flatMap lower)
    runUnary unary unary_local ρ t

theorem total_twice {V W X : Nat → Type} (ρ : ∀ n, X n → Position n)
    (σ : Substitution Op V W) (τ : Substitution Op W X) {n} (t : Term Op V n) :
    (bytecode ((t.graft σ).graft τ)).run runTotal
      (fun n v => SquareKit.DependentOperation.Selector.total n (ρ n v)) =
    SquareKit.DependentOperation.Selector.total n
      (eval @operate (fun n v => eval @operate
        (fun k w => eval @operate ρ (τ k w)) (σ n v)) t) := by
  rw [total_sound, eval_twice]
theorem distances_twice {V W X : Nat → Type} (ρ : ∀ n, X n → Position n)
    (σ : Substitution Op V W) (τ : Substitution Op W X) {n} (t : Term Op V n) :
    (bytecode ((t.graft σ).graft τ)).run runDistances
      (fun n v => SquareKit.DependentOperation.Selector.distances n (ρ n v)) =
    SquareKit.DependentOperation.Selector.distances n
      (eval @operate (fun n v => eval @operate
        (fun k w => eval @operate ρ (τ k w)) (σ n v)) t) := by
  rw [distances_sound, eval_twice]
theorem unary_twice {V W X : Nat → Type} (ρ : ∀ n, X n → Position n)
    (σ : Substitution Op V W) (τ : Substitution Op W X) {n} (t : Term Op V n) :
    (bytecode ((t.graft σ).graft τ)).run runUnary
      (fun n v => unary n (ρ n v)) =
    unary n (eval @operate (fun n v => eval @operate
        (fun k w => eval @operate ρ (τ k w)) (σ n v)) t) := by
  rw [unary_sound, eval_twice]

def envSix (n) (_ : Context n) : Position n := ⟨min 6 n, by omega⟩
def stageThree : Term Op Context 7 :=
  app (.old (.insert 6)) (app (.old (.reflect 6)) (app (.rotate 6)
    (app (.old (.pad 4)) (app (.old (.reflect 4)) (app (.compress 9)
      (app (.old (.insert 8)) (app (.half 8) (app (.rotate 8) (.hyp ())))))))))
def reflectVars : Substitution Op Context Context := fun n _ =>
  app (.old (.reflect n)) (.hyp ())
def resetVars : Substitution Op Context Context := fun n _ =>
  app (.old (.reset n)) (.hyp ())
theorem stageThree_meaning : eval @operate envSix stageThree =
    repairedStageThree 6 := rfl
theorem stageThree_quote : (bytecode stageThree).instructions =
    [.rotate,.half,.old .left,.compress,.old .mirror,.old .left,.old .right,
      .rotate,.old .mirror,.old .left] := rfl
theorem stageThree_meaning_reflected : eval @operate envSix (stageThree.graft reflectVars) =
    repairedStageThree (Fin.rev 6) := rfl
theorem stageThree_meaning_twice : eval @operate envSix
    ((stageThree.graft reflectVars).graft resetVars) =
    repairedStageThree (Fin.rev 0) := rfl

theorem stageThree_total : (bytecode stageThree).run runTotal
    (fun n v => SquareKit.DependentOperation.Selector.total n (envSix n v)) = (7,4) := rfl
theorem stageThree_distances : (bytecode stageThree).run runDistances
    (fun n v => SquareKit.DependentOperation.Selector.distances n (envSix n v)) = (4,3) := rfl
theorem stageThree_unary : (bytecode stageThree).run runUnary
    (fun n v => unary n (envSix n v)) =
      (List.replicate 4 (),List.replicate 3 ()) := rfl
theorem stageThree_reflected : (bytecode (stageThree.graft reflectVars)).run runTotal
    (fun n v => SquareKit.DependentOperation.Selector.total n (envSix n v)) = (7,3) := rfl
theorem stageThree_twice : (bytecode ((stageThree.graft reflectVars).graft resetVars)).run runTotal
    (fun n v => SquareKit.DependentOperation.Selector.total n (envSix n v)) = (7,5) := rfl

def Tail (n) := (i : Position n) × Fin (i.val+1)
def selectedTail {n} (i : Position n) : Tail n := ⟨i,Fin.last i.val⟩
def recoverPosition (n j : Nat) : Position n := ⟨min j n,by omega⟩
theorem recover_position {n} (i : Position n) : recoverPosition n i.val = i := by
  apply Fin.ext
  simp [recoverPosition, Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)]
theorem total_tail {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    selectedTail (recoverPosition n ((bytecode t).run runTotal
      (fun n v => SquareKit.DependentOperation.Selector.total n (ρ n v))).2) =
      selectedTail (eval @operate ρ t) := by
  rw [total_sound]
  exact congrArg selectedTail (recover_position _)
theorem distances_tail {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    selectedTail (recoverPosition n ((bytecode t).run runDistances
      (fun n v => SquareKit.DependentOperation.Selector.distances n (ρ n v))).1) =
      selectedTail (eval @operate ρ t) := by
  rw [distances_sound]
  exact congrArg selectedTail (recover_position _)
theorem unary_tail {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    selectedTail (recoverPosition n ((bytecode t).run runUnary
      (fun n v => unary n (ρ n v))).1.length) =
      selectedTail (eval @operate ρ t) := by
  rw [unary_sound]
  simp only [unary, List.length_replicate]
  exact congrArg selectedTail (recover_position _)
theorem stageThree_wrong : eval @operate envSix stageThree ≠ (0 : Position 7) := by decide

def includeOld : Compiler SquareKit.DependentOperation.Selector.Op Op where
  certificate r := app (.old r.op) (.hyp ⟨(),rfl⟩)
theorem includeOld_local : includeOld.LocalMeaning
    (model Position @SquareKit.DependentOperation.Selector.operate)
    (model Position @operate) (fun _ => id) := by
  intro r xs
  rfl
theorem includeOld_meaning {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term SquareKit.DependentOperation.Selector.Op V n) :
    eval @operate ρ (compile includeOld t) =
      eval @SquareKit.DependentOperation.Selector.operate ρ t :=
  compile_meaning includeOld @SquareKit.DependentOperation.Selector.operate
    @operate (fun _ => id) includeOld_local ρ t
theorem recovered_selector {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term SquareKit.DependentOperation.Selector.Op V n) :
    (bytecode (compile includeOld t)).run runTotal
      (fun n v => SquareKit.DependentOperation.Selector.total n (ρ n v)) =
      SquareKit.DependentOperation.Selector.total n
        (eval @SquareKit.DependentOperation.Selector.operate ρ t) := by
  rw [total_sound, includeOld_meaning]
theorem reflect_pad (n) (i : Position n) :
    operate (.old (.reflect (n+2))) (operate (.old (.pad n)) i) =
    operate (.old (.pad n)) (operate (.old (.reflect n)) i) :=
  SquareKit.DependentOperation.Selector.reflect_pad n i
theorem reflect_insert_fails :
    operate (.old (.reflect 3)) (operate (.old (.insert 2)) (0 : Position 2)) ≠
      operate (.old (.insert 2)) (operate (.old (.reflect 2)) (0 : Position 2)) := by decide

theorem repaired_interaction_values :
    operate (.half 5) (operate (.rotate 5) (0 : Position 5)) = 2 ∧
    operate (.rotate 5) (operate (.half 5) (0 : Position 5)) = 5 := by decide
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
