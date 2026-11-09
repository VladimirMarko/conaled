import SquareKit.GuardedStreamCompiler
import Applications.Progress.Streams
import Mathlib.Data.List.GetD

namespace SquareKit.GuardedStreamCompiler
open GuardedStreams

variable {Const Param Ref Op Bin A : Type}
local notation "Syntax" => Body Const Param Ref Op Bin

/-- Operational inputs for coordinate evaluation. In particular an indexed
operation may read an available parameter at its coordinate; causality alone
would not provide this operational contract. -/
structure Execution (Const Param Ref Op Bin A : Type) where
  constant : Const → A
  parameter : Param → Nat → A
  reference : Ref → Nat → A
  operation : Op → Nat → A → A
  binary : Bin → A → A → A

namespace Execution

def meaning (E : Execution Const Param Ref Op Bin A) : Meaning Const Param Ref Op Bin A where
  constant := E.constant
  parameter := E.parameter
  reference := E.reference
  operation o s n := E.operation o n (s n)
  causal o n _s _t h := congrArg (E.operation o n) (h n (Nat.le_refl n))
  binary := E.binary

/-- Primitive compatibility, without a whole-program correctness premise. -/
structure Realizes (E : Execution Const Param Ref Op Bin A)
    (M : Meaning Const Param Ref Op Bin A) : Prop where
  constant : E.constant = M.constant
  parameter : E.parameter = M.parameter
  reference : E.reference = M.reference
  operation : ∀ o s n, E.operation o n (s n) = M.operation o s n
  binary : E.binary = M.binary

def eval (E : Execution Const Param Ref Op Bin A) : Syntax → Stream A → Nat → A
  | .recur, s, n => s n
  | .param p, _, n => E.parameter p n
  | .ref r, _, n => E.reference r n
  | .delay c _, _, 0 => E.constant c
  | .delay _ t, s, n + 1 => E.eval t s n
  | .app o t, s, n => E.operation o n (E.eval t s n)
  | .zip o t u, s, n => E.binary o (E.eval t s n) (E.eval u s n)

theorem eval_denote (E : Execution Const Param Ref Op Bin A) (t : Syntax) (s : Stream A) :
    E.eval t s = denote E.meaning t s := by
  induction t with
  | recur | param | ref => rfl
  | delay c t ih => funext n; cases n <;> simp [eval, denote, cons, meaning, ih]
  | app o t ih => funext n; simp [eval, denote, meaning, ih]
  | zip o t u ih jh => funext n; simp [eval, denote, meaning, ih, jh]

theorem eval_realizes (E : Execution Const Param Ref Op Bin A)
    (M : Meaning Const Param Ref Op Bin A) (R : E.Realizes M) (t : Syntax) (s : Stream A) :
    E.eval t s = denote M t s := by
  induction t with
  | recur => rfl
  | param => simp [eval, denote, R.parameter]
  | ref => simp [eval, denote, R.reference]
  | delay c t ih => funext n; cases n <;> simp [eval, denote, cons, R.constant, ih]
  | app o t ih => funext n; simp [eval, denote, ih, R.operation]
  | zip o t u ih jh => funext n; simp [eval, denote, R.binary, ih, jh]

/-- An executable compilation target, constructed from local operations. -/
def target (E : Execution Const Param Ref Op Bin A) : Target Const Param Ref Op Bin :=
  functionTarget E.meaning

theorem compiled_eval (E : Execution Const Param Ref Op Bin A) (t : Syntax) :
    compile E.target t = E.eval t := by
  funext s
  exact (congrFun (compile_sound E.target E.meaning (functionSound E.meaning) t) s).trans
    (E.eval_denote t s).symm

/-- Finite stored coefficients agree with an independently specified stream. -/
def Agrees (xs : List A) (s : Stream A) : Prop :=
  ∀ i, i < xs.length → xs[i]? = some (s i)

def history (seed : A) (xs : List A) : Stream A := fun i => xs[i]?.getD seed

def step (E : Execution Const Param Ref Op Bin A) (t : Syntax) (seed : A)
    (xs : List A) : A × List A :=
  let a := E.eval t (history seed xs) xs.length
  (a, xs ++ [a])

theorem next_correct (E : Execution Const Param Ref Op Bin A) (M : Meaning Const Param Ref Op Bin A)
    (R : E.Realizes M) (t : Syntax) (ht : guarded t = true) (seed : A)
    (s : Stream A) (hs : s = denote M t s) (xs : List A) (h : Agrees xs s) :
    (E.step t seed xs).1 = s xs.length := by
  change E.eval t (history seed xs) xs.length = s xs.length
  rw [E.eval_realizes M R]
  have hh : ∀ i, i < xs.length → history seed xs i = s i := by
    intro i hi
    simp [history, h i hi]
  exact (denote_guarded M t ht xs.length _ s hh).trans (congrFun hs xs.length).symm

theorem agrees_append {xs : List A} {s : Stream A} (h : Agrees xs s) :
    Agrees (xs ++ [s xs.length]) s := by
  intro i hi
  by_cases hj : i < xs.length
  · rw [List.getElem?_append_left hj]; exact h i hj
  · have he : i = xs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simp

theorem step_agrees (E : Execution Const Param Ref Op Bin A) (M : Meaning Const Param Ref Op Bin A)
    (R : E.Realizes M) (t : Syntax) (ht : guarded t = true) (seed : A)
    (s : Stream A) (hs : s = denote M t s) (xs : List A) (h : Agrees xs s) :
    Agrees (E.step t seed xs).2 s := by
  have hn := E.next_correct M R t ht seed s hs xs h
  change Agrees (xs ++ [(E.step t seed xs).1]) s
  rw [hn]
  exact agrees_append h

/-- One producer transition evaluates a finite body and appends its coefficient.
The Progress step count counts outputs, not primitive operations or physical time. -/
theorem delivery (E : Execution Const Param Ref Op Bin A) (t : Syntax) (seed : A)
    (xs : List A) (n : Nat) :
    Progress.Delivers (Progress.guarded (E.step t seed)) xs
      (Progress.unfold (E.step t seed) xs n) (Progress.advance (E.step t seed) xs n) n :=
  Progress.guarded_delivery _ _ _

theorem emitted_correct (E : Execution Const Param Ref Op Bin A)
    (M : Meaning Const Param Ref Op Bin A) (R : E.Realizes M)
    (t : Syntax) (ht : guarded t = true) (seed : A) (s : Stream A)
    (hs : s = denote M t s) (n : Nat) (xs : List A) (h : Agrees xs s) :
    Progress.unfold (E.step t seed) xs n = (List.range n).map (fun i => s (xs.length + i)) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Progress.unfold, E.next_correct M R t ht seed s hs xs h,
      ih _ (E.step_agrees M R t ht seed s hs xs h)]
    simp [List.range_succ_eq_map, step, Nat.add_comm, Nat.add_left_comm]

end Execution
end SquareKit.GuardedStreamCompiler
