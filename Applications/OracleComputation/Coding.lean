import Applications.OracleComputation.Core
import Mathlib.Logic.Encodable.Basic

/-! Executable finite descriptions and their concrete decoding retraction. -/

namespace OracleComputation

/-- A stack algebra interprets instruction tags; its carrier need not be executable. -/
structure Algebra (α : Type) where
  zero : α
  succ : α
  left : α
  right : α
  query : α
  pair : α → α → α
  comp : α → α → α
  prec : α → α → α
  rfind : α → α

def interpret (a : Algebra α) : Code → α
  | .zero => a.zero
  | .succ => a.succ
  | .left => a.left
  | .right => a.right
  | .query => a.query
  | .pair f g => a.pair (interpret a f) (interpret a g)
  | .comp f g => a.comp (interpret a f) (interpret a g)
  | .prec f g => a.prec (interpret a f) (interpret a g)
  | .rfind f => a.rfind (interpret a f)

/-- Tags 0–4 push primitives, 5–7 combine two entries, and 8 minimizes one. -/
def step (a : Algebra α) : Nat → List α → Option (List α)
  | 0, s => some (a.zero :: s)
  | 1, s => some (a.succ :: s)
  | 2, s => some (a.left :: s)
  | 3, s => some (a.right :: s)
  | 4, s => some (a.query :: s)
  | 5, g :: f :: s => some (a.pair f g :: s)
  | 6, g :: f :: s => some (a.comp f g :: s)
  | 7, g :: f :: s => some (a.prec f g :: s)
  | 8, f :: s => some (a.rfind f :: s)
  | _, _ => none

def run (a : Algebra α) : List Nat → List α → Option (List α)
  | [], s => some s
  | i :: is, s => (step a i s).bind (run a is)

/-- Finite symbolic output, independent of the supplied oracle. -/
def emit : Code → List Nat
  | .zero => [0]
  | .succ => [1]
  | .left => [2]
  | .right => [3]
  | .query => [4]
  | .pair f g => emit f ++ emit g ++ [5]
  | .comp f g => emit f ++ emit g ++ [6]
  | .prec f g => emit f ++ emit g ++ [7]
  | .rfind f => emit f ++ [8]

theorem run_append (a : Algebra α) (xs ys : List Nat) (s : List α) :
    run a (xs ++ ys) s = (run a xs s).bind (run a ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, run]
    cases step a x s <;> simp [ih]

/-- Arbitrary preserved stack tails expose operand order and compositionality. -/
theorem run_emit (a : Algebra α) (c : Code) (s : List α) :
    run a (emit c) s = some (interpret a c :: s) := by
  induction c generalizing s with
  | zero | succ | left | right | query => rfl
  | pair f g hf hg => simp [emit, run_append, hf, hg, run, step, interpret]
  | comp f g hf hg => simp [emit, run_append, hf, hg, run, step, interpret]
  | prec f g hf hg => simp [emit, run_append, hf, hg, run, step, interpret]
  | rfind f hf => simp [emit, run_append, hf, run, step, interpret]

def syntaxAlgebra : Algebra Code :=
  ⟨.zero, .succ, .left, .right, .query, .pair, .comp, .prec, .rfind⟩

@[simp] theorem interpret_syntax (c : Code) : interpret syntaxAlgebra c = c := by
  induction c <;> simp_all [interpret, syntaxAlgebra]

/-- Reject both malformed instructions and non-singleton final stacks. -/
def parse (xs : List Nat) : Option Code :=
  match run syntaxAlgebra xs [] with
  | some [c] => some c
  | _ => none

@[simp] theorem parse_emit (c : Code) : parse (emit c) = some c := by
  simp [parse, run_emit]

instance : Encodable Code := Encodable.ofLeftInjection emit parse parse_emit

/-- Numeric descriptions use the standard executable encoding of finite lists. -/
def index (c : Code) : Nat := Encodable.encode c

def ofIndex (n : Nat) : Code := (Encodable.decode n).getD .zero

@[simp] theorem ofIndex_index (c : Code) : ofIndex (index c) = c := by
  simp [ofIndex, index, Encodable.encodek]

theorem index_injective : Function.Injective index := by
  intro c d h
  simpa using congrArg ofIndex h

/-- Adequate enumeration of the relative class; no effective universal evaluator is assumed. -/
theorem recursiveIn_iff_exists_index {oracle f : Nat →. Nat} :
    Nat.RecursiveIn {oracle} f ↔ ∃ n, eval oracle (ofIndex n) = f := by
  rw [recursiveIn_iff_exists_code]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨index c, by simpa using hc⟩
  · rintro ⟨n, hn⟩
    exact ⟨ofIndex n, hn⟩

end OracleComputation
