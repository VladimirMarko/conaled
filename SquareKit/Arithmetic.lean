import FirstOrder
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Algebra.Ring.Defs

/-! A single source vocabulary reused by exact, incremental, interval and stack backends. -/
namespace Arithmetic
open FirstOrderCompiler

inductive Prim : Ty → Ty → Type where
  | literal : Int → Prim .unit .base
  | add : Prim (.prod .base .base) .base
  | mul : Prim (.prod .base .base) .base
  | neg : Prim .base .base

def meaning {R : Type} [Ring R] : {a b : Ty} → Prim a b → Val R a → Val R b
  | _, _, .literal n, _ => n
  | _, _, .add, p => p.1 + p.2
  | _, _, .mul, p => p.1 * p.2
  | _, _, .neg, x => -x

def name : {a b : Ty} → Prim a b → String
  | _, _, .literal n => "CONST " ++ toString n
  | _, _, .add => "ADD"
  | _, _, .mul => "MUL"
  | _, _, .neg => "NEG"

def x : Term Prim [.prod .base .base] .base := .fst (.var .here)
def y : Term Prim [.prod .base .base] .base := .snd (.var .here)

def magSqr : Term Prim [.prod .base .base] .base :=
  .prim .add (.pair (.prim .mul (.pair x x)) (.prim .mul (.pair y y)))

def shared : Term Prim [.prod .base .base] .base :=
  .letE (.prim .mul (.pair x y))
    (.prim .add (.pair (.prim .mul (.pair (.var .here) (.var .here)))
      (.fst (.var (.there .here)))))

theorem eval_magSqr {R : Type} [Ring R] (a b : R) :
    eval meaning magSqr ((), (a, b)) = a * a + b * b := rfl

theorem eval_shared {R : Type} [Ring R] (a b : R) :
    eval meaning shared ((), (a, b)) = (a * b) * (a * b) + a := rfl

end Arithmetic
