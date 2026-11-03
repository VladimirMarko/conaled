import FirstOrder
import Mathlib.Algebra.Order.Field.Rat

/-! # Typed, inspectable cartesian circuit syntax -/

namespace Applications.Circuits

open FirstOrderCompiler

/-- Gate labels are inspectable data, including each pin's rational delay. -/
inductive Gate : Ty → Ty → Type where
  | constant (v : Bool) : Gate .unit .base
  | not (delay : ℚ) : Gate .base .base
  | nand (leftDelay rightDelay : ℚ) : Gate (.prod .base .base) .base
  | nor (leftDelay rightDelay : ℚ) : Gate (.prod .base .base) .base
  | xor (leftDelay rightDelay : ℚ) : Gate (.prod .base .base) .base

def Gate.meaning : Gate a b → Val Bool a → Val Bool b
  | .constant v, _ => v
  | .not _, x => !x
  | .nand _ _, x => !(x.1 && x.2)
  | .nor _ _, x => !(x.1 || x.2)
  | .xor _ _, x => Bool.xor x.1 x.2

inductive Circuit : Ty → Ty → Type where
  | identity : Circuit a a
  | compose : Circuit b c → Circuit a b → Circuit a c
  | terminate : Circuit a .unit
  | first : Circuit (.prod a b) a
  | second : Circuit (.prod a b) b
  | pair : Circuit a b → Circuit a c → Circuit a (.prod b c)
  | gate : Gate a b → Circuit a b

namespace Circuit

def target : Target Gate where
  Hom := Circuit
  ident := .identity
  comp := .compose
  terminal := .terminate
  fst := .first
  snd := .second
  pair := .pair
  primitive := .gate

/-- Interpret the same circuit vocabulary in any cartesian gate algebra. -/
def interpret (K : Target Gate) : Circuit a b → K.Hom a b
  | .identity => K.ident
  | .compose g f => K.comp (interpret K g) (interpret K f)
  | .terminate => K.terminal
  | .first => K.fst
  | .second => K.snd
  | .pair f g => K.pair (interpret K f) (interpret K g)
  | .gate p => K.primitive p

theorem interpret_compileVar (K : Target Gate) (v : Var Γ a) :
    interpret K (compileVar target v) = compileVar K v := by
  induction v with
  | here => rfl
  | there v ih =>
    change K.comp (interpret K (compileVar target v)) K.fst =
      K.comp (compileVar K v) K.fst
    rw [ih]

/-- The frontend and the circuit fold compose for every target algebra. -/
theorem interpret_compile (K : Target Gate) (t : Term Gate Γ a) :
    interpret K (compile target t) = compile K t := by
  induction t with
  | var v => exact interpret_compileVar K v
  | unit => rfl
  | pair t u it iu =>
    change K.pair (interpret K (compile target t)) (interpret K (compile target u)) =
      K.pair (compile K t) (compile K u)
    rw [it, iu]
  | fst t it =>
    change K.comp K.fst (interpret K (compile target t)) = K.comp K.fst (compile K t)
    rw [it]
  | snd t it =>
    change K.comp K.snd (interpret K (compile target t)) = K.comp K.snd (compile K t)
    rw [it]
  | letE t u it iu =>
    change K.comp (interpret K (compile target u))
      (K.pair K.ident (interpret K (compile target t))) =
      K.comp (compile K u) (K.pair K.ident (compile K t))
    rw [it, iu]
  | prim p t it =>
    change K.comp (K.primitive p) (interpret K (compile target t)) =
      K.comp (K.primitive p) (compile K t)
    rw [it]

def productMap (f : Circuit a c) (g : Circuit b d) : Circuit (.prod a b) (.prod c d) :=
  .pair (.compose f .first) (.compose g .second)

def not : Circuit .base .base := .gate (.not (1 / 10))
def nand : Circuit (.prod .base .base) .base := .gate (.nand (1 / 5) (1 / 5))
def nor : Circuit (.prod .base .base) .base := .gate (.nor (1 / 5) (1 / 5))
def xor : Circuit (.prod .base .base) .base := .gate (.xor (1 / 4) (1 / 4))
def and : Circuit (.prod .base .base) .base := .compose not nand
def or : Circuit (.prod .base .base) .base := .compose not nor

end Circuit
end Applications.Circuits
