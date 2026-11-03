import Applications.Linear.Matrix
import FirstOrder
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option

/-!
# Compiling the linear fragment directly to finite matrices

Objects have an explicit finite coordinate type. The compiler emits matrices,
not functions hidden in matrix wrappers. The source vocabulary contains zero,
addition, and constant scaling, so every source program is linear. Nonzero
constants and multiplication of two variables are excluded by the vocabulary.
-/
namespace MatrixCompiler
open FirstOrderCompiler

@[reducible] def Slots : Ty → Type
  | .base => Unit
  | .unit => Empty
  | .prod a b => Sum (Slots a) (Slots b)

instance slotsFintype : (a : Ty) → Fintype (Slots a)
  | .base => inferInstanceAs (Fintype Unit)
  | .unit => inferInstanceAs (Fintype Empty)
  | .prod a b => @instFintypeSum (Slots a) (Slots b) (slotsFintype a) (slotsFintype b)

instance slotsDecidableEq : (a : Ty) → DecidableEq (Slots a)
  | .base => inferInstanceAs (DecidableEq Unit)
  | .unit => inferInstanceAs (DecidableEq Empty)
  | .prod a b => @instDecidableEqSum (Slots a) (Slots b) (slotsDecidableEq a) (slotsDecidableEq b)

def encode {R : Type} : (a : Ty) → Val R a → Slots a → R
  | .base, x, _ => x
  | .unit, _, e => nomatch e
  | .prod a _, x, .inl i => encode a x.1 i
  | .prod _ b, x, .inr j => encode b x.2 j

def decode {R : Type} : (a : Ty) → (Slots a → R) → Val R a
  | .base, x => x ()
  | .unit, _ => ()
  | .prod a b, x => (decode a (fun i => x (.inl i)), decode b (fun j => x (.inr j)))

theorem decode_encode {R : Type} (a : Ty) (x : Val R a) : decode a (encode a x) = x := by
  induction a with
  | base => rfl
  | unit => cases x; rfl
  | prod a b ia ib => exact Prod.ext (ia x.1) (ib x.2)

theorem encode_decode {R : Type} (a : Ty) (x : Slots a → R) : encode a (decode a x) = x := by
  funext i
  induction a with
  | base => cases i; rfl
  | unit => exact nomatch i
  | prod a b ia ib => cases i with
    | inl i => exact ia (fun j => x (.inl j)) i
    | inr i => exact ib (fun j => x (.inr j)) i

variable (R : Type) [CommSemiring R]

abbrev Code (a b : Ty) := Matrix (Slots b) (Slots a) R

def denote {a b : Ty} (M : Code R a b) (x : Val R a) : Val R b :=
  decode b (M.mulVec (encode a x))

def first (a b : Ty) : Code R (.prod a b) a :=
  fun i => Sum.elim (fun j => if i = j then 1 else 0) (fun _ => 0)

def second (a b : Ty) : Code R (.prod a b) b :=
  fun i => Sum.elim (fun _ => 0) (fun j => if i = j then 1 else 0)

def pair {a b c : Ty} (M : Code R a b) (N : Code R a c) : Code R a (.prod b c) :=
  Sum.elim M N

theorem first_mulVec (a b : Ty) (x : Slots (.prod a b) → R) :
    (first R a b).mulVec x = fun i => x (.inl i) := by
  funext i
  simp [first, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem second_mulVec (a b : Ty) (x : Slots (.prod a b) → R) :
    (second R a b).mulVec x = fun i => x (.inr i) := by
  funext i
  simp [second, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

inductive Prim (R : Type) : Ty → Ty → Type where
  | zero : Prim R .unit .base
  | add : Prim R (.prod .base .base) .base
  | scale : R → Prim R .base .base

def meaning : {a b : Ty} → Prim R a b → Val R a → Val R b
  | _, _, .zero, _ => 0
  | _, _, .add, p => p.1 + p.2
  | _, _, .scale r, x => r * x

def primitive : {a b : Ty} → Prim R a b → Code R a b
  | _, _, .zero => fun _ e => nomatch e
  | _, _, .add => fun _ _ => 1
  | _, _, .scale r => fun _ _ => r

theorem denote_primitive {a b : Ty} (p : Prim R a b) (x : Val R a) :
    denote R (primitive R p) x = meaning R p x := by
  cases p <;> simp [denote, primitive, meaning, decode, encode, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type]

def target : Target (Prim R) where
  Hom := Code R
  ident := 1
  comp M N := M * N
  terminal := fun e => nomatch e
  fst := first R _ _
  snd := second R _ _
  pair := pair R
  primitive := primitive R

end MatrixCompiler
