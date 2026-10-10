import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Squares

/-!
# Statically shaped containers

Products build containers; `subst` composes their shapes by replacing every
leaf of the outer shape by the inner shape.  `Nested` keeps that composition
visible in the carrier, so algorithms can exploit both levels.  Flattening
forgets the grouping.  No inverse of flattening is required by the square.
-/

universe u v w

namespace Applications.Parallel

inductive Shape where
  | empty
  | leaf
  | prod (left right : Shape)
  deriving Repr, DecidableEq

namespace Shape

@[reducible] def Data : Shape → Type u → Type u
  | .empty, _ => PUnit
  | .leaf, A => A
  | .prod s t, A => Data s A × Data t A

def size : Shape → Nat
  | .empty => 0
  | .leaf => 1
  | .prod s t => size s + size t

def subst : Shape → Shape → Shape
  | .empty, _ => .empty
  | .leaf, t => t
  | .prod s₁ s₂, t => .prod (subst s₁ t) (subst s₂ t)

theorem size_subst (s t : Shape) : (s.subst t).size = s.size * t.size := by
  induction s with
  | empty => simp [subst, size]
  | leaf => simp [subst, size]
  | prod s₁ s₂ ih₁ ih₂ => simp [subst, size, ih₁, ih₂, Nat.add_mul]

def map (s : Shape) (f : A → B) : s.Data A → s.Data B :=
  match s with
  | .empty => fun _ => PUnit.unit
  | .leaf => f
  | .prod s t => fun x => (s.map f x.1, t.map f x.2)

def zipWith (s : Shape) (f : A → B → C) : s.Data A → s.Data B → s.Data C :=
  match s with
  | .empty => fun _ _ => PUnit.unit
  | .leaf => f
  | .prod s t => fun x y => (s.zipWith f x.1 y.1, t.zipWith f x.2 y.2)

def pure (s : Shape) (a : A) : s.Data A :=
  match s with
  | .empty => PUnit.unit
  | .leaf => a
  | .prod s t => (s.pure a, t.pure a)

def flatten (s : Shape) : s.Data A → List A :=
  match s with
  | .empty => fun _ => []
  | .leaf => fun a => [a]
  | .prod s t => fun x => s.flatten x.1 ++ t.flatten x.2

@[simp] theorem flatten_length (s : Shape) (x : s.Data A) :
    (s.flatten x).length = s.size := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ihs iht => simp [flatten, size, ihs, iht]

@[simp] theorem flatten_map (s : Shape) (f : A → B) (x : s.Data A) :
    s.flatten (s.map f x) = (s.flatten x).map f := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ihs iht => simp [flatten, map, ihs, iht]

@[simp] theorem map_map (s : Shape) (g : B → C) (f : A → B) (x : s.Data A) :
    s.map g (s.map f x) = s.map (fun a => g (f a)) x := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ihs iht => simp [map, ihs, iht]

@[simp] theorem map_id (s : Shape) (x : s.Data A) : s.map id x = x := by
  induction s with
  | empty => cases x; rfl
  | leaf => rfl
  | prod s t ihs iht => simp [map, ihs, iht]

theorem map_congr (s : Shape) {f g : A → B} (h : ∀ a, f a = g a)
    (x : s.Data A) : s.map f x = s.map g x := by
  have : f = g := funext h
  rw [this]

private theorem zipWith_append_equal (f : A → B → C)
    (xs xs' : List A) (ys ys' : List B) (h : xs.length = ys.length) :
    List.zipWith f (xs ++ xs') (ys ++ ys') =
      List.zipWith f xs ys ++ List.zipWith f xs' ys' := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys => simp_all

@[simp] theorem flatten_zipWith (s : Shape) (f : A → B → C)
    (x : s.Data A) (y : s.Data B) :
    s.flatten (s.zipWith f x y) = List.zipWith f (s.flatten x) (s.flatten y) := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ihs iht =>
    simp only [flatten, zipWith, ihs, iht]
    symm
    apply zipWith_append_equal
    simp

@[simp] theorem flatten_pure (s : Shape) (a : A) :
    s.flatten (s.pure a) = List.replicate s.size a := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ihs iht => simp only [flatten, pure, size, ihs, iht, List.replicate_add]

/-- The data interpretation exposes only the ordered leaf sequence. -/
def rep (s : Shape) (A : Type u) : Squares.Rep where
  R := s.Data A
  S := List A
  decode := s.flatten

/-- Keeping a composition explicit is operationally meaningful. -/
def nestedRep (outer inner : Shape) (A : Type u) : Squares.Rep where
  R := outer.Data (inner.Data A)
  S := List A
  decode := fun x => (outer.flatten x).flatMap inner.flatten

/-- Reassociate an explicit nested container into its substituted product shape. -/
def join (s t : Shape) : s.Data (t.Data A) → (s.subst t).Data A :=
  match s with
  | .empty => fun _ => PUnit.unit
  | .leaf => id
  | .prod s₁ s₂ => fun x => (s₁.join t x.1, s₂.join t x.2)

def split (s t : Shape) : (s.subst t).Data A → s.Data (t.Data A) :=
  match s with
  | .empty => fun _ => PUnit.unit
  | .leaf => id
  | .prod s₁ s₂ => fun x => (s₁.split t x.1, s₂.split t x.2)

@[simp] theorem join_split (s t : Shape) (x : (s.subst t).Data A) :
    s.join t (s.split t x) = x := by
  induction s with
  | empty => cases x; rfl
  | leaf => rfl
  | prod s₁ s₂ ih₁ ih₂ => simp [join, split, ih₁, ih₂]

@[simp] theorem split_join (s t : Shape) (x : s.Data (t.Data A)) :
    s.split t (s.join t x) = x := by
  induction s with
  | empty => cases x; rfl
  | leaf => rfl
  | prod s₁ s₂ ih₁ ih₂ => simp [join, split, ih₁, ih₂]

@[simp] theorem flatten_join (s t : Shape) (x : s.Data (t.Data A)) :
    (s.subst t).flatten (s.join t x) = (s.flatten x).flatMap t.flatten := by
  induction s with
  | empty => rfl
  | leaf => simp [join, subst, flatten]
  | prod s₁ s₂ ih₁ ih₂ => simp [join, subst, flatten, ih₁, ih₂]

theorem flatten_split (s t : Shape) (x : (s.subst t).Data A) :
    (s.flatten (s.split t x)).flatMap t.flatten = (s.subst t).flatten x := by
  rw [← flatten_join, join_split]

def joinSquare (s t : Shape) (A : Type u) :
    Squares.Square (nestedRep s t A) ((s.subst t).rep A) where
  impl := s.join t
  spec := id
  commutes := s.flatten_join t

def splitSquare (s t : Shape) (A : Type u) :
    Squares.Square ((s.subst t).rep A) (nestedRep s t A) where
  impl := s.split t
  spec := id
  commutes := s.flatten_split t

def mapSquare (s : Shape) (f : A → B) :
    Squares.Square (s.rep A) (s.rep B) where
  impl := s.map f
  spec := List.map f
  commutes := s.flatten_map f

def pairShape : Shape := .prod .leaf .leaf

def rightPow (s : Shape) : Nat → Shape
  | 0 => .leaf
  | n + 1 => s.subst (rightPow s n)

def leftPow (s : Shape) : Nat → Shape
  | 0 => .leaf
  | n + 1 => (leftPow s n).subst s

def bush : Nat → Shape
  | 0 => pairShape
  | n + 1 => (bush n).subst (bush n)

theorem size_rightPow (s : Shape) (n : Nat) : (s.rightPow n).size = s.size ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightPow, size_subst, ih, Nat.pow_succ, Nat.mul_comm]

theorem size_leftPow (s : Shape) (n : Nat) : (s.leftPow n).size = s.size ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftPow, size_subst, ih, Nat.pow_succ]

end Shape
end Applications.Parallel
