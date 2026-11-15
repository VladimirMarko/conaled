import Squares

/-!
# Relational interpretations and their commuting-square presentation

An interval represents many points, and a stable signal needs evidence about
an interval of time. Such interpretations are relations, not arbitrary chosen
decoding functions. This module keeps that distinction explicit. The `witness`
construction presents a relational morphism as a square on its total witness
spaces; it is a mathematical presentation, not a proof of witness erasure.
-/

universe u

namespace Relational

structure RelRep where
  R : Type u
  S : Type u
  Rel : R → S → Prop

structure RelSquare (A B : RelRep.{u}) where
  impl : A.R → B.R
  spec : A.S → B.S
  preserves : ∀ {r s}, A.Rel r s → B.Rel (impl r) (spec s)

@[ext] theorem RelSquare.ext {A B : RelRep.{u}} {f g : RelSquare A B}
    (hi : ∀ x, f.impl x = g.impl x) (hs : ∀ x, f.spec x = g.spec x) : f = g := by
  cases f with
  | mk fi fs fp =>
    cases g with
    | mk gi gs gp =>
      have hi' : fi = gi := funext hi
      have hs' : fs = gs := funext hs
      cases hi'; cases hs'; rfl

def identity (A : RelRep.{u}) : RelSquare A A where
  impl := id
  spec := id
  preserves := id

def compose {A B C : RelRep.{u}} (g : RelSquare B C) (f : RelSquare A B) :
    RelSquare A C where
  impl := g.impl ∘ f.impl
  spec := g.spec ∘ f.spec
  preserves h := g.preserves (f.preserves h)

theorem compose_assoc {A B C D : RelRep.{u}}
    (h : RelSquare C D) (g : RelSquare B C) (f : RelSquare A B) :
    compose h (compose g f) = compose (compose h g) f :=
  RelSquare.ext (fun _ => rfl) (fun _ => rfl)

theorem identity_compose {A B : RelRep.{u}} (f : RelSquare A B) :
    compose (identity B) f = f := RelSquare.ext (fun _ => rfl) (fun _ => rfl)

theorem compose_identity {A B : RelRep.{u}} (f : RelSquare A B) :
    compose f (identity A) = f := RelSquare.ext (fun _ => rfl) (fun _ => rfl)

def terminal : RelRep.{u} := ⟨PUnit, PUnit, fun _ _ => True⟩

def terminate (A : RelRep.{u}) : RelSquare A terminal where
  impl _ := PUnit.unit
  spec _ := PUnit.unit
  preserves _ := True.intro

def product (A B : RelRep.{u}) : RelRep.{u} where
  R := A.R × B.R
  S := A.S × B.S
  Rel r s := A.Rel r.1 s.1 ∧ B.Rel r.2 s.2

def first (A B : RelRep.{u}) : RelSquare (product A B) A where
  impl := Prod.fst
  spec := Prod.fst
  preserves := And.left

def second (A B : RelRep.{u}) : RelSquare (product A B) B where
  impl := Prod.snd
  spec := Prod.snd
  preserves := And.right

def pair {X A B : RelRep.{u}} (f : RelSquare X A) (g : RelSquare X B) :
    RelSquare X (product A B) where
  impl x := (f.impl x, g.impl x)
  spec x := (f.spec x, g.spec x)
  preserves h := ⟨f.preserves h, g.preserves h⟩

theorem first_pair {X A B : RelRep.{u}} (f : RelSquare X A) (g : RelSquare X B) :
    compose (first A B) (pair f g) = f := RelSquare.ext (fun _ => rfl) (fun _ => rfl)

theorem second_pair {X A B : RelRep.{u}} (f : RelSquare X A) (g : RelSquare X B) :
    compose (second A B) (pair f g) = g := RelSquare.ext (fun _ => rfl) (fun _ => rfl)

theorem pair_eta {X A B : RelRep.{u}} (f : RelSquare X (product A B)) :
    pair (compose (first A B) f) (compose (second A B) f) = f :=
  RelSquare.ext (fun _ => rfl) (fun _ => rfl)

def exponential (A B : RelRep.{u}) : RelRep.{u} where
  R := A.R → B.R
  S := A.S → B.S
  Rel f g := ∀ {r s}, A.Rel r s → B.Rel (f r) (g s)

def evaluation (A B : RelRep.{u}) :
    RelSquare (product (exponential A B) A) B where
  impl p := p.1 p.2
  spec p := p.1 p.2
  preserves h := h.1 h.2

def curry {X A B : RelRep.{u}} (f : RelSquare (product X A) B) :
    RelSquare X (exponential A B) where
  impl x a := f.impl (x, a)
  spec x a := f.spec (x, a)
  preserves hx _ _ ha := f.preserves ⟨hx, ha⟩

def uncurry {X A B : RelRep.{u}} (f : RelSquare X (exponential A B)) :
    RelSquare (product X A) B where
  impl p := f.impl p.1 p.2
  spec p := f.spec p.1 p.2
  preserves h := f.preserves h.1 h.2

theorem uncurry_curry {X A B : RelRep.{u}} (f : RelSquare (product X A) B) :
    uncurry (curry f) = f := RelSquare.ext (fun _ => rfl) (fun _ => rfl)

theorem curry_uncurry {X A B : RelRep.{u}} (f : RelSquare X (exponential A B)) :
    curry (uncurry f) = f := RelSquare.ext (fun _ => rfl) (fun _ => rfl)

def graph (A : Squares.Rep.{u}) : RelRep.{u} where
  R := A.R
  S := A.S
  Rel r s := A.decode r = s

def ofSquare {A B : Squares.Rep.{u}} (f : Squares.Square A B) :
    RelSquare (graph A) (graph B) where
  impl := f.impl
  spec := f.spec
  preserves h := (f.commutes _).trans (congrArg f.spec h)

def toSquare {A B : Squares.Rep.{u}} (f : RelSquare (graph A) (graph B)) :
    Squares.Square A B where
  impl := f.impl
  spec := f.spec
  commutes _ := f.preserves rfl

theorem toSquare_ofSquare {A B : Squares.Rep.{u}} (f : Squares.Square A B) :
    toSquare (ofSquare f) = f := Squares.Square.ext (fun _ => rfl) (fun _ => rfl)

/-- Total relation witnesses, projected to their semantic component. -/
def witness (A : RelRep.{u}) : Squares.Rep.{u} where
  R := {p : A.R × A.S // A.Rel p.1 p.2}
  S := A.S
  decode p := p.val.2

/-- Every relation-preserving implementation has an honest square on witnesses. -/
def witnessSquare {A B : RelRep.{u}} (f : RelSquare A B) :
    Squares.Square (witness A) (witness B) where
  impl p := ⟨(f.impl p.val.1, f.spec p.val.2), f.preserves p.property⟩
  spec := f.spec
  commutes _ := rfl

theorem witness_compose {A B C : RelRep.{u}} (g : RelSquare B C) (f : RelSquare A B) :
    witnessSquare (compose g f) = Squares.compose (witnessSquare g) (witnessSquare f) :=
  Squares.Square.ext (fun _ => rfl) (fun _ => rfl)

end Relational
