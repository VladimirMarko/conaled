import FirstOrder
import SquareKit.Combinators

/-!
# Incremental computation as exact update squares

The derivative of a finite change is specified by the update equation, not
by the infinitesimal derivative equation. Changes can depend on the old input.
The abstract interface imposes no group/invertibility requirements. Concrete
instances supply and prove their update rules in `Arithmetic.lean`.
-/
namespace Incremental

structure ChangeObj where
  X : Type
  Delta : Type
  update : X → Delta → X

structure Map (A B : ChangeObj) where
  run : A.X → B.X
  change : A.X → A.Delta → B.Delta
  correct : ∀ x dx, B.update (run x) (change x dx) = run (A.update x dx)

@[ext] theorem Map.ext {A B : ChangeObj} {f g : Map A B}
    (hr : ∀ x, f.run x = g.run x) (hc : ∀ x dx, f.change x dx = g.change x dx) : f = g := by
  cases f with
  | mk fr fc fp =>
    cases g with
    | mk gr gc gp =>
      have h₁ : fr = gr := funext hr
      have h₂ : fc = gc := funext fun x => funext (hc x)
      cases h₁; cases h₂; rfl

def ident (A : ChangeObj) : Map A A := ⟨id, fun _ dx => dx, fun _ _ => rfl⟩

def comp {A B C : ChangeObj} (g : Map B C) (f : Map A B) : Map A C where
  run x := g.run (f.run x)
  change x dx := g.change (f.run x) (f.change x dx)
  correct x dx := by rw [g.correct, f.correct]

theorem comp_assoc {A B C D : ChangeObj} (h : Map C D) (g : Map B C) (f : Map A B) :
    comp h (comp g f) = comp (comp h g) f :=
  Map.ext (fun _ => rfl) (fun _ _ => rfl)

theorem ident_comp {A B : ChangeObj} (f : Map A B) : comp (ident B) f = f :=
  Map.ext (fun _ => rfl) (fun _ _ => rfl)

theorem comp_ident {A B : ChangeObj} (f : Map A B) : comp f (ident A) = f :=
  Map.ext (fun _ => rfl) (fun _ _ => rfl)

def product (A B : ChangeObj) : ChangeObj :=
  ⟨A.X × B.X, A.Delta × B.Delta, fun x dx => (A.update x.1 dx.1, B.update x.2 dx.2)⟩

def fst (A B : ChangeObj) : Map (product A B) A :=
  ⟨Prod.fst, fun _ => Prod.fst, fun _ _ => rfl⟩

def snd (A B : ChangeObj) : Map (product A B) B :=
  ⟨Prod.snd, fun _ => Prod.snd, fun _ _ => rfl⟩

def pair {X A B : ChangeObj} (f : Map X A) (g : Map X B) : Map X (product A B) where
  run x := (f.run x, g.run x)
  change x dx := (f.change x dx, g.change x dx)
  correct x dx := Prod.ext (f.correct x dx) (g.correct x dx)

theorem fst_pair {X A B : ChangeObj} (f : Map X A) (g : Map X B) :
    comp (fst A B) (pair f g) = f := Map.ext (fun _ => rfl) (fun _ _ => rfl)

theorem snd_pair {X A B : ChangeObj} (f : Map X A) (g : Map X B) :
    comp (snd A B) (pair f g) = g := Map.ext (fun _ => rfl) (fun _ _ => rfl)

theorem pair_eta {X A B : ChangeObj} (f : Map X (product A B)) :
    pair (comp (fst A B) f) (comp (snd A B) f) = f :=
  Map.ext (fun _ => rfl) (fun _ _ => rfl)

/-- Decode an old value/change pair as its updated value. -/
def updateRep (A : ChangeObj) : Squares.Rep := ⟨A.X × A.Delta, A.X, fun p => A.update p.1 p.2⟩

def square {A B : ChangeObj} (f : Map A B) : Squares.Square (updateRep A) (updateRep B) where
  impl p := (f.run p.1, f.change p.1 p.2)
  spec := f.run
  commutes p := f.correct p.1 p.2

theorem square_comp {A B C : ChangeObj} (g : Map B C) (f : Map A B) :
    square (comp g f) = Squares.compose (square g) (square f) :=
  Squares.Square.ext (fun _ => rfl) (fun _ => rfl)

/-- Cached results carry the actual invariant required by incremental reuse. -/
structure Cache {A B : ChangeObj} (f : Map A B) where
  input : A.X
  output : B.X
  valid : output = f.run input

def initializeCache {A B : ChangeObj} (f : Map A B) (x : A.X) : Cache f := ⟨x, f.run x, rfl⟩

def Cache.advance {A B : ChangeObj} {f : Map A B} (c : Cache f) (dx : A.Delta) : Cache f where
  input := A.update c.input dx
  output := B.update c.output (f.change c.input dx)
  valid := by rw [c.valid, f.correct]

theorem advance_correct {A B : ChangeObj} {f : Map A B} (c : Cache f) (dx : A.Delta) :
    (c.advance dx).output = f.run (A.update c.input dx) := (c.advance dx).valid

/-- A lawful but potentially inefficient baseline: changes replace the value. -/
def replacement (A : Type) : ChangeObj := ⟨A, A, fun _ y => y⟩

def recompute {A B : Type} (f : A → B) : Map (replacement A) (replacement B) :=
  ⟨f, fun _ new => f new, fun _ _ => rfl⟩

namespace Compiler
open FirstOrderCompiler

@[reducible] def Delta (base : ChangeObj) : Ty → Type
  | .base => base.Delta
  | .unit => Unit
  | .prod a b => Delta base a × Delta base b

def update (base : ChangeObj) : (a : Ty) → Val base.X a → Delta base a → Val base.X a
  | .base, x, dx => base.update x dx
  | .unit, _, _ => ()
  | .prod a b, x, dx => (update base a x.1 dx.1, update base b x.2 dx.2)

@[reducible] def object (base : ChangeObj) (a : Ty) : ChangeObj :=
  ⟨Val base.X a, Delta base a, update base a⟩

structure Primitives (base : ChangeObj) (Prim : Ty → Ty → Type)
    (meaning : {a b : Ty} → Prim a b → Val base.X a → Val base.X b) where
  change : {a b : Ty} → Prim a b → Val base.X a → Delta base a → Delta base b
  correct : ∀ {a b : Ty} (p : Prim a b) x dx,
    update base b (meaning p x) (change p x dx) = meaning p (update base a x dx)

def target (base : ChangeObj) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.X a → Val base.X b}
    (P : Primitives base Prim meaning) : Target Prim where
  Hom a b := Map (object base a) (object base b)
  ident := ⟨id, fun _ dx => dx, fun _ _ => rfl⟩
  comp := Incremental.comp
  terminal := ⟨fun _ => (), fun _ _ => (), fun _ _ => rfl⟩
  fst := ⟨Prod.fst, fun _ => Prod.fst, fun _ _ => rfl⟩
  snd := ⟨Prod.snd, fun _ => Prod.snd, fun _ _ => rfl⟩
  pair f g := ⟨fun x => (f.run x, g.run x), fun x dx => (f.change x dx, g.change x dx),
    fun x dx => Prod.ext (f.correct x dx) (g.correct x dx)⟩
  primitive p := ⟨meaning p, P.change p, P.correct p⟩

def sound (base : ChangeObj) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.X a → Val base.X b}
    (P : Primitives base Prim meaning) : Sound base.X (target base P) meaning where
  denote f := f.run
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  primitive _ _ := rfl

theorem compile_update (base : ChangeObj) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.X a → Val base.X b}
    (P : Primitives base Prim meaning) (t : Term Prim Γ a) (x) (dx) :
    update base a (eval meaning t x) ((compile (target base P) t).change x dx) =
      eval meaning t (update base (context Γ) x dx) := by
  have h := (compile (target base P) t).correct x dx
  change update base a ((compile (target base P) t).run x) _ =
    (compile (target base P) t).run _ at h
  simpa only [show ∀ y, (compile (target base P) t).run y = eval meaning t y from
    fun y => compile_sound _ (sound base P) t y] using h

end Compiler
end Incremental
