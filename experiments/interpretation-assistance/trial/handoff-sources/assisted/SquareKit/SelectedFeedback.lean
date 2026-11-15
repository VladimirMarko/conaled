import SquareKit.FunctionCategory
import SquareKit.GuardedStreams

namespace SquareKit
universe u v w

/-- Admissibility retains the selected witness; no trace equations are assumed. -/
structure SelectedFeedback {Obj : Type u} (C : CategoryOps.{u,v} Obj)
    (prod : Obj → Obj → Obj) where
  WF : {a b s : Obj} → C.Hom (prod a s) (prod b s) → Type w
  trace : {a b s : Obj} → (f : C.Hom (prod a s) (prod b s)) → WF f → C.Hom a b

namespace FunctionFeedback
variable {A B S : Type u}

/-- The output and feedback state are data, with their fixed-point equation. -/
abbrev Witness (f : A × S → B × S) :=
  (x : A) → Σ y : B, { z : S // f (x, z) = (y, z) }

def trace (f : A × S → B × S) (w : Witness f) : A → B := fun x => (w x).1

def selected : SelectedFeedback FunctionCategory.ops Prod where
  WF := Witness
  trace := trace

/-- A sufficient condition for a selected output to respect input equivalence. -/
def OutputCongruent (RA : A → A → Prop) (RB : B → B → Prop)
    {f : A × S → B × S} (w : Witness f) : Prop :=
  ∀ x x', RA x x' → RB (w x).1 (w x').1

theorem trace_congruent {RA : A → A → Prop} {RB : B → B → Prop}
    {f : A × S → B × S} (w : Witness f) (h : OutputCongruent RA RB w) :
    ∀ x x', RA x x' → RB (trace f w x) (trace f w x') := h

/-- Uniqueness modulo the output relation suffices without uniqueness of state. -/
theorem outputCongruent_of_unique {RA : A → A → Prop} {RB : B → B → Prop}
    {f : A × S → B × S} (w : Witness f)
    (h : ∀ x x' y y' z z', RA x x' → f (x,z) = (y,z) →
      f (x',z') = (y',z') → RB y y') : OutputCongruent RA RB w := by
  intro x x' hx
  exact h x x' _ _ _ _ hx (w x).2.property (w x').2.property

open GuardedStreams

/-- Only the recursive stream component must be guarded. -/
def guardedWitness {T : Type u} (F : A → Stream T → Stream T)
    (out : A → Stream T → B) (hF : ∀ x, Guarded (F x)) (seed : T) :
    Witness (fun p : A × Stream T => (out p.1 p.2, F p.1 p.2)) :=
  fun x => ⟨out x (solve (F x) seed), solve (F x) seed,
    congrArg (fun s => (out x (solve (F x) seed), s)) (solve_fixed (hF x) seed).symm⟩

/-- Guardedness makes every admitted choice produce the constructed output. -/
theorem guarded_trace_unique {T : Type u} (F : A → Stream T → Stream T)
    (out : A → Stream T → B) (hF : ∀ x, Guarded (F x)) (seed : T)
    (w : Witness (fun p : A × Stream T => (out p.1 p.2, F p.1 p.2))) :
    trace _ w = trace _ (guardedWitness F out hF seed) := by
  funext x
  have he := (w x).2.property
  have hs : (w x).2.val = solve (F x) seed :=
    unique (hF x) seed _ (congrArg Prod.snd he).symm
  have ho := congrArg Prod.fst he
  change (w x).1 = out x (solve (F x) seed)
  exact ho.symm.trans (congrArg (out x) hs)

end FunctionFeedback
end SquareKit
