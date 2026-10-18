import SquareKit.Internal.Squares

/-! Internal and ordinary proof styles in one file; no new notation or instances. -/
namespace Examples.InternalGraphs
open SquareKit.Internal

-- Expected heterogeneous path: (3,true) ↦ 3 ↦ (3 : Int).
example : ∃ n : Nat, n = (3, true).1 ∧ (3 : Int) = Int.ofNat n :=
  (Graph.inSet (Prod.fst : Nat × Bool → Nat) Int.ofNat (3, true) 3).mpr rfl

-- Increment then double gives 8, whereas reversing the order gives 7.
example : ∃ n : Nat, n = 3 + 1 ∧ 8 = n * 2 :=
  (Graph.inSet (fun n : Nat => n + 1) (fun n => n * 2) 3 8).mpr rfl

example : ¬ ∃ n : Nat, n = 3 + 1 ∧ 7 = n * 2 := by
  intro h
  have impossible := (Graph.inSet (fun n : Nat => n + 1) (fun n => n * 2) 3 7).mp h
  contradiction

-- Set soundness can be specialized to an empty carrier without an instance.
example (f : Empty → Nat) (a : Empty) (c : Int) :
    (∃ n, n = f a ∧ c = Int.ofNat n) ↔ c = Int.ofNat (f a) :=
  Graph.inSet f Int.ofNat a c

/-- Replace the free variable with an arbitrary term, including a free variable
of the same sort as the binder. Its value must remain outside that binder. -/
example {S : Type} {F : S → S → Type} {s : S} {Δ : List S}
    (M : Interpretation F) (ρ : Env M Δ) (t : Term F Δ s) :
    let σ : Sub F [s] Δ := fun {_} i => match i with | .zero => t | .succ i => nomatch i
    ((Formula.ex (.eq (.var (.succ .zero)) (.var .zero))).subst σ).eval M ρ ↔
      ∃ x : M.Carrier s, t.eval M ρ = x := by
  dsimp only
  rw [formula_subst]
  rfl

-- Same-sort free variable zero survives an added binder (a concrete capture test).
example (n : Nat) :
    let M := Graph.model (id : Nat → Nat) (id : Nat → Nat)
    let ρ : Env M [Graph.GraphSort.input] :=
      Env.extend n (fun {_} (i : Var [] _) => nomatch i)
    (Term.var (F := Graph.Arrow) (Var.zero : Var [Graph.GraphSort.input] _)).shift.eval M
      (ρ.extend (s := Graph.GraphSort.input) (n + 1)) = n :=
  term_shift _ _ _ _

open Squares Relational

abbrev pairRep : Rep := ⟨Nat × Bool, Nat, Prod.fst⟩
def firstSquare : Square pairRep pairRep where
  impl p := (0 + p.1, p.2)
  spec n := 0 + n
  commutes _ := rfl

def secondSquare : Square (Rep.mk Nat Int Int.ofNat) (Rep.mk Nat Int Int.ofNat) :=
  Squares.identity _

theorem middle_agrees (n : Nat) : firstSquare.spec n = secondSquare.impl n :=
  Nat.zero_add n

-- Both endpoint decoders have genuinely different input, middle and output types.
example :
    Graph.transportRelations (A := Graph.composedGraph pairRep Int.ofNat)
      (B := Graph.composedGraph pairRep Int.ofNat)
      (@Graph.existentialVertical pairRep pairRep Int Int Int.ofNat Int.ofNat firstSquare secondSquare middle_agrees)
      (graph (pairRep.after Int.ofNat)).Rel (graph (pairRep.after Int.ofNat)).Rel
      (Graph.composedGraph_iff pairRep Int.ofNat) (Graph.composedGraph_iff pairRep Int.ofNat) =
      ofSquare (vertical (AS := Int) (BS := Int) Int.ofNat Int.ofNat firstSquare secondSquare middle_agrees) :=
  Graph.vertical_comparison _ _ _ _ _

-- Ordinary calls still take just their original arguments in this mixed-style file.
example : (vertical (AS := Int) (BS := Int) Int.ofNat Int.ofNat firstSquare secondSquare middle_agrees).impl (3, true) =
    (3, true) := rfl
example : (vertical (AS := Int) (BS := Int) Int.ofNat Int.ofNat firstSquare secondSquare middle_agrees).spec (-2 : Int) = (-2 : Int) := rfl

example {A B C : Rep} (g : Square B C) (f : Square A B) :
    ofSquare (Squares.compose g f) = Relational.compose (ofSquare g) (ofSquare f) :=
  Graph.horizontal_comparison g f

example {A B C : RelRep} (g : RelSquare B C) (f : RelSquare A B)
    {r : A.R} {s : A.S} (h : A.Rel r s) : C.Rel (g.impl (f.impl r)) (g.spec (f.spec s)) :=
  SquareKit.RelationalCategory.compose_preserves g f h
end Examples.InternalGraphs
