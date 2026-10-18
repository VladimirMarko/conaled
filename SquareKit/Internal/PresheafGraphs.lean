import SquareKit.Internal.Presheaf
import SquareKit.Internal.Squares

/-! Experimental graph validity and evaluation into ordinary square pasting.
The derivations remain `Graph.forward` and `Graph.backward`; this module only
constructs their model and the external comparison.
-/
namespace SquareKit.Internal.Presheaf
open CategoryTheory Opposite Squares Relational
universe u v
variable {J : Type v} [SmallCategory J]
variable {A B C A' B' C' : Jᵒᵖ ⥤ Type u}

def graphModel (f : A ⟶ B) (g : B ⟶ C) : Model (J := J) Graph.Arrow where
  carrier | .input => A | .middle => B | .output => C
  arrow | .first => f | .second => g

/-- The existing two derivations yield equality of context subfunctors. -/
theorem graph_valid (f : A ⟶ B) (g : B ⟶ C) :
    (graphModel f g).formula (Graph.composite .first .second) =
      (graphModel f g).formula (Graph.result .first .second) :=
  le_antisymm ((graphModel f g).sound (Graph.forward _ _))
    ((graphModel f g).sound (Graph.backward _ _))

def graphEnv (f : A ⟶ B) (g : B ⟶ C) (j : Jᵒᵖ) (a : A.obj j) (c : C.obj j) :
    Env ((graphModel f g).fiber j) [.input, .output] :=
  Env.extend a (Env.extend c (fun {_} (i : Var [] _) => nomatch i))

/-- Evaluation consumes model validity and the general formula comparison. -/
theorem graph_evaluation (f : A ⟶ B) (g : B ⟶ C) (j : Jᵒᵖ)
    (a : A.obj j) (c : C.obj j) :
    (∃ b, b = f.app j a ∧ c = g.app j b) ↔ c = g.app j (f.app j a) := by
  have h := congrArg (fun Q => Q.obj j (graphEnv f g j a c)) (graph_valid f g)
  exact ((graphModel f g).evaluation (Graph.composite .first .second) j _).symm.trans
    ((iff_of_eq h).trans ((graphModel f g).evaluation (Graph.result .first .second) j _))

/-- Equality orientation for the ordinary relational consumer. -/
theorem evaluated_relation (f : A ⟶ B) (g : B ⟶ C) (j : Jᵒᵖ)
    (a : A.obj j) (c : C.obj j) :
    (Graph.composedGraph (Rep.mk _ _ (f.app j)) (g.app j)).Rel a c ↔
      (graph ((Rep.mk _ _ (f.app j)).after (g.app j))).Rel a c := by
  have h := graph_evaluation f g j a c
  constructor
  · rintro ⟨b, hab, hbc⟩
    exact (h.mp ⟨b, hab.symm, hbc.symm⟩).symm
  · intro hac
    obtain ⟨b, hab, hbc⟩ := h.mpr hac.symm
    exact ⟨b, hab.symm, hbc.symm⟩

/-- A square of natural transformations, with both horizontal maps retained. -/
structure NaturalSquare (f : A ⟶ B) (f' : A' ⟶ B') where
  impl : A ⟶ A'
  spec : B ⟶ B'
  commutes : impl ≫ f' = f ≫ spec

namespace NaturalSquare
variable {f : A ⟶ B} {f' : A' ⟶ B'}

abbrev evaluate (q : NaturalSquare f f') (j : Jᵒᵖ) :
    Square (Rep.mk _ _ (f.app j)) (Rep.mk _ _ (f'.app j)) where
  impl := q.impl.app j
  spec := q.spec.app j
  commutes x := congrArg (fun (t : A ⟶ B') => t.app j x) q.commutes

end NaturalSquare

/-- Both endpoint comparisons come from the presheaf interpretation; proof
irrelevance then permits the unchanged Set `Graph.vertical_comparison` consumer.
Middle agreement is pointwise at each object, with no definitional-equality demand. -/
theorem vertical_evaluation {f : A ⟶ B} {g : B ⟶ C}
    {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    (q : NaturalSquare f f') (r : NaturalSquare g g')
    (middle : ∀ j x, q.spec.app j x = r.impl.app j x) (j : Jᵒᵖ) :
    transportRelations
      (Graph.existentialVertical (A := Rep.mk (A.obj j) (B.obj j) (f.app j))
        (B := Rep.mk (A'.obj j) (B'.obj j) (f'.app j)) (AS := C.obj j) (BS := C'.obj j) (fun x => g.app j x) (fun x => g'.app j x) (q.evaluate j) (r.evaluate j) (middle j))
      (graph ((Rep.mk _ _ (f.app j)).after (g.app j))).Rel
      (graph ((Rep.mk _ _ (f'.app j)).after (g'.app j))).Rel
      (evaluated_relation f g j) (evaluated_relation f' g' j) =
      ofSquare (vertical (A := Rep.mk (A.obj j) (B.obj j) (f.app j))
        (B := Rep.mk (A'.obj j) (B'.obj j) (f'.app j)) (AS := C.obj j) (BS := C'.obj j) (fun x => g.app j x) (fun x => g'.app j x) (q.evaluate j) (r.evaluate j) (middle j)) :=
  Graph.vertical_comparison _ _ _ _ _

end SquareKit.Internal.Presheaf
