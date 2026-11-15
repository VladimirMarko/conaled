import SquareKit.Internal.Cubical.SquareFaceCocycle
import SquareKit.Internal.Cubical.CochainSieveExtension
import SquareKit.Internal.Cubical.CocycleEvaluation
import SquareKit.Internal.Cubical.Faces

/-! Boundary labels are read from formal De Morgan substitutions at the empty partial assignment. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

def squareFaceData (X : Over (⟨2⟩ : Cube)) : PartialDimension.Carrier × PartialDimension.Carrier :=
  (Face.assignmentMap X.hom (fun _ => none) 0, Face.assignmentMap X.hom (fun _ => none) 1)

theorem squareFaceData_refines {X Y : Over (⟨2⟩ : Cube)} (f : X ⟶ Y) :
    PartialDimension.Refines (squareFaceData Y).1 (squareFaceData X).1 ∧
      PartialDimension.Refines (squareFaceData Y).2 (squareFaceData X).2 := by
  have h := Face.assignmentMap_refines Y.hom (fun _ => none)
    (Face.assignmentMap f.left (fun _ => none)) (fun _ => Or.inl rfl)
  have e : Face.assignmentMap X.hom (fun _ => none) =
      Face.assignmentMap Y.hom (Face.assignmentMap f.left (fun _ => none)) := by
    rw [← Over.w f]
    exact Face.assignmentMap_comp _ _ _
  rw [← e] at h
  exact ⟨h 0,h 1⟩

def squareBoundarySieve : SieveObjects (Over (⟨2⟩ : Cube)) where
  contains X := (squareFaceData X).1 ≠ none ∨ (squareFaceData X).2 ≠ none
  downward f p := by
    have h := squareFaceData_refines f
    rcases p with p | p
    · left
      rcases h.1 with q | q
      · exact (p q).elim
      · exact q ▸ p
    · right
      rcases h.2 with q | q
      · exact (p q).elim
      · exact q ▸ p

def squareLabel (X : Over (⟨2⟩ : Cube)) (p : squareBoundarySieve.contains X) : SquareFaceLabel :=
  ⟨squareFaceData X,p⟩

def partialSquareCochain : PartialCochain1 squareBoundarySieve := fun {X Y} f p =>
  squareEdgeValue (squareLabel X (squareBoundarySieve.downward f p)) (squareLabel Y p)

theorem partialSquareCochain_closed {X Y Z : Over (⟨2⟩ : Cube)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : squareBoundarySieve.contains Z) :
    partialSquareCochain g p - partialSquareCochain (f ≫ g) p +
      partialSquareCochain f (squareBoundarySieve.downward g p) = 0 := by
  let LZ := squareLabel Z p
  let LY := squareLabel Y (squareBoundarySieve.downward g p)
  let LX := squareLabel X (squareBoundarySieve.downward (f ≫ g) p)
  exact squareBoundaryCochain_closed
    (homOfLE (show LX ≤ LY from squareFaceData_refines f))
    (homOfLE (show LY ≤ LZ from squareFaceData_refines g))

noncomputable def squareCocycle : CubeCocycle (⟨2⟩ : Cube) := coboundary (extendZero partialSquareCochain)

theorem squareCocycle_boundary {X Y Z : Over (⟨2⟩ : Cube)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : squareBoundarySieve.contains Z) :
    squareCocycle.cochain f g = 0 :=
  (δ1_extendZero_inside partialSquareCochain f g p).trans (partialSquareCochain_closed f g p)

end SquareKit.Cubical.CategoryCocycles
