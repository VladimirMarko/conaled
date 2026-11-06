import SquareKit.Internal.Cubical.FaceFormulas
import SquareKit.Internal.Cubical.PartialSections
import SquareKit.Internal.Cubical.DimensionModels
import SquareKit.Internal.Cubical.Naturals

/-! Face restrictions retain an unspecified interior, exact endpoints and
compatible dependent section values. -/
namespace Examples.CubicalFaces
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

abbrev line : Context := total (interval terminal)
abbrev coordinate : Term (interval line) := generic (interval terminal)
def left : Cofibration line := Cofibration.endpoint coordinate false
def right : Cofibration line := Cofibration.endpoint coordinate true

theorem generic_not_boundary :
    ¬ (left.join right).full (line.elementsMk (Opposite.op ⟨1⟩) ⟨PUnit.unit,⟨Cube.identity ⟨1⟩⟩⟩) := by
  change ¬ Face.Full (Face.join (Face.endpoint (Cube.identity ⟨1⟩) false)
    (Face.endpoint (Cube.identity ⟨1⟩) true))
  intro h
  exact Face.boundary_not_top ((Face.full_iff_top _).mp h)

theorem zero_on_left : left.full
    (line.elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨Cube.endpoint ⟨0⟩ false⟩⟩) :=
  (Cofibration.full_endpoint coordinate false _).mpr rfl

theorem one_on_right : right.full
    (line.elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨Cube.endpoint ⟨0⟩ true⟩⟩) :=
  (Cofibration.full_endpoint coordinate true _).mpr rfl

def leftSection : PartialSection (interval line) left := PartialSection.ofTerm left (endpoint line false)
def rightSection : PartialSection (interval line) right := PartialSection.ofTerm right (endpoint line true)

theorem endpoints_compatible : leftSection.Compatible rightSection := by
  intro x p q
  have hp := (Cofibration.full_endpoint coordinate false x).mp p
  have hq := (Cofibration.full_endpoint coordinate true x).mp q
  exact hp.symm.trans hq

noncomputable def boundarySection : PartialSection (interval line) (left.join right) :=
  leftSection.glue rightSection endpoints_compatible

theorem boundary_is_coordinate (x : line.Elements) (p : (left.join right).full x) :
    boundarySection.val x p = coordinate.val x := by
  rcases (Cofibration.full_join left right x).mp p with h | h
  · exact (glueValue_left leftSection rightSection x p h).trans
      ((Cofibration.full_endpoint coordinate false x).mp h).symm
  · exact (glueValue_right leftSection rightSection endpoints_compatible x p h).trans
      ((Cofibration.full_endpoint coordinate true x).mp h).symm

theorem endpoint_section_rejection :
    ¬ (PartialSection.ofTerm (Cofibration.top line) (endpoint line false)).Compatible
      (PartialSection.ofTerm (Cofibration.top line) (endpoint line true)) := by
  intro h
  have he := h (line.elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨Cube.endpoint ⟨0⟩ false⟩⟩) rfl rfl
  have hd := congrArg ULift.down he
  have bad := PartialDimension.sound (fun _ => none) (Quotient.exact hd 0)
  cases bad

theorem finite_formula_representation : (Face.normalForm (Face.join (Face.atom (0 : Fin 2) false)
    (Face.atom 1 true))).eval = Face.join (Face.atom 0 false) (Face.atom 1 true) := Face.normalForm_eval _

end Examples.CubicalFaces
