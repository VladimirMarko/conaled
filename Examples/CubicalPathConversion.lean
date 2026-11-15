import SquareKit.Internal.Cubical.PathConversion
import Examples.CubicalContraction

/-! Literal Path conversion preserves the source contraction's nonconstant line. -/
namespace Examples.CubicalPathConversion
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalContraction

abbrev lineCubes : Context := cubes lineSpace 1
abbrev body : Family (total (Presheaf.interval lineCubes)) :=
  Functor.Elements.π (total (Presheaf.interval lineCubes)) ⋙ lineCubes
abbrev origin : Term (reindex body (endpointSub lineCubes false)) :=
  transformationTerm (cubeOrigin lineSpace 1 ≫ constantCube lineSpace 1)
abbrev identity : Term (reindex body (endpointSub lineCubes true)) :=
  transformationTerm (𝟙 lineCubes)

def chooseLine : terminal ⟶ lineCubes where
  app I := TypeCat.ofHom (fun _ => line I)
  naturality _ _ _ := rfl

def contraction : Term (normalizedPath body origin identity) :=
  Term.map (normalizedPathIso body origin identity).hom (interpretedContractionPath lineSpace 1)

theorem contraction_application :
    normalizedPathApp contraction = pathApp (interpretedContractionPath lineSpace 1) :=
  congrArg pathApp (Term.map_iso_roundtrip (normalizedPathIso body origin identity)
    (interpretedContractionPath lineSpace 1))

theorem selected_path_formation : reindex (normalizedPath body origin identity) chooseLine =
    normalizedPath (reindex body (liftSub (Presheaf.interval lineCubes) chooseLine))
      (origin.reindex chooseLine) (identity.reindex chooseLine) :=
  normalizedPath_reindex body origin identity chooseLine

theorem selected_path_application :
    normalizedPathApp ((contraction.reindex chooseLine).convert selected_path_formation) =
      (pathApp (interpretedContractionPath lineSpace 1)).reindex
        (liftSub (Presheaf.interval lineCubes) chooseLine) :=
  (normalizedPathApp_reindex contraction chooseLine).trans
    (congrArg (fun t : Term body => t.reindex (liftSub (Presheaf.interval lineCubes) chooseLine))
      contraction_application)

/-- The equality-converted source path still computes the two-dimensional meet. -/
theorem selected_connection :
    ((normalizedPathApp ((contraction.reindex chooseLine).convert selected_path_formation)).val
      ((total (Presheaf.interval terminal)).elementsMk (Opposite.op ⟨2⟩)
        ⟨PUnit.unit, ⟨Cube.ofRaw (fun _ => .var (1 : Fin 2))⟩⟩)).val (𝟙 _)
          (fun _ => Cube.ofRaw (fun _ => .var (0 : Fin 2))) = Cube.connection := by
  rw [selected_path_application, interpretedContractionPath_eq]
  rfl

theorem selected_endpoints_distinct :
    (origin.reindex chooseLine).val (terminal.elementsMk (Opposite.op ⟨1⟩) PUnit.unit) ≠
      (identity.reindex chooseLine).val (terminal.elementsMk (Opposite.op ⟨1⟩) PUnit.unit) :=
  Ne.symm line_not_constant_origin

end Examples.CubicalPathConversion
