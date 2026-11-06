import SquareKit.Internal.Cubical.SourceContraction
import SquareKit.Internal.Cubical.Substitution
import SquareKit.Internal.Cubical.DimensionModels

/-! The source connection calculation and arbitrary-dimensional contraction
through the constructed Path and function operations. -/
namespace Examples.CubicalContraction
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

abbrev lineSpace : Context := yoneda.obj (Cube.mk 1)

def line (I : Cubeᵒᵖ) : CubeElement lineSpace 1 I where
  val _ r := r 0
  naturality _ _ _ := rfl

/-- The n=1 source body computes to the genuine two-dimensional connection. -/
theorem one_dimension_connection :
    ((contractCube lineSpace 1).app (Opposite.op ⟨2⟩)
      ⟨line (Opposite.op ⟨2⟩), ⟨Cube.ofRaw (fun _ => .var 1)⟩⟩).val (𝟙 _)
      (fun _ => Cube.ofRaw (fun _ => .var 0)) = Cube.connection := rfl

/-- The same calculation is reached through the interpreted Nat recursion. -/
theorem one_dimension_source_connection :
    ((interpretedContraction lineSpace 1).app (Opposite.op ⟨2⟩)
      ⟨line (Opposite.op ⟨2⟩), ⟨Cube.ofRaw (fun _ => .var 1)⟩⟩).val (𝟙 _)
      (fun _ => Cube.ofRaw (fun _ => .var 0)) = Cube.connection := by
  rw [interpretedContraction_eq]
  exact one_dimension_connection

/-- The contraction cannot be replaced by equality with the origin constant. -/
theorem line_not_constant_origin :
    line (Opposite.op ⟨1⟩) ≠
      (constantCube lineSpace 1).app (Opposite.op ⟨1⟩)
        ((cubeOrigin lineSpace 1).app (Opposite.op ⟨1⟩) (line (Opposite.op ⟨1⟩))) := by
  intro h
  have he := congrArg (fun p : CubeElement lineSpace 1 (Opposite.op ⟨1⟩) =>
    p.val (𝟙 _) (fun _ => Cube.identity ⟨1⟩)) h
  have hc : Cube.identity ⟨1⟩ = Cube.endpoint ⟨1⟩ false := he
  have bad := Four.sound (fun _ => (true,true)) ((Quotient.exact hc) 0)
  cases bad

/-- The recursive source equation retains every inner coordinate. -/
theorem successor_source_equation (X : Context) (n : ℕ) {I : Cubeᵒᵖ}
    (c : CubeElement X (n+1) I) (j i : Cube.Hom I.unop ⟨1⟩) :
    ((contractCube X (n+1)).app I ⟨c, ⟨j⟩⟩).apply i =
      (contractCube X n).app I ⟨c.apply (Cube.meet i j), ⟨j⟩⟩ :=
  contractCube_apply X n c j i

/-- The first endpoint is obtained from the public dependent Path operation. -/
theorem contraction_path_zero (X : Context) (n : ℕ) :
    Term.reindex (pathApp (interpretedContractionPath X n)) (endpointSub (cubes X n) false) =
      transformationTerm (cubeOrigin X n ≫ constantCube X n) :=
  pathApp_zero (interpretedContractionPath X n)

theorem contraction_path_one (X : Context) (n : ℕ) :
    Term.reindex (pathApp (interpretedContractionPath X n)) (endpointSub (cubes X n) true) =
      transformationTerm (𝟙 (cubes X n)) :=
  pathApp_one (interpretedContractionPath X n)

/-- Two arbitrary context substitutions retain the full contraction section. -/
theorem contraction_two_substitutions (X Γ Δ : Context) (n : ℕ)
    (σ : Γ ⟶ cubes X n) (τ : Δ ⟶ Γ) :
    Term.reindex (Term.reindex (interpretedContractionPath X n) σ) τ =
      Term.reindex (interpretedContractionPath X n) (τ ≫ σ) :=
  Term.reindex_comp (interpretedContractionPath X n) σ τ

/-- Path substitution and its inverse retain the interpreted recursive witness. -/
theorem source_path_substitution_roundtrip (X Γ : Context) (n : ℕ) (σ : Γ ⟶ cubes X n) :
    let e := pathReindexIso (Functor.Elements.π (total (interval (cubes X n))) ⋙ cubes X n)
      (transformationTerm (cubeOrigin X n ≫ constantCube X n))
      (transformationTerm (𝟙 (cubes X n))) σ
    Term.map e.inv (Term.map e.hom (Term.reindex (interpretedContractionPath X n) σ)) =
      Term.reindex (interpretedContractionPath X n) σ :=
  Term.map_iso_roundtrip _ _

end Examples.CubicalContraction
