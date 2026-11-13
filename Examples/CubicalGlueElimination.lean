import Examples.CubicalUnivalenceTransport
import SquareKit.Internal.Cubical.GlueEliminationSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalGlueElimination
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport

private abbrev a := (constantLocal terminal Bool).code
private def f := (codeIso booleanTransposition).hom
private def E := HomotopyEquivalence.ofIso (codeIso booleanTransposition)

/-- Rebuild the eliminator from the restricted complete Glue code. -/
noncomputable def restrictedElimination {Δ : Context.{0}} (σ : Δ ⟶ total (interval terminal.{0})) :=
  eqToHom (congrArg decode (Glue.code_substitution Univalence.face (Univalence.ambient a)
    (CodeSystem.boundary a a) (Univalence.boundaryMap a a f)
    (Univalence.boundaryEquivalence a a f E) σ)) ≫
  Glue.codeUnglue (Univalence.face.reindex σ) (raisedSub σ ≫ Univalence.ambient a)
    (raisedSub (restrictSubstitution Univalence.face σ) ≫ CodeSystem.boundary a a)
    (Functor.whiskerLeft (restrictSubstitution Univalence.face σ).mapElements
      (Univalence.boundaryMap a a f))
    ((Univalence.boundaryEquivalence a a f E).reindex (restrictSubstitution Univalence.face σ))

theorem restrictedElimination_eq {Δ : Context.{0}} (σ : Δ ⟶ total (interval terminal.{0})) :
    restrictedElimination σ = Functor.whiskerLeft σ.mapElements (Univalence.unglueLine a a f E) :=
  (Glue.codeUnglue_substitution Univalence.face (Univalence.ambient a)
    (CodeSystem.boundary a a) (Univalence.boundaryMap a a f)
    (Univalence.boundaryEquivalence a a f E) σ).symm

/-- Restricting and rebuilding the whole Boolean ua eliminator still returns
its supplied transposition at the zero endpoint. -/
theorem restrictedElimination_zero :
    restrictedElimination (endpointSub terminal false) =
      eqToHom (congrArg decode (Univalence.uaCode_zero a a f E)) ≫ f :=
  (restrictedElimination_eq (endpointSub terminal false)).trans
    (Univalence.unglueLine_zero a a f E)

end Examples.CubicalGlueElimination
