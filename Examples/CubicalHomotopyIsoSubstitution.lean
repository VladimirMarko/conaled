import Examples.CubicalUnivalenceTransport
import SquareKit.Internal.Cubical.HomotopyIsoSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalHomotopyIsoSubstitution
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport

/-- Restricting the Boolean transposition preserves the chosen center and
whole contraction in every native homotopy fiber. -/
theorem booleanChosenEquivalence_reindex {Δ : Context.{0}} (σ : Δ ⟶ terminal.{0}) :
    (HomotopyEquivalence.ofIso (codeIso booleanTransposition)).reindex σ =
      HomotopyEquivalence.ofIso (Functor.isoWhiskerLeft σ.mapElements (codeIso booleanTransposition)) :=
  HomotopyEquivalence.ofIso_reindex (codeIso booleanTransposition) σ

end Examples.CubicalHomotopyIsoSubstitution
