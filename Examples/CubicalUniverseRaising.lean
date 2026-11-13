import Examples.CubicalUniversalDecode
import SquareKit.Internal.Cubical.UniverseRaisingNaturality

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalUnivalenceTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue

/-- Lowering retains a genuine native fiber contraction for the actual
universal-decoding transport of the Boolean universe loop. -/
noncomputable def loweredBooleanTransportEquivalence :
    HomotopyEquivalence (SmallUniverse.lowerChartMap
      (constantLocal terminal Bool).code (constantLocal terminal Bool).code (𝟙 _)
      (SmallUniverse.NativeUnivalence.pathToMap booleanUniverseLoop)) :=
  SmallUniverse.lowerChartEquivalence _ _ (𝟙 _) _ booleanUniversalTransportEquivalence

/-- Restricting the actual Boolean transport keeps its complete chosen fiber data. -/
theorem loweredBoolean_substitution {Δ : Context.{0}} (σ : Δ ⟶ terminal.{0}) :
    SmallUniverse.lowerChartEquivalence
      (constantLocal terminal Bool).code (constantLocal terminal Bool).code (raisedSub σ ≫ 𝟙 _)
      (SmallUniverse.NativeUnivalence.pathToMap booleanUniverseLoop)
      booleanUniversalTransportEquivalence = loweredBooleanTransportEquivalence.reindex σ := by
  exact SmallUniverse.lowerChartEquivalence_reindex
      (constantLocal terminal Bool).code (constantLocal terminal Bool).code (𝟙 _)
      (SmallUniverse.NativeUnivalence.pathToMap booleanUniverseLoop)
      booleanUniversalTransportEquivalence σ

end Examples.CubicalUnivalenceTransport
