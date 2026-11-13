import SquareKit.Internal.Cubical.NativePathSingleton
import SquareKit.Internal.Cubical.HomotopyRetracts
import SquareKit.Internal.Cubical.HomotopyEquivalenceSubstitution
import Examples.CubicalEquivalenceFamilies

/-! Native contractions apply to based path families and chosen equivalence witnesses. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalNativeContractions
open CategoryTheory SquareKit.Cubical.Presheaf
open EquivalenceFamilies CubicalEquivalenceFamilies
variable {Γ : Context.{0}}

def truth : Term (constantFamily Γ Bool) where
  val _ := true
  property _ := rfl

def truePathSingleton : HomotopyContractible (NativePathSingleton.singleton (truth (Γ := Γ))) :=
  NativePathSingleton.contractible truth

theorem singleton_center :
    sigmaFst (truePathSingleton (Γ := Γ)).center = truth := rfl

/-- The native contraction reaches every based path, not just its carrier endpoint. -/
def basedPathContraction (z : Term (NativePathSingleton.singleton (truth (Γ := Γ)))) :=
  truePathSingleton.pathTo z

/-- Concatenation combines comparisons of actual chosen equivalence witnesses. -/
noncomputable def witnessRoundtrip
    (e d : HomotopyEquivalence (boolIso (Γ := Γ)).hom) :
    Term (homogeneousPath (isEquiv boolIso.hom) (encodeIsEquiv e) (encodeIsEquiv e)) :=
  homogeneousConcat
    (isEquivFilling boolIso.hom boolFilling boolFilling_lawful boolFilling boolFilling_lawful)
    (isEquivFilling_lawful boolIso.hom boolFilling boolFilling_lawful boolFilling boolFilling_lawful)
    (flipWitnessPath e d) (flipWitnessPath d e)

/-- Repeated context substitution retains the supplied Boolean fiber contractions. -/
theorem flip_substitution_comp {Δ Θ : Context.{0}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (e : HomotopyEquivalence (boolIso (Γ := Γ)).hom) :
    (e.reindex σ).reindex τ = e.reindex (τ ≫ σ) :=
  e.reindex_comp σ τ

end Examples.CubicalNativeContractions
