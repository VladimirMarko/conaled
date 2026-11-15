import SquareKit.Internal.Cubical.ContractibleTotals
import Examples.CubicalNativeContractions

/-! Contractible totals give an equivalence between forward and reversed based paths. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalContractibleTotals
open CategoryTheory SquareKit.Cubical.Presheaf
open CubicalEquivalenceFamilies CubicalNativeContractions
variable {Γ : Context.{0}}

abbrev carrier := constantFamily Γ Bool
abbrev forwardPaths := homogeneousPath (reindex (carrier (Γ := Γ)) (projection carrier))
  (truth.reindex (projection carrier)) (generic carrier)
abbrev backwardPaths := homogeneousPath (reindex (carrier (Γ := Γ)) (projection carrier))
  (generic carrier) (truth.reindex (projection carrier))

def reverseMap : forwardPaths (Γ := Γ) ⟶ backwardPaths :=
  (NativePathSingleton.reverseIso (truth.reindex (projection carrier)) (generic carrier)).hom

noncomputable def forwardFilling : Filling (forwardPaths (Γ := Γ)) :=
  pathFilling (boolFilling.reindex (projection (interval (total carrier)) ≫ projection carrier))
    (boolFilling_lawful.reindex _) (truth.reindex (projection carrier)) (generic carrier)

theorem forwardFilling_lawful : (forwardFilling (Γ := Γ)).Lawful :=
  pathFilling_lawful _ (boolFilling_lawful.reindex _) _ _

noncomputable def backwardFilling : Filling (backwardPaths (Γ := Γ)) :=
  pathFilling (boolFilling.reindex (projection (interval (total carrier)) ≫ projection carrier))
    (boolFilling_lawful.reindex _) (generic carrier) (truth.reindex (projection carrier))

theorem backwardFilling_lawful : (backwardFilling (Γ := Γ)).Lawful :=
  pathFilling_lawful _ (boolFilling_lawful.reindex _) _ _

def forwardTotal : HomotopyContractible (sigma (carrier (Γ := Γ)) forwardPaths) :=
  NativePathSingleton.contractible truth

def backwardTotal : HomotopyContractible (sigma (carrier (Γ := Γ)) backwardPaths) :=
  NativePathSingleton.fiberAt (HomotopyEquivalence.ofIso (Iso.refl carrier)) truth

/-- The equivalence is derived from total-space contractions, using the actual
path-reversal map and the native dependent path fillers. -/
noncomputable def reversalFromTotals : HomotopyEquivalence (reverseMap (Γ := Γ)) :=
  HomotopyEquivalence.ofContractibleTotals reverseMap boolFilling boolFilling_lawful
    forwardFilling forwardFilling_lawful backwardFilling backwardFilling_lawful
    forwardTotal backwardTotal

/-- The resulting witness includes contractions of all native homotopy fibers. -/
noncomputable def nativeFibers := (reversalFromTotals (Γ := Γ)).fibers

def falsity : Term (constantFamily terminal.{0} Bool) where
  val _ := false
  property _ := rfl

def falseSub : terminal.{0} ⟶ total (carrier (Γ := terminal)) := pair (𝟙 terminal) falsity

/-- Contractibility of the total does not make every base fiber inhabited. -/
theorem noForwardAtFalse (p : Term (reindex (forwardPaths (Γ := terminal)) falseSub)) : False := by
  let q := Term.map (pathReindexIso
    (reindex (carrier (Γ := terminal))
      (projection (interval (total carrier)) ≫ projection carrier))
    (truth.reindex (projection carrier)) (generic carrier) falseSub).hom p
  have h := discretePath_endpoints q
  have hb := congrArg (fun t => t.val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)) h
  exact Bool.false_ne_true hb.symm


end Examples.CubicalContractibleTotals
