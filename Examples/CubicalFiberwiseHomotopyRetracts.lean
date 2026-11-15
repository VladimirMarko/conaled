import SquareKit.Internal.Cubical.FiberwiseHomotopyRetracts
import Examples.CubicalContractibleTotals

/-! Dependent path reversal transfers the contraction of a based path total. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalFiberwiseHomotopyRetracts
open CategoryTheory SquareKit.Cubical.Presheaf
open CubicalContractibleTotals CubicalEquivalenceFamilies CubicalNativeContractions
universe u

/-- An actual fiber isomorphism supplies a native roundtrip homotopy. -/
def isoRoundtrip {Γ : Context.{u}} {X : Family Γ} {A B : Family (total X)}
    (e : A ≅ B) : Term (homogeneousPath (reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements e.hom)
        (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B)))
      (generic B)) := by
  have he : Term.map (Functor.whiskerLeft (projection B).mapElements e.hom)
      (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B)) = generic B := by
    apply Term.ext
    intro x
    exact congrArg (fun m => m.app ((projection B).mapElements.obj x) x.val.2) e.inv_hom_id
  exact pathLam ((generic B).reindex (projection (interval (total B)))) he.symm rfl

variable {Γ : Context.{0}}

def reversal : forwardPaths (Γ := Γ) ≅ backwardPaths :=
  NativePathSingleton.reverseIso (truth.reindex (projection carrier)) (generic carrier)

/-- The target is a varying dependent path family. Only the forward total's
contraction is supplied; the target total homotopy is constructed by the API. -/
noncomputable def reversedTotal : HomotopyContractible
    (sigma (carrier (Γ := Γ)) backwardPaths) :=
  forwardTotal.fiberwiseRetract boolFilling boolFilling_lawful
    backwardFilling backwardFilling_lawful reversal.hom reversal.inv (isoRoundtrip reversal)

/-- The construction retains the forward total's base point. -/
theorem reversedTotal_center_base : sigmaFst (reversedTotal (Γ := Γ)).center = truth := rfl

/-- The API contracts every target point, including its native path component. -/
noncomputable def contractReversedPoint
    (b : Term (sigma (carrier (Γ := Γ)) backwardPaths)) :
    Term (homogeneousPath (sigma carrier backwardPaths) reversedTotal.center b) :=
  reversedTotal.pathTo b

/-- Total-space contractibility still does not assert inhabitation at every
base point: reversal would otherwise yield the impossible forward path at false. -/
theorem noBackwardAtFalse (p : Term (reindex (backwardPaths (Γ := terminal)) falseSub)) : False :=
  noForwardAtFalse (Term.map (Functor.whiskerLeft falseSub.mapElements reversal.inv) p)

end Examples.CubicalFiberwiseHomotopyRetracts
