import SquareKit.SmoothLocalizationDual
import SquareKit.SmoothStage

/-! Experimental localization arrows for finite-presentation smooth stages.
The displayed algebra pushout is a geometric pullback in the opposite site. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PresentedLocalization
open CategoryTheory
variable {n m a b : ℕ}

def presentationStage (r : Fin m → Free n) : SmoothStage.Stage := .presented n m r

def stage (r : Fin m → Free n) (s : Presentation.Carrier r) : SmoothStage.Stage :=
  .presented (n+1) (m+1) (Presentation.relations r (equation (representative r s)))

def stageBase (r : Fin m → Free n) (s : Presentation.Carrier r) : presentationStage r ⟶ stage r s := atBase r s

def stageHomEquiv (r : Fin m → Free n) (s : Presentation.Carrier r) (B : SmoothStage.Stage) :
    (stage r s ⟶ B) ≃ {h : presentationStage r ⟶ B // IsUnit ((SmoothStage.smoothMap h).toFun s)} := atHomEquiv r s

def stageMap (r : Fin m → Free n) (s : Presentation.Carrier r) (t : Fin b → Free a)
    (h : presentationStage r ⟶ presentationStage t) : stage r s ⟶ stage t ((SmoothStage.smoothMap h).toFun s) := atMap r s t h

theorem stage_square (r : Fin m → Free n) (s : Presentation.Carrier r) (t : Fin b → Free a)
    (h : presentationStage r ⟶ presentationStage t) :
    stageBase r s ≫ stageMap r s t h = h ≫ stageBase t ((SmoothStage.smoothMap h).toFun s) :=
  map_base r (representative r s) t (representative t ((SmoothStage.smoothMap h).toFun s)) h
    (by rw [representative_eq]; exact (representative_eq t ((SmoothStage.smoothMap h).toFun s)).symm)

/-- Arbitrary smooth target algebras, not just coded stages, test this pushout. -/
theorem stage_pushout {C : Type*} [CommRing C] [Algebra ℝ C] [Structure C]
    (r : Fin m → Free n) (s : Presentation.Carrier r) (t : Fin b → Free a)
    (h : presentationStage r ⟶ presentationStage t)
    (u : Hom (At r s) C) (v : Hom (Presentation.Carrier t) C)
    (hc : Hom.comp u (atBase r s) = Hom.comp v h) :
    ∃! k : Hom (At t ((SmoothStage.smoothMap h).toFun s)) C,
      Hom.comp k (atMap r s t h) = u ∧ Hom.comp k (atBase t ((SmoothStage.smoothMap h).toFun s)) = v :=
  pushout_universal r (representative r s) t (representative t ((SmoothStage.smoothMap h).toFun s)) h
    (by rw [representative_eq]; exact (representative_eq t ((SmoothStage.smoothMap h).toFun s)).symm) u v hc

def stageDualBase (r : Fin m → Free n) (s : Presentation.Carrier r) :
    SmoothStage.Stage.dual (presentationStage r) ⟶ .dual (stage r s) := dualBase r (representative r s)

def dualLocalizedStage (r : Fin m → Free n) (s : Presentation.Carrier r) : SmoothStage.Stage :=
  .presented ((n+1)+1) ((m+1)+1)
    (Presentation.relations (Presentation.relations r (Presentation.dualEquation n))
      (equation (Localization.extend (k := 1) (representative r s))))

def stageDualComparison (r : Fin m → Free n) (s : Presentation.Carrier r) :
    dualLocalizedStage r s ⟶ SmoothStage.Stage.dual (stage r s) := toLocalizedDual r (representative r s)
def stageDualComparisonInverse (r : Fin m → Free n) (s : Presentation.Carrier r) :
    SmoothStage.Stage.dual (stage r s) ⟶ dualLocalizedStage r s := fromLocalizedDual r (representative r s)

theorem stageDualComparison_inv (r : Fin m → Free n) (s : Presentation.Carrier r) :
    stageDualComparison r s ≫ stageDualComparisonInverse r s = 𝟙 _ := localized_dual_inverse r (representative r s)
theorem stageDualComparison_inv_rev (r : Fin m → Free n) (s : Presentation.Carrier r) :
    stageDualComparisonInverse r s ≫ stageDualComparison r s = 𝟙 _ := dual_localized_inverse r (representative r s)

end SquareKit.SmoothAlgebra.PresentedLocalization
