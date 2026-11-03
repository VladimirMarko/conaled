import SquareKit.ExponentiablePullback
import SquareKit.SheafTerminalProduct
import SquareKit.SheafFamily

/-! Experimental dependent products along ordinary sheaf product projections,
constructed by pullback stability of the terminal-map adjunction. -/
noncomputable section
namespace SquareKit.SheafProjectionProduct
open CategoryTheory Limits SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (A Γ : Sheaf J (Type (max u v)))

/-- The explicit product is the actual pullback of a terminal display. -/
theorem projectionSquare : IsPullback (snd A Γ) (fst A Γ)
    (SheafTerminalProduct.terminalMap Γ) (SheafTerminalProduct.terminalMap A) := by
  apply IsPullback.flip
  apply IsPullback.of_is_product' _ CartesianMonoidalCategory.isTerminalTensorUnit
  exact BinaryFan.IsLimit.mk _ (fun f g => lift f g) (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro T f g m hm hn
      ext U x
      exact Prod.ext (congrArg (fun k => k.hom.app U x) hm)
        (congrArg (fun k => k.hom.app U x) hn))

/-- This functor applies to every family over A × Γ. -/
def pi : Over (product A Γ) ⥤ Over Γ :=
  ExponentiablePullback.squareRightAdjoint
    (SheafTerminalProduct.terminalMap A) (SheafTerminalProduct.terminalMap Γ)
    (SheafTerminalProduct.adjunction A) (projectionSquare A Γ)

def adjunction : Over.pullback (snd A Γ) ⊣ pi A Γ :=
  ExponentiablePullback.squareAdjunction
    (SheafTerminalProduct.terminalMap A) (SheafTerminalProduct.terminalMap Γ)
    (SheafTerminalProduct.adjunction A) (projectionSquare A Γ)

/-- An explicit Mathlib witness, with ordinary limit-based pullbacks. -/
abbrev exponentiable := ExponentiablePullback.exponentiable
  (SheafTerminalProduct.terminalMap A) (SheafTerminalProduct.terminalMap Γ)
  (SheafTerminalProduct.adjunction A) (projectionSquare A Γ)

/-- Compare the ordinary chosen pullback with explicit argument/parameter pairs. -/
def parameterIso (X : Over Γ) : pullback X.hom (snd A Γ) ≅ product A X.left :=
  pullbackSymmetry _ _ ≪≫ SheafFamily.constantIso A X.hom

@[reassoc (attr := simp)] theorem parameterIso_argument (X : Over Γ) :
    (parameterIso A Γ X).hom ≫ fst A X.left = pullback.snd X.hom (snd A Γ) ≫ fst A Γ := by
  simp [parameterIso, Category.assoc, SheafFamily.constantIso_comparison]

@[reassoc (attr := simp)] theorem parameterIso_parameter (X : Over Γ) :
    (parameterIso A Γ X).hom ≫ snd A X.left = pullback.fst X.hom (snd A Γ) := by
  simp [parameterIso, SheafFamily.constantIso_display, Family.reindex]

/-- The other pullback leg is the existing family reindexing map. -/
theorem parameterIso_display (X : Over Γ) :
    (parameterIso A Γ X).inv ≫ Family.reindex X.hom (snd A Γ) =
      lift (fst A X.left) (snd A X.left ≫ X.hom) := by
  apply (cancel_epi (parameterIso A Γ X).hom).1
  rw [Iso.hom_inv_id_assoc]
  ext U x
  apply Prod.ext
  · exact (congrArg (fun k => k.hom.app U x) (parameterIso_argument A Γ X)).symm
  · have h := pullback.condition (f := X.hom) (g := snd A Γ)
    exact (congrArg (fun k => k.hom.app U x) h).symm.trans
      (congrArg (fun k => (k ≫ X.hom).hom.app U x) (parameterIso_parameter A Γ X)).symm

theorem parameterIso_natural {X Y : Over Γ} (f : X ⟶ Y) :
    ((Over.pullback (snd A Γ)).map f).left ≫ (parameterIso A Γ Y).hom =
      (parameterIso A Γ X).hom ≫ SheafFunction.parameterMap A f.left := by
  have hp : SheafFunction.parameterMap A f.left ≫ fst A Y.left = fst A X.left := rfl
  have hq : SheafFunction.parameterMap A f.left ≫ snd A Y.left = snd A X.left ≫ f.left := rfl
  have ha : (((Over.pullback (snd A Γ)).map f).left ≫ (parameterIso A Γ Y).hom) ≫ fst A Y.left =
      ((parameterIso A Γ X).hom ≫ SheafFunction.parameterMap A f.left) ≫ fst A Y.left := by
    simp [Category.assoc, hp, Over.pullback]
  have hx : (((Over.pullback (snd A Γ)).map f).left ≫ (parameterIso A Γ Y).hom) ≫ snd A Y.left =
      ((parameterIso A Γ X).hom ≫ SheafFunction.parameterMap A f.left) ≫ snd A Y.left := by
    simp [Category.assoc, hq, Over.pullback]
  ext U x
  exact Prod.ext (congrArg (fun k => k.hom.app U x) ha) (congrArg (fun k => k.hom.app U x) hx)

end SquareKit.SheafProjectionProduct
