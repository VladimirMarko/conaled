import SquareKit.SmoothLocalizationBaseChange
import SquareKit.SmoothLocalizationOpen

/-! Experimental compatibility with the previous free-stage and ordinary-open localization.
The empty relation presentation introduces no different smooth algebra. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PresentedLocalization
variable {n : ℕ}

def noRelations (n : ℕ) : Fin 0 → Free n := Fin.elim0

def freeValue (n : ℕ) : Hom (Presentation.Carrier (noRelations n)) (Free n) :=
  Quotient.lift (Presentation.ideal (noRelations n)) Hom.ident (by
    intro p hp
    have hi : Presentation.ideal (noRelations n) = ⊥ := by
      unfold Presentation.ideal noRelations
      simp
    rw [hi] at hp
    exact hp)

theorem freeValue_projection (n : ℕ) : Hom.comp (freeValue n) (Presentation.projection (noRelations n)) = Hom.ident :=
  Quotient.lift_projection _ _ _

theorem free_projectionValue (n : ℕ) : Hom.comp (Presentation.projection (noRelations n)) (freeValue n) = Hom.ident := by
  apply Quotient.unique (Presentation.ideal (noRelations n))
  change Hom.comp (Hom.comp (Presentation.projection (noRelations n)) (freeValue n)) (Presentation.projection (noRelations n)) = _
  rw [← Hom.comp_assoc,freeValue_projection]
  rfl

def freeToOld (p : Free n) : Hom (Carrier (noRelations n) p) (Localization.Principal p) :=
  lift _ p (Hom.comp (Localization.principalBase p) (freeValue n)) (Localization.base_isUnit _ 0)

def oldToFree (p : Free n) : Hom (Localization.Principal p) (Carrier (noRelations n) p) :=
  Localization.principalLift p (Hom.comp (base (noRelations n) p) (Presentation.projection (noRelations n))) (base_isUnit _ _)

theorem freeToOld_base (p : Free n) :
    Hom.comp (freeToOld p) (base (noRelations n) p) = Hom.comp (Localization.principalBase p) (freeValue n) := by
  unfold freeToOld
  apply lift_base

theorem oldToFree_base (p : Free n) :
    Hom.comp (oldToFree p) (Localization.principalBase p) =
      Hom.comp (base (noRelations n) p) (Presentation.projection (noRelations n)) := by
  unfold oldToFree
  apply Localization.lift_base

theorem free_old_inverse (p : Free n) : Hom.comp (oldToFree p) (freeToOld p) = Hom.ident := by
  apply unique (noRelations n) p
  rw [← Hom.comp_assoc,freeToOld_base,Hom.comp_assoc,
    oldToFree_base,← Hom.comp_assoc,free_projectionValue]
  rfl

theorem old_free_inverse (p : Free n) : Hom.comp (freeToOld p) (oldToFree p) = Hom.ident := by
  apply Localization.principal_unique p
  rw [← Hom.comp_assoc,oldToFree_base,Hom.comp_assoc,freeToOld_base,
    ← Hom.comp_assoc,freeValue_projection]
  rfl

def freeToOpen (p : Free n) : Hom (Carrier (noRelations n) p) (Localization.Functions p) :=
  Hom.comp (Localization.toOpen p) (freeToOld p)
def openToFree (p : Free n) : Hom (Localization.Functions p) (Carrier (noRelations n) p) :=
  Hom.comp (oldToFree p) (Localization.fromOpen p)

theorem free_open_inverse (p : Free n) : Hom.comp (openToFree p) (freeToOpen p) = Hom.ident := by
  unfold openToFree freeToOpen
  calc
    _ = Hom.comp (oldToFree p) (Hom.comp (Hom.comp (Localization.fromOpen p) (Localization.toOpen p)) (freeToOld p)) := (Hom.comp_assoc _ _ _).symm.trans (congrArg (Hom.comp _) (Hom.comp_assoc _ _ _))
    _ = Hom.comp (oldToFree p) (freeToOld p) := by rw [Localization.fromOpen_toOpen]; rfl
    _ = Hom.ident := free_old_inverse p

theorem open_free_inverse (p : Free n) : Hom.comp (freeToOpen p) (openToFree p) = Hom.ident := by
  unfold openToFree freeToOpen
  calc
    _ = Hom.comp (Localization.toOpen p) (Hom.comp (Hom.comp (freeToOld p) (oldToFree p)) (Localization.fromOpen p)) := (Hom.comp_assoc _ _ _).symm.trans (congrArg (Hom.comp _) (Hom.comp_assoc _ _ _))
    _ = Hom.comp (Localization.toOpen p) (Localization.fromOpen p) := by rw [old_free_inverse]; rfl
    _ = Hom.ident := Localization.toOpen_fromOpen p

end SquareKit.SmoothAlgebra.PresentedLocalization
