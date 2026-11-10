import SquareKit.Internal.PathTransport.CechMatching
import SquareKit.SmoothQuotientGeneratedComposition
import SquareKit.SplitSheafCech

/-! Independent matching data for the direct interpretation of every generated
context. The same context derivation is used at all three overlap levels. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ)

abbrev context (_h : Typed.CtxDeriv.{2} Γ γ) (X : Sheaf topology Type) : Grpd.{1,1} :=
  γ (SmoothQuotientSource.model a X)

def restriction {X Y : Sheaf topology Type} (f : Y ⟶ X) :
    context a hΓ X ⥤ context a hΓ Y :=
  generatedContextMap (SmoothQuotientComparison.signature (a := a) f) hΓ

theorem restriction_id (X : Sheaf topology Type) :
    restriction a hΓ (𝟙 X) = 𝟭 (context a hΓ X) :=
  SmoothQuotientComparison.generatedContextMap_id a hΓ

theorem restriction_comp {X Y Z : Sheaf topology Type} (f : Y ⟶ X) (g : Z ⟶ Y) :
    restriction a hΓ f ⋙ restriction a hΓ g = restriction a hΓ (g ≫ f) :=
  SmoothQuotientComparison.generatedContextMap_comp a f g hΓ

/-- The endpoint identifications are the proved generated parameter laws. -/
def strictDiagram (A : SplitSheaf.Ty X) : CechMatching.StrictDiagram.{1} where
  localCategory := context a hΓ (SplitSheaf.Ext A)
  doubleCategory := context a hΓ (SplitSheaf.Cech.double A)
  tripleCategory := context a hΓ (SplitSheaf.Cech.triple A)
  first := restriction a hΓ (SplitSheaf.Cech.first A)
  second := restriction a hΓ (SplitSheaf.Cech.second A)
  diagonal := restriction a hΓ (SplitSheaf.Cech.diagonal A)
  firstSecond := restriction a hΓ (SplitSheaf.Cech.firstSecond A)
  firstThird := restriction a hΓ (SplitSheaf.Cech.firstThird A)
  secondThird := restriction a hΓ (SplitSheaf.Cech.secondThird A)
  diagonalFirst := by
    rw [restriction_comp]
    exact restriction_id a hΓ _
  diagonalSecond := by
    rw [restriction_comp]
    exact restriction_id a hΓ _
  tripleFirst := by
    rw [restriction_comp,
      restriction_comp]
    rfl
  tripleMiddle := by
    rw [restriction_comp,
      restriction_comp]
    rfl
  tripleLast := by
    rw [restriction_comp,
      restriction_comp]
    rfl

/-- The matching diagram retains the selected equality-induced comparisons. -/
def diagram (A : SplitSheaf.Ty X) : CechMatching.Diagram.{1} :=
  (strictDiagram a hΓ A).toDiagram

/-- Actual local generated objects with overlap arrows and Čech equations.
Neither a global extension nor a cocycle-model interpretation is an input. -/
abbrev Datum (A : SplitSheaf.Ty X) := CechMatching.Datum (diagram a hΓ A)

/-- Restricting along the two overlap projections gives the same functor. -/
theorem restrictionOverlap_eq (A : SplitSheaf.Ty X) :
    restriction a hΓ (SplitSheaf.p A) ⋙ restriction a hΓ (SplitSheaf.Cech.first A) =
      restriction a hΓ (SplitSheaf.p A) ⋙ restriction a hΓ (SplitSheaf.Cech.second A) := by
  rw [restriction_comp, restriction_comp]
  rfl

/-- Restriction creates matching data with the canonical overlap, rather than
choosing a new local representative. -/
def restrictDatum (A : SplitSheaf.Ty X) (x : context a hΓ X) : Datum a hΓ A :=
  (strictDiagram a hΓ A).equalDatum ((restriction a hΓ (SplitSheaf.p A)).obj x)
    (Functor.congr_obj (restrictionOverlap_eq a hΓ A) x)

/-- The full global-to-local functor uses the actual restriction on arrows. -/
def restrictionFunctor (A : SplitSheaf.Ty X) : context a hΓ X ⥤ Datum a hΓ A :=
  (strictDiagram a hΓ A).equalFunctor (restriction a hΓ (SplitSheaf.p A))
    (restrictionOverlap_eq a hΓ A)

end SquareKit.SmoothQuotientGeneratedMatching
