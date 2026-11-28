import SquareKit.SheafGroupoidBibundleFunctor
import SquareKit.SheafGroupoidBibundlePrincipality
import SquareKit.SheafGroupoidTrivialActionMap
import Examples.GroupoidCompletion
import Mathlib.CategoryTheory.IsomorphismClasses
/-! Orbit equivalence does not imply tensor invertibility: the actual BC4 to 1 map. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.PrincipalBibundleNoninvertible
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SmoothOpenSite SquareKit.SmoothPresentationSite SquareKit.SmoothGeometricKL
open Orbifolds.QuarterTurn
open SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans

abbrev group := locallyConstantGroup C4
abbrev trivialGroup := locallyConstantGroup PUnit
abbrev point := Examples.SmoothTorsors.point
abbrev source := SheafGroupoidAction.operations (SheafGroupoidAction.trivialAction group point)
abbrev target := SheafGroupoidAction.operations (SheafGroupoidAction.trivialAction trivialGroup point)
def collapseGroup : group ⟶ trivialGroup := locallyConstantGroupMap (1 : C4 →* PUnit)
def collapse : source.pseudofunctor ⟶ target.pseudofunctor :=
  SheafGroupoidAction.trivialMapTransformation (M := point) collapseGroup
abbrev base : source.Object point := ⟨𝟙 point⟩
def loop (g : C4) : base ⟶ base where
  map := SheafRelation.lift (constantSection point g) (𝟙 point)
  source := rfl
  target := rfl

theorem loop_injective : Function.Injective loop := by
  intro g h he
  have hv := congrArg (fun f : base ⟶ base =>
    (f.map.hom.app (atStage (free 0)) (𝟙 (op (free 0)))).1) he
  exact constantLabel_injective C4 (free 0) (𝟙 _) hv

theorem quarterTurn_loop_ne : loop quarterTurn ≠ loop 1 :=
  fun h => Examples.SmoothTorsors.quarterTurn_ne_one (loop_injective h)

theorem collapse_loop (g h : C4) :
    (StackDescentTransformation.component collapse point).map (loop g) =
      (StackDescentTransformation.component collapse point).map (loop h) := by
  apply Operations.Arrow.ext
  ext U z
  apply Prod.ext
  · exact (Examples.GroupoidCompletion.TrivialGroup.label_eq_one U _).trans
      (Examples.GroupoidCompletion.TrivialGroup.label_eq_one U _).symm
  · rfl

theorem collapse_not_faithful :
    ¬ (StackDescentTransformation.component collapse point).Faithful := by
  intro h
  exact quarterTurn_loop_ne ((StackDescentTransformation.component collapse point).map_injective
    (collapse_loop quarterTurn 1))

abbrev collapseBibundle := functorBibundle collapse

theorem collapse_no_tensorInverse : ¬ Nonempty (TensorInverse collapseBibundle) := by
  rintro ⟨i⟩
  have ff := (i.sourceFullyFaithful collapseBibundle point).ofIso
    (componentIso (reconstructionIso (collapse ≫ Bundle.unit target)).symm point)
  apply quarterTurn_loop_ne
  apply ff.map_injective
  exact congrArg (Bundle.regularFunctor target).map (collapse_loop quarterTurn 1)

theorem collapse_not_leftPrincipal : ¬ LeftPrincipal collapseBibundle :=
  fun h => collapse_no_tensorInverse ((leftPrincipal_iff_tensorInverse collapseBibundle).mp h)

theorem collapse_no_stackEquivalence :
    ¬ ∃ e : CategoryTheory.Bicategory.Equivalence (Bundle.pseudofunctor source)
      (Bundle.pseudofunctor target), e.hom = tensorTransformation collapseBibundle :=
  fun h => collapse_no_tensorInverse ((tensorInverse_iff_stackEquivalence collapseBibundle).mpr h)

def includeGroup : trivialGroup ⟶ group := locallyConstantGroupMap (1 : PUnit →* C4)

/-- On isomorphism classes of chart objects the same map is an equivalence,
although it identifies distinct isotropy arrows. -/
def collapseOrbitEquiv (X : Sheaf SmoothOpenSite.topology Type) :
    Quotient (isIsomorphicSetoid (source.Object X)) ≃
      Quotient (isIsomorphicSetoid (target.Object X)) where
  toFun := Quotient.map (StackDescentTransformation.component collapse X).obj
    (fun _ _ ⟨i⟩ => ⟨(StackDescentTransformation.component collapse X).mapIso i⟩)
  invFun := Quotient.map (SheafGroupoidAction.trivialMapFunctor (M := point) includeGroup).obj
    (fun _ _ ⟨i⟩ => ⟨(SheafGroupoidAction.trivialMapFunctor includeGroup).mapIso i⟩)
  left_inv q := Quotient.inductionOn q (fun _ => rfl)
  right_inv q := Quotient.inductionOn q (fun _ => rfl)

theorem collapseOrbitEquiv_apply (X : Sheaf SmoothOpenSite.topology Type) (m : source.Object X) :
    collapseOrbitEquiv X (Quotient.mk _ m) =
      Quotient.mk _ ((StackDescentTransformation.component collapse X).obj m) := rfl

end Examples.PrincipalBibundleNoninvertible
