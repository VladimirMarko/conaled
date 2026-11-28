import SquareKit.SheafGroupoidBibundleFunctor
import SquareKit.SheafGroupoidBibundlePrincipality
import SquareKit.SheafGroupoidTrivialActionMap
import Examples.SheafAssociatedBundle
/-! Noncommuting S3 isotropy and composition order through the actual tensor stack map. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.PrincipalBibundleNoncommuting
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SmoothOpenSite SquareKit.SmoothPresentationSite SquareKit.SmoothGeometricKL
open Examples.SheafAssociatedBundle Examples.SheafAssociatedBundle.GroupChange
open SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
abbrev point := Examples.SmoothTorsors.point
abbrev source := SheafGroupoidAction.operations (SheafGroupoidAction.trivialAction group point)
abbrev target := SheafGroupoidAction.operations (SheafGroupoidAction.trivialAction productGroup point)
def diagonalTransformation : source.pseudofunctor ⟶ target.pseudofunctor :=
  SheafGroupoidAction.trivialMapTransformation (M := point) diagonal
abbrev base : source.Object point := ⟨𝟙 point⟩
def loop (g : S3) : base ⟶ base where
  map := SheafRelation.lift (constantSection point g) (𝟙 point)
  source := rfl
  target := rfl

theorem loop_comp (g h : S3) : loop g ≫ loop h = loop (h * g) := by
  apply Operations.Arrow.ext
  have hl : (loop g ≫ loop h).map ≫ SheafGroupoidAction.label =
      SheafTorsor.labelMul ((loop h).map ≫ SheafGroupoidAction.label)
        ((loop g).map ≫ SheafGroupoidAction.label) := by
    change CategoryTheory.Limits.pullback.lift _ _ _ ≫ SheafTorsor.labelMul _ _ = _
    rw [SheafTorsor.labelMul_precomp]
    simp only [← Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
      CategoryTheory.Limits.pullback.lift_snd]
  have hs : (loop g ≫ loop h).map ≫ SheafGroupoidAction.source = (loop g).map ≫
      SheafGroupoidAction.source := by
    change CategoryTheory.Limits.pullback.lift _ _ _ ≫ _ ≫ SheafGroupoidAction.source = _
    simp only [CategoryTheory.Limits.pullback.lift_fst_assoc]
  ext U z
  apply Prod.ext
  · exact (congrArg (fun a => a.hom.app U z) hl).trans
      (((constantLabel S3).app U).hom.map_mul h g).symm
  · exact congrArg (fun a => a.hom.app U z) hs

theorem noncommuting_loops : loop swap ≫ loop otherSwap ≠ loop otherSwap ≫ loop swap := by
  rw [loop_comp, loop_comp]
  intro he
  have hv := congrArg (fun f : base ⟶ base =>
    (f.map.hom.app realStage (𝟙 (op (free 0)))).1) he
  apply order_control
  rw [show h = (constantLabel (S3 × S3)).app realStage (swap,1) from rfl,
    show first = locallyConstantGroupMap firstHom from rfl, map_constant]
  exact (((constantLabel S3).app realStage).hom.map_mul otherSwap swap).symm.trans
    (hv.trans (((constantLabel S3).app realStage).hom.map_mul swap otherSwap))

instance diagonal_faithful (X : Sheaf SmoothOpenSite.topology Type) :
    (StackDescentTransformation.component diagonalTransformation X).Faithful where
  map_injective := by
    intro m n f g he
    apply Operations.Arrow.ext
    ext U z
    have hv := congrArg (fun a => a.map.hom.app U z) he
    apply Prod.ext
    · have hf := congrArg (fun a : group ⟶ group => a.hom.app U (f.map.hom.app U z).1) diagonal_first
      have hg := congrArg (fun a : group ⟶ group => a.hom.app U (g.map.hom.app U z).1) diagonal_first
      exact hf.symm.trans ((congrArg (fun a => first.hom.app U a.1) hv).trans hg)
    · exact congrArg (fun a : target.arrows.obj.obj U => a.2) hv

abbrev diagonalBibundle := functorBibundle diagonalTransformation
abbrev tensorOnRegular := Bundle.regularFunctor source (X := point) ⋙
  StackDescentTransformation.component (tensorTransformation diagonalBibundle) point

def regularComparison : tensorOnRegular ≅
    StackDescentTransformation.component diagonalTransformation point ⋙ Bundle.regularFunctor target :=
  componentIso (tensorRecovery diagonalBibundle ≪≫
    (reconstructionIso (diagonalTransformation ≫ Bundle.unit target)).symm) point

instance tensorOnRegular_faithful : tensorOnRegular.Faithful := by
  have : (Bundle.regularFunctor target (X := point)).Faithful :=
    ⟨fun he => (Bundle.regularFullyFaithful target).map_injective he⟩
  have : (StackDescentTransformation.component diagonalTransformation point ⋙
      Bundle.regularFunctor target).Faithful :=
    { map_injective := fun he => (StackDescentTransformation.component diagonalTransformation point).map_injective
        ((Bundle.regularFullyFaithful target).map_injective he) }
  exact Functor.Faithful.of_iso regularComparison.symm

/-- The actual balanced-tensor map on regular bundles retains the multiplication order. -/
theorem tensor_noncommuting :
    tensorOnRegular.map (loop swap) ≫ tensorOnRegular.map (loop otherSwap) ≠
      tensorOnRegular.map (loop otherSwap) ≫ tensorOnRegular.map (loop swap) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact fun h => noncommuting_loops (tensorOnRegular.map_injective h)

theorem tensor_order (g h : S3) :
    tensorOnRegular.map (loop g) ≫ tensorOnRegular.map (loop h) =
      tensorOnRegular.map (loop (h * g)) := by
  rw [← Functor.map_comp, loop_comp]

end Examples.PrincipalBibundleNoncommuting
