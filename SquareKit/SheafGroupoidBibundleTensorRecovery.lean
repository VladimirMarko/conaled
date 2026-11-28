import SquareKit.SheafGroupoidBibundleStackTensor

/-! Recovery of the actual balanced product from tensor stack maps. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open SquareKit.SheafGroupoid.Bundle.BalancedAction SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H) {X Y Z : Sheaf J (Type (max u v))}

variable {K : Operations J} [K.Laws] (Q : Bibundle H K)

theorem sourceMap_generic : sourceMap P (genericArrow (G := G)) = leftOnP P.right P.left := rfl

variable (θ : G.pseudofunctor ⟶ Bundle.pseudofunctor H)

theorem reconstructedTensor_generic :
    recoveredGeneric (θ ≫ tensorTransformation Q) =
      arrowTensorMap Q.right Q.left (recoveredBibundle θ).right (recoveredBibundle θ).left := by
  have h := SquareKit.StackDescentTransformation.mapHom_vcomp θ (tensorTransformation Q)
    (M₁ := SquareKit.SheafGroupoid.Bibundle.identityObject G) (M₂ := SquareKit.SheafGroupoid.Bibundle.identityObject G)
    (arrowSource G) (arrowTarget G) genericArrow
  have he : leftOnP (recoveredBibundle θ).right (recoveredBibundle θ).left =
      recoveredGeneric θ := (sourceMap_generic (recoveredBibundle θ)).symm.trans
        (sourceMap_recovered θ genericArrow)
  exact h.trans (congrArg (fun f =>
    (baseChangeIso (recoveredRight θ) Q.right Q.left (arrowSource G)).inv.comp
      ((tensorMap Q.right Q.left f).comp
        (baseChangeIso (recoveredRight θ) Q.right Q.left (arrowTarget G)).hom)) he.symm)

theorem reconstructedTensor_act {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y)
    (k : K.Section U)
    (t : Fiber K G.objects (compositionRightBundle (recoveredRight θ) Q.right Q.left).family
      (atSection x) k) :
    recoveredAct (θ ≫ tensorTransformation Q) g k t =
      residualAct Q.right Q.left (recoveredRight θ) (recoveredLeft θ) g k t := by
    exact congrArg (fun a : Bundle.Map
      (Bundle.reindex (compositionRightBundle (recoveredRight θ) Q.right Q.left) (arrowSource G))
      (Bundle.reindex (compositionRightBundle (recoveredRight θ) Q.right Q.left) (arrowTarget G)) =>
      a.hom.app (point K (arrowContext G)
        ((arrowContext G).obj.elementsMk U (arrowPoint g)) k) t)
      (reconstructedTensor_generic Q θ)



end SquareKit.SheafGroupoid.Bibundle

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open SquareKit.SheafGroupoid.Bundle.BalancedAction SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H) {X Y Z : Sheaf J (Type (max u v))}

variable {K : Operations J} [K.Laws] (Q : Bibundle H K)

variable (θ : G.pseudofunctor ⟶ Bundle.pseudofunctor H)

theorem reconstructedTensor_left : recoveredLeft (θ ≫ tensorTransformation Q) =
    compositionLeftAction (recoveredRight θ) (recoveredLeft θ) Q.right Q.left := by
  apply Bundle.LeftAction.ext
  intro U x y g k t
  exact reconstructedTensor_act Q θ g k t

theorem reconstructedTensor_eq : recoveredBibundle (θ ≫ tensorTransformation Q) =
    tensor (recoveredBibundle θ) Q :=
  congrArg (fun L => Bibundle.mk (compositionRightBundle (recoveredRight θ) Q.right Q.left) L)
    (reconstructedTensor_left Q θ)

def reconstructedTensorIso :
    recoveredBibundle (θ ≫ tensorTransformation Q) ≅ tensor (recoveredBibundle θ) Q :=
  eqToIso (reconstructedTensor_eq Q θ)

end SquareKit.SheafGroupoid.Bibundle
