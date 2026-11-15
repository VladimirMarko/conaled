import SquareKit.Internal.Cubical.FunctionFilling
import Examples.CubicalSumFilling

/-! Fill dependent functions whose result fiber changes with their argument.
The selected function returns the last element, including after two substitutions. -/
namespace Examples.CubicalFunctionFilling
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling CubicalSumFilling

def lastBody : Term result where
  val x := show Fin (Nat.succ x.val.2) from Fin.last x.val.2
  property {x y} f := cast_last (secondIndex.val x) (secondIndex.val y) (secondIndex.property f)

abbrev selected : Term (pi argument result) := lam lastBody
noncomputable abbrev functions := piFilling firstFilling
  (discreteFilling_lawful index (fun _ => ℕ)) secondFilling

theorem lawful : functions.Lawful := piFilling_lawful firstFilling
  (discreteFilling_lawful index (fun _ => ℕ)) secondFilling
  (discreteFilling_lawful secondIndex (fun n => Fin (n+1)))

def functionBox : OpenBox (reindex (pi argument result) path) (Cofibration.top naturals) where
  tube := PartialSection.ofTerm _ (selected.reindex path)
  base := selected
  boundary _ _ := rfl

theorem selected_function (x : naturals.Elements) :
    (functions.comp path (Cofibration.top naturals) functionBox).val x = selected.val x :=
  Filling.comp_boundary lawful path (Cofibration.top naturals) functionBox x rfl

theorem retains_dependent_result :
    (((functions.comp path (Cofibration.top naturals) functionBox).reindex (twice ≫ successor)).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))).val (𝟙 _) (6 : ℕ) = (6 : Fin 7) := by
  rw [show ((functions.comp path (Cofibration.top naturals) functionBox).reindex
      (twice ≫ successor)).val (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) =
      selected.val ((twice ≫ successor).mapElements.obj
        (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))) from selected_function _]
  rfl

theorem result_not_erased :
    ((((functions.comp path (Cofibration.top naturals) functionBox).reindex (twice ≫ successor)).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))).val (𝟙 _) (6 : ℕ)).val ≠ 0 := by
  rw [retains_dependent_result]
  decide

theorem two_substitutions :
    ((functions.reindex successor).reindex twice).fill path
      (((Cofibration.top naturals).reindex successor).reindex twice)
      ((functionBox.reindex successor).reindex twice) =
      ((functions.fill path (Cofibration.top naturals) functionBox).reindex
        (liftSub (interval naturals) successor)).reindex (liftSub (interval naturals) twice) :=
  ((lawful.reindex successor).uniform path _ (functionBox.reindex successor) twice).trans
    (congrArg (fun t => t.reindex (liftSub (interval naturals) twice))
      (lawful.uniform path _ functionBox successor))

end Examples.CubicalFunctionFilling
