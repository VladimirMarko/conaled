import SquareKit.SheafGroupoidBibundleAssociator
import Mathlib.CategoryTheory.Bicategory.Basic

/-! Lawful represented sheaf groupoids and their principal-bibundle bicategory. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

instance : CategoryStruct (SquareKit.SheafGroupoid J) where
  Hom G H := Bibundle G.toOperations H.toOperations
  id G := Bibundle.identity G.toOperations
  comp := Bibundle.tensor

instance bibundleHomCategory (G H : SquareKit.SheafGroupoid J) : Category (G ⟶ H) :=
  Bibundle.instCategory

instance : Bicategory (SquareKit.SheafGroupoid J) where
  toCategoryStruct := inferInstance
  homCategory := bibundleHomCategory
  whiskerLeft f _ _ η := Bibundle.map (Bibundle.Map.ident f) η
  whiskerRight η h := Bibundle.map η (Bibundle.Map.ident h)
  associator := Bibundle.associator
  leftUnitor := Bibundle.leftUnitor
  rightUnitor := Bibundle.rightUnitor
  whiskerLeft_id f g := Bibundle.map_id f g
  id_whiskerRight f g := Bibundle.map_id f g
  whiskerLeft_comp := by
    intro a b c f g h i η θ
    change Bibundle.map (Bibundle.Map.ident f) (η.comp θ) =
      (Bibundle.map (Bibundle.Map.ident f) η).comp (Bibundle.map (Bibundle.Map.ident f) θ)
    have e := Bibundle.map_comp (Bibundle.Map.ident f) (Bibundle.Map.ident f) η θ
    have hi : (Bibundle.Map.ident f).comp (Bibundle.Map.ident f) = Bibundle.Map.ident f :=
      Category.id_comp (𝟙 f)
    rw [hi] at e
    exact e
  comp_whiskerRight := by
    intro a b c f g h η θ i
    change Bibundle.map (η.comp θ) (Bibundle.Map.ident i) =
      (Bibundle.map η (Bibundle.Map.ident i)).comp (Bibundle.map θ (Bibundle.Map.ident i))
    have e := Bibundle.map_comp η θ (Bibundle.Map.ident i) (Bibundle.Map.ident i)
    have hi : (Bibundle.Map.ident i).comp (Bibundle.Map.ident i) = Bibundle.Map.ident i :=
      Category.id_comp (𝟙 i)
    rw [hi] at e
    exact e
  id_whiskerLeft {a b f g} η := by
    change Bibundle.map (Bibundle.Map.ident (Bibundle.identity a.toOperations)) η =
      (Bibundle.leftUnitor f).hom ≫ η ≫ (Bibundle.leftUnitor g).inv
    apply (cancel_mono (Bibundle.leftUnitor g).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      Bibundle.leftUnitor_natural η
  whiskerRight_id {a b f g} η := by
    change Bibundle.map η (Bibundle.Map.ident (Bibundle.identity b.toOperations)) =
      (Bibundle.rightUnitor f).hom ≫ η ≫ (Bibundle.rightUnitor g).inv
    apply (cancel_mono (Bibundle.rightUnitor g).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      Bibundle.rightUnitor_natural η
  comp_whiskerLeft {a b c d} f g {h h'} η := by
    change Bibundle.map (Bibundle.Map.ident (Bibundle.tensor f g)) η =
      (Bibundle.associator f g h).hom ≫
        Bibundle.map (Bibundle.Map.ident f) (Bibundle.map (Bibundle.Map.ident g) η) ≫
          (Bibundle.associator f g h').inv
    apply (cancel_mono (Bibundle.associator f g h').hom).mp
    have e := Bibundle.associator_natural (Bibundle.Map.ident f) (Bibundle.Map.ident g) η
    rw [Bibundle.map_id] at e
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using e
  whiskerRight_comp {a b c d f f'} η g h := by
    change Bibundle.map η (Bibundle.Map.ident (Bibundle.tensor g h)) =
      (Bibundle.associator f g h).inv ≫
        Bibundle.map (Bibundle.map η (Bibundle.Map.ident g)) (Bibundle.Map.ident h) ≫
          (Bibundle.associator f' g h).hom
    apply (cancel_epi (Bibundle.associator f g h).hom).mp
    have e := Bibundle.associator_natural η (Bibundle.Map.ident g) (Bibundle.Map.ident h)
    rw [Bibundle.map_id] at e
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using e.symm
  whisker_assoc {a b c d} f {g g'} η h := by
    apply (cancel_mono (Bibundle.associator f g' h).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      Bibundle.associator_natural (Bibundle.Map.ident f) η (Bibundle.Map.ident h)
  whisker_exchange {a b c f g h i} η θ := by
    have e := Bibundle.map_comp (Bibundle.Map.ident f) η θ (Bibundle.Map.ident i)
    have e' := Bibundle.map_comp η (Bibundle.Map.ident g) (Bibundle.Map.ident h) θ
    change Bibundle.map ((𝟙 f) ≫ η) (θ ≫ (𝟙 i)) = _ at e
    change Bibundle.map (η ≫ (𝟙 g)) ((𝟙 h) ≫ θ) = _ at e'
    simp only [Category.id_comp, Category.comp_id] at e e'
    exact e.symm.trans e'
  pentagon f g h i := (Bibundle.pentagon f g h i).symm
  triangle f g := Bibundle.triangle f g

end SquareKit.SheafGroupoid
