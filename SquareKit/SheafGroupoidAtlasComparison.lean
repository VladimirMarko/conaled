import SquareKit.SheafGroupoidAtlasStackification

/-! Atlas completion comparisons retain their common ambient groupoid. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory Opposite Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws]
variable {U V : Sheaf J (Type (max u v))} {p : U ⟶ G.objects} {q : V ⟶ G.objects}
variable (D : Chart G p p) (E : Chart G q q)

/-- The actual atlas groupoid maps to its ambient object and arrow sheaves. -/
def ambientTransformation : D.atlasOperations.pseudofunctor ⟶ G.pseudofunctor :=
  D.atlasPresentation ≫ D.transformation

theorem representedMapFunctor_ambient {X : Sheaf J (Type (max u v))}
    (r : U ⟶ V) (comm : r ≫ q = p) :
    D.representedMapFunctor (X := X) E r comm ⋙ E.atlasToChart ⋙ E.toGroupoid =
      D.atlasToChart ⋙ D.toGroupoid := by
  change D.atlasToChart ⋙ D.atlasMap E r comm ⋙
    (E.chartToAtlas ⋙ E.atlasToChart) ⋙ E.toGroupoid = _
  rw [chartToAtlas_atlasToChart, Functor.id_comp]
  rw [atlasMap_toGroupoid]

/-- Returning from represented arrows to their coordinate presentation is exact. -/
def atlasPresentation_inverse : D.atlasPresentationInverse ≫ D.atlasPresentation ≅ 𝟙 D.pseudofunctor :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Cat.Hom.isoMk (Iso.refl _)) (by
    intro X Y f
    cases X
    cases Y
    cases f
    apply Cat.Hom₂.ext
    ext m
    dsimp [atlasPresentation, atlasPresentationInverse, Pseudofunctor.StrongTrans.vcomp,
      Pseudofunctor.StrongTrans.id, Cat.Hom.isoMk]
    simp
    repeat' first
      | erw [CategoryTheory.Functor.map_id]
      | erw [Category.comp_id]
    all_goals rfl)

/-- The ambient comparison commutes before completion. -/
def representedMap_ambient (r : U ⟶ V) (comm : r ≫ q = p) :
    D.representedMap E r comm ≫ E.ambientTransformation ≅ D.ambientTransformation :=
  associator (D.atlasPresentation ≫ D.atlasTransformation E r comm)
      E.atlasPresentationInverse (E.atlasPresentation ≫ E.transformation) ≪≫
    whiskerLeftIso (D.atlasPresentation ≫ D.atlasTransformation E r comm)
      ((associator E.atlasPresentationInverse E.atlasPresentation E.transformation).symm ≪≫
        whiskerRightIso E.atlasPresentation_inverse E.transformation ≪≫ leftUnitor (B := Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
          Cat.{max u v, max (u + 1) (v + 1)}) E.transformation) ≪≫
    associator D.atlasPresentation (D.atlasTransformation E r comm) E.transformation ≪≫
    whiskerLeftIso D.atlasPresentation (D.atlasTransformation_toGroupoid E r comm)

/-- The completed ambient map is extended from the constructed input map. -/
def completedAmbient : Bundle.pseudofunctor D.atlasOperations ⟶ Bundle.pseudofunctor G :=
  Bundle.completeMap D.ambientTransformation

/-- Every commuting atlas square retains its ambient meaning after completion. -/
def completedMap_ambient (r : U ⟶ V) (comm : r ≫ q = p) :
    D.completedMap E r comm ≫ E.completedAmbient ≅ D.completedAmbient :=
  Bundle.completeMap_comp _ _ ≪≫ Bundle.completeMapModification (D.representedMap_ambient E r comm)

variable {W : Sheaf J (Type (max u v))} {s : W ⟶ G.objects} (R : Chart G s s)

/-- Both routes from an actual common refinement agree as invertible modifications. -/
def completedCommonRefinement (r : W ⟶ U) (hr : r ≫ p = s)
    (t : W ⟶ V) (ht : t ≫ q = s) :
    R.completedMap D r hr ≫ D.completedAmbient ≅ R.completedMap E t ht ≫ E.completedAmbient :=
  R.completedMap_ambient D r hr ≪≫ (R.completedMap_ambient E t ht).symm

end SquareKit.SheafGroupoid.Chart
