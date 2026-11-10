import SquareKit.Internal.PathTransport.ComparisonReindex

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

private theorem pre_eqToHom {C D : Type u} [Category.{u} C] [Category.{u} D]
    (A : C ⥤ Cat.{u,u}) {F G : D ⥤ C} (h : F = G) :
    Grothendieck.map (eqToHom (congrArg (· ⋙ A) h)) ⋙ Grothendieck.pre A G =
      Grothendieck.pre A F := by
  cases h
  rw [eqToHom_refl, Grothendieck.map_id_eq, CategoryTheory.Functor.id_comp]

theorem whisker_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (h : F = G) (K : D ⥤ E) :
    whiskerRight (eqToHom h) K = eqToHom (congrArg (· ⋙ K) h) := by
  cases h
  exact whiskerRight_id' K

namespace Family
variable {Γ Δ : Context.{u}}

/-- The ordinary comprehension maps form a commuting comparison square. -/
def lift (A : Family Γ) (σ : Substitution Δ Γ) :
    Substitution (A.reindex σ).extend A.extend where
  left := Grothendieck.pre (A.left ⋙ Grpd.forgetToCat) σ.left
  right := Grothendieck.pre (A.right ⋙ Grpd.forgetToCat) σ.right
  commutes := by
    dsimp [extend, reindex]
    rw [whiskerRight_comp, Grothendieck.map_comp_eq]
    simp only [CategoryTheory.Functor.assoc]
    change _ = Grothendieck.map (whiskerRight (whiskerLeft σ.left A.map) Grpd.forgetToCat) ⋙
      Grothendieck.map (whiskerRight (eqToHom (congrArg (· ⋙ A.right) σ.commutes)) Grpd.forgetToCat) ⋙
      Grothendieck.pre (A.right ⋙ Grpd.forgetToCat) (Δ.map ⋙ σ.right)
    have he : whiskerRight (eqToHom (congrArg (· ⋙ A.right) σ.commutes)) Grpd.forgetToCat =
        eqToHom (congrArg (· ⋙ A.right ⋙ Grpd.forgetToCat) σ.commutes) :=
      whisker_eq _ _
    rw [he, pre_eqToHom _ σ.commutes]
    rfl

/-- The newest variable is compared by the given family transformation. -/
def «variable» (A : Family Γ) : Section (A.reindex A.weaken) where
  left := GroupoidModel.«variable» A.left
  right := GroupoidModel.«variable» A.right
  commutes := by
    rfl

/-- Pairing is assembled from the section and the comprehension square. -/
def pair (A : Family Γ) (σ : Substitution Δ Γ) (t : Section (A.reindex σ)) :
    Substitution Δ A.extend := Substitution.comp (A.lift σ) t.lift

@[simp] theorem pair_left (A : Family Γ) (σ : Substitution Δ Γ) (t : Section (A.reindex σ)) :
    (A.pair σ t).left = GroupoidModel.pair A.left σ.left t.left := rfl
@[simp] theorem pair_right (A : Family Γ) (σ : Substitution Δ Γ) (t : Section (A.reindex σ)) :
    (A.pair σ t).right = GroupoidModel.pair A.right σ.right t.right := rfl

@[simp] theorem weaken_pair (A : Family Γ) (σ : Substitution Δ Γ) (t : Section (A.reindex σ)) :
    Substitution.comp A.weaken (A.pair σ t) = σ := by ext <;> rfl

theorem variable_pair (A : Family Γ) (σ : Substitution Δ Γ) (t : Section (A.reindex σ)) :
    HEq (A.variable.reindex (A.pair σ t)) t := by
  apply Section.hext
    ((A.reindex_comp A.weaken (A.pair σ t)).trans (congrArg A.reindex (A.weaken_pair σ t)))
    HEq.rfl HEq.rfl

theorem pair_eta (A : Family Γ) (σ : Substitution Δ A.extend) :
    A.pair (Substitution.comp A.weaken σ)
      (cast (congrArg Section (A.reindex_comp A.weaken σ)) (A.variable.reindex σ)) = σ := by
  apply Substitution.ext
  · change GroupoidModel.pair A.left (σ.left ⋙ GroupoidModel.weaken A.left)
      (cast (congrArg Section (A.reindex_comp A.weaken σ)) (A.variable.reindex σ)).left = σ.left
    rw [eq_of_heq (Section.cast_left (A.reindex_comp A.weaken σ) (A.variable.reindex σ))]
    fapply CategoryTheory.Functor.ext
    · intro a; rfl
    · intro a b f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
  · change GroupoidModel.pair A.right (σ.right ⋙ GroupoidModel.weaken A.right)
      (cast (congrArg Section (A.reindex_comp A.weaken σ)) (A.variable.reindex σ)).right = σ.right
    rw [eq_of_heq (Section.cast_right (A.reindex_comp A.weaken σ) (A.variable.reindex σ))]
    fapply CategoryTheory.Functor.ext
    · intro a; rfl
    · intro a b f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl

end Family
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
