import SquareKit.Internal.PathTransport.TwoPathContractionSquare
namespace SquareKit.Internal.PathTransport.TwoIdentityTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]
variable [IsLocallyGroupoid B]
omit [IsLocallyGroupoid B] in
private theorem whisker_identity_heq {a b c : B} (u : b ⟶ a) (f : a ⟶ a)
    (e : f = 𝟙 a) {v v' : a ⟶ c} (σ : v ⟶ v') :
    HEq (u ◁ f ◁ σ) (u ◁ σ) := by
  cases e
  simp only [id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_comp, whiskerLeft_eqToHom]
  apply HEq.trans (eqToHom_comp_heq _ _)
  exact comp_eqToHom_heq _ _
omit [Bicategory.Strict A] in
/-- On the identity path, an endpoint comparison with fixed first endpoint retains its second cell. -/
theorem homComparison_identity_path (H : StrictPseudofunctor A B)
    {a : A} {b c : B} (u : H.obj a ⟶ b) [IsIso u]
    {v v' : H.obj a ⟶ c} (σ : v ⟶ v') :
    HEq ((homComparison (StrictTwoTransformation.Trans.id H)
      (eqToHom (Category.id_comp u).symm)
      (σ ≫ eqToHom (Category.id_comp v').symm)).app (𝟙 a)) (inv u ◁ σ) := by
  simp [homComparison, homNaturality, inverseMate, StrictTwoTransformation.Trans.id,
    Strict.associator_eqToIso]
  exact whisker_identity_heq (inv u) (H.map (𝟙 a)) (H.map_id a) σ
end SquareKit.Internal.PathTransport.TwoIdentityTransport
