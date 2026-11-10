import SquareKit.Internal.PathTransport.FamilyModification

/-! External selected isomorphism comparisons, with constructed comprehension.
No strict field of the existing comparison model is changed. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} {F G : C ⥤ D} (η : F ≅ G)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}}

/-- Compare a family map after transport along the selected context isomorphism.
The component isomorphisms and their base naturality are retained. -/
abbrev Modification (α : A ⟶ F ⋙ B) (β : A ⟶ G ⋙ B) :=
  FamilyModification (α ≫ whiskerRight η.hom B) β

private def transportTotal (α : A ⟶ F ⋙ B) :
    totalMap F α ≅ totalMap G (α ≫ whiskerRight η.hom B) :=
  isoWhiskerLeft (Grothendieck.map (whiskerRight α Grpd.forgetToCat))
    (Grothendieck.preNatIso (B ⋙ Grpd.forgetToCat) η) ≪≫ eqToIso (by
      unfold totalMap
      rw [whiskerRight_comp, Grothendieck.map_comp_eq]
      rfl)

/-- Comprehension's complete functor isomorphism is derived, not an input field. -/
def Modification.totalIso {α : A ⟶ F ⋙ B} {β : A ⟶ G ⋙ B}
    (m : Modification η α β) : totalMap F α ≅ totalMap G β :=
  transportTotal η α ≪≫ isoWhiskerRight (FamilyModification.totalIso m)
    (Grothendieck.pre (B ⋙ Grpd.forgetToCat) G)

/-- The comprehension comparison keeps the selected base component. -/
theorem Modification.totalIso_base {α : A ⟶ F ⋙ B} {β : A ⟶ G ⋙ B}
    (m : Modification η α β) (x : Extend A) :
    ((Modification.totalIso η m).hom.app x).base = η.hom.app x.base := by
  simp [Modification.totalIso, transportTotal, FamilyModification.totalIso,
    FamilyModification.totalComponent, Grothendieck.preNatIso, Grothendieck.transportIso]

/-- The empty generated context has the selected identity comparison. -/
def emptyModification : (𝟭 (Discrete PUnit.{u+1})) ≅ 𝟭 (Discrete PUnit.{u+1}) := Iso.refl _

/-- Constant base-family maps retain the base natural isomorphism itself. -/
def baseModification (K : Type u) [Category.{u} K] :
    FamilyModification (A := constant C (Γ := K)) (B := constant D (Γ := K))
      { app := fun _ => F, naturality := fun {_ _} _ => rfl }
      { app := fun _ => G, naturality := fun {_ _} _ => rfl } where
  app _ := η
  naturality _ := by ext x; simp [constant]; rfl

/-- The primitive fiber square yields an equality after discretization, hence
its selected component natural isomorphisms without an invertibility premise. -/
def fiberModification (P : C ⥤ Type u) (Q : D ⥤ Type u)
    (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
    (h : α ≫ whiskerRight η.hom Q = β) :
    Modification η (A := setFamily P) (B := setFamily Q)
      (whiskerRight α discrete) (whiskerRight β discrete) :=
  FamilyModification.ofEq (by
    change whiskerRight α discrete ≫ whiskerRight (whiskerRight η.hom Q) discrete = _
    rw [← whiskerRight_comp, h])

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
