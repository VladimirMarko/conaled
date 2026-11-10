import SquareKit.Internal.PathTransport.GeneratedCylinderFamilies

/-! Selected section coherence follows from the generated pairing substitution.
In particular, no identity-elimination preservation field is assumed. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u)
variable {G : C ⥤ D} (η : F ≅ G)
variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
variable (h : α ≫ whiskerRight η.hom Q = β)
local notation "S" => Signature.mk (Context.mk C D F) P Q α
local notation "T" => Signature.mk (Context.mk C D G) P Q β
local notation "L" => Instance.fullModel C P
local notation "R" => Instance.fullModel D Q

/-- Pairing the actual interpreted term gives its entire section functor. -/
theorem generatedSection_commutes (K : Signature.{u})
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) (hA : Typed.TyDeriv.{u+1} Γ γ A a)
    (hx : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    (x (Instance.fullModel K.base.left K.leftFiber)).down.lift ⋙
        generatedContextMap K (.ext hΓ hA) =
      generatedContextMap K hΓ ⋙ (x (Instance.fullModel K.base.right K.rightFiber)).down.lift :=
  generatedSubstitution_commutes K (.ext hΓ hA) hΓ
    (.pair hA (.id hΓ) (.sub hx (.id hΓ)))

/-- An isomorphism-valued square for the actual interpreted section functors.
The term may use contextual J with arbitrary supported finite dependent tails. -/
theorem contextComparison_section (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) (hx : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    isoWhiskerLeft (x L).down.lift (contextComparison F P η Q α β h (.ext hΓ hA)) ≪≫
        eqToIso (generatedSection_commutes T hΓ hA hx) =
      eqToIso (generatedSection_commutes S hΓ hA hx) ≪≫
        isoWhiskerRight (contextComparison F P η Q α β h hΓ) (x R).down.lift :=
  contextComparison_substitution F P η Q α β h (.ext hΓ hA) hΓ
    (.pair hA (.id hΓ) (.sub hx (.id hΓ)))

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
