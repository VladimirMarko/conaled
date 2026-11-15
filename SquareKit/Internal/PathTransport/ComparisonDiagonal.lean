import SquareKit.Internal.PathTransport.ComparisonHorizontalFiber

/-! Identity comparison data for generated parameter coherence. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

def Context.diagonal (C : Grpd.{u,u}) : Context.{u} := ⟨C,C,𝟭 _⟩
def Family.diagonal {C : Grpd.{u,u}} (A : C ⥤ Grpd.{u,u}) : Family (Context.diagonal C) :=
  ⟨A,A,𝟙 _⟩
def Section.diagonal {C : Grpd.{u,u}} {A : C ⥤ Grpd.{u,u}} (s : GroupoidModel.Section A) :
    Section (Family.diagonal A) := ⟨s,s,GroupoidModel.Section.familyImage_id s⟩
def Substitution.diagonal {C D : Grpd.{u,u}} (F : D ⥤ C) :
    Substitution (Context.diagonal D) (Context.diagonal C) := ⟨F,F,rfl⟩

theorem Family.diagonal_extend {C : Grpd.{u,u}} (A : C ⥤ Grpd.{u,u}) :
    (Family.diagonal A).extend = Context.diagonal (@Grpd.of (Extend A) Groupoid.ofIsGroupoid) :=
  congrArg (fun F => Context.mk (@Grpd.of (Extend A) Groupoid.ofIsGroupoid)
    (@Grpd.of (Extend A) Groupoid.ofIsGroupoid) F) (totalMap_id A)

theorem Family.diagonal_reindex {C D : Grpd.{u,u}} (A : C ⥤ Grpd.{u,u}) (F : D ⥤ C) :
    (Family.diagonal A).reindex (Substitution.diagonal F) = Family.diagonal (F ⋙ A) := by
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  simp [Family.reindex, Family.diagonal, Substitution.diagonal]

def Signature.diagonal (C : Grpd.{u,u}) (B : C ⥤ Type u) : Signature.{u} :=
  ⟨Context.diagonal C,B,B,𝟙 _⟩

theorem Signature.diagonal_baseFamily (C D : Grpd.{u,u}) (B : C ⥤ Type u) :
    (Signature.diagonal C B).baseFamily (Context.diagonal D) = Family.diagonal (constant C) := rfl

theorem Signature.diagonal_primitive (C : Grpd.{u,u}) (B : C ⥤ Type u) :
    (Signature.diagonal C B).primitive = Family.diagonal (setFamily B) := by
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  exact whiskerRight_id' discrete

theorem Signature.diagonal_baseSubstitution {C D : Grpd.{u,u}} (B : C ⥤ Type u)
    (x : GroupoidModel.Section (constant (Γ := D) C)) :
    (Signature.diagonal C B).baseSubstitution (Section.diagonal x) =
      Substitution.diagonal (baseFunctor x) := by
  apply Substitution.ext <;> rfl

theorem Signature.diagonal_fiber {C D : Grpd.{u,u}} (B : C ⥤ Type u)
    (x : GroupoidModel.Section (constant (Γ := D) C)) :
    (Signature.diagonal C B).fiber (Section.diagonal x) = Family.diagonal (primitiveFiber B x) := by
  unfold Signature.fiber
  rw [Signature.diagonal_primitive, Signature.diagonal_baseSubstitution,
    Family.diagonal_reindex]
  rfl

theorem Family.diagonal_identity {C : Grpd.{u,u}} (A : C ⥤ Grpd.{u,u})
    (x y : GroupoidModel.Section A) :
    (Family.diagonal A).identity (Section.diagonal x) (Section.diagonal y) =
      Family.diagonal (identityFamily A x y) := by
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext c
  fapply CategoryTheory.Functor.ext
  · intro p
    dsimp [Family.identity, Family.diagonal, Section.diagonal, identityMap, directIdentityMap,
      discrete]
    simp only [eqToHom_app, Grpd.comp_eq_comp, CategoryTheory.Functor.comp_obj]
    rfl
  · intro p q f
    exact congrArg Discrete.Hom.mk rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
