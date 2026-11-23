import SquareKit.SheafifiedSliceQuotient
import SquareKit.SubcanonicalSheafStack
/-! Subcanonical recovery of sheafified presentations, including maps and restriction coherence. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafifiedSubcanonical
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} [J.Subcanonical]
variable (K : (Sheaf J (Type u))ᵒᵖ ⥤ Cat)

/-- Restricting any sheaf-context category along the two represented presentations agrees. -/
def comparison : (SheafifiedYoneda.functor J).op ⋙ K ≅ J.yoneda.op ⋙ K :=
  Functor.isoWhiskerRight (NatIso.op (SheafifiedYoneda.subcanonicalIso J)).symm K

abbrev torsorComparison (G : Sheaf J GrpCat.{u}) :
    (SheafifiedYoneda.functor J).op ⋙ SheafTorsor.Stack.functor G ≅
      SubcanonicalSheafStack.torsorFunctor G := comparison (SheafTorsor.Stack.functor G)
abbrev quotientComparison {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) :
    (SheafifiedYoneda.functor J).op ⋙ SheafActionQuotient.Stack.functor a ≅
      SubcanonicalSheafStack.quotientFunctor a := comparison (SheafActionQuotient.Stack.functor a)

def equivalence (U : C) : K.obj (op ((SheafifiedYoneda.functor J).obj U)) ≌
    K.obj (op (J.yoneda.obj U)) :=
  CategoryTheory.Equivalence.mk ((comparison K).hom.app (op U)).toFunctor
    ((comparison K).inv.app (op U)).toFunctor
    (eqToIso (congrArg Cat.Hom.toFunctor ((comparison K).app (op U)).hom_inv_id).symm)
    (eqToIso (congrArg Cat.Hom.toFunctor ((comparison K).app (op U)).inv_hom_id))

/-- The comparison on each context is natural in every arrow of the fiber category. -/
theorem recovery_natural (U : C)
    {P Q : K.obj (op ((SheafifiedYoneda.functor J).obj U))} (h : P ⟶ Q) :
    h ≫ (equivalence K U).unitIso.hom.app Q =
      (equivalence K U).unitIso.hom.app P ≫
        (equivalence K U).inverse.map ((equivalence K U).functor.map h) :=
  (equivalence K U).unitIso.hom.naturality h

/-- A change of context commutes with comparison as an equality of functors. -/
theorem restriction {U V : C} (f : V ⟶ U) :
    K.map ((SheafifiedYoneda.functor J).map f).op ≫ (comparison K).hom.app (op V) =
      (comparison K).hom.app (op U) ≫ K.map (J.yoneda.map f).op :=
  (comparison K).hom.naturality f.op

theorem identity (U : C) :
    K.map ((SheafifiedYoneda.functor J).map (𝟙 U)).op ≫
      (comparison K).hom.app (op U) = (comparison K).hom.app (op U) := by simp

/-- Two successive base changes agree with comparison on objects and all maps. -/
theorem composition {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    K.map ((SheafifiedYoneda.functor J).map f).op ≫
      K.map ((SheafifiedYoneda.functor J).map g).op ≫ (comparison K).hom.app (op W) =
    (comparison K).hom.app (op U) ≫ K.map (J.yoneda.map f).op ≫
      K.map (J.yoneda.map g).op := by
  rw [restriction, ← Category.assoc, restriction, Category.assoc]

/-- Every commuting refinement triangle is respected as an equality of functors. -/
theorem refinement {U V W : C} (f : V ⟶ U) (g : W ⟶ U) (r : W ⟶ V)
    (w : r ≫ f = g) :
    K.map ((SheafifiedYoneda.functor J).map f).op ≫
      K.map ((SheafifiedYoneda.functor J).map r).op ≫ (comparison K).hom.app (op W) =
    (comparison K).hom.app (op U) ≫ K.map (J.yoneda.map g).op := by
  rw [composition, ← K.map_comp, ← op_comp, ← J.yoneda.map_comp, w]


theorem inverse_unit (U : C) :
    ((SheafifiedYoneda.subcanonicalIso J).inv.app U).hom = toSheafify J (yoneda.obj U) := by
  change (inv ((sheafificationAdjunction J (Type u)).counit.app (J.yoneda.obj U))).hom = _
  rw [ObjectProperty.hom_inv]
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  rw [sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift]
  rfl

abbrev torsorEquivalence (G : Sheaf J GrpCat.{u}) (U : C) :=
  equivalence (SheafTorsor.Stack.functor G) U
abbrev quotientEquivalence {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) (U : C) :=
  equivalence (SheafActionQuotient.Stack.functor a) U

theorem torsor_forward (G : Sheaf J GrpCat.{u}) (U : C) :
    (torsorEquivalence G U).functor =
      SheafTorsor.restriction ((SheafifiedYoneda.subcanonicalIso J).inv.app U) := rfl

theorem quotient_forward {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) (U : C) :
    (quotientEquivalence a U).functor =
      SheafActionQuotient.restriction ((SheafifiedYoneda.subcanonicalIso J).inv.app U) := rfl

/-- Automorphism labels are preserved by the actual comparison functor. -/
def stabilizerEquiv {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) (U : C)
    (P : SheafActionQuotient.Object a ((SheafifiedYoneda.functor J).obj U)) :
    (P ⟶ P) ≃ ((quotientEquivalence a U).functor.obj P ⟶
      (quotientEquivalence a U).functor.obj P) :=
  (quotientEquivalence a U).fullyFaithfulFunctor.homEquiv

/-- The recovered ordinary-slice torsor is the existing direct restriction. -/
def torsorSliceComparison (G : Sheaf J GrpCat.{u}) (U : C) :
    (torsorEquivalence G U).functor ⋙ SheafSliceTorsor.forward J U ≅
      SheafifiedSliceTorsor.forward J U := by
  have h : (SheafifiedYoneda.subcanonicalIso J).inv.app U =
      (⟨toSheafify J (yoneda.obj U)⟩ : J.yoneda.obj U ⟶ (SheafifiedYoneda.functor J).obj U) := by
    apply ObjectProperty.hom_ext
    exact inverse_unit U
  rw [torsor_forward, h]
  exact Iso.refl _

/-- The same comparison also retains the ordinary-slice target map. -/
def quotientSliceComparison {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) (U : C) :
    (quotientEquivalence a U).functor ⋙ SheafSliceQuotient.forward a U ≅
      SheafifiedSliceQuotient.forward a U := by
  have h : (SheafifiedYoneda.subcanonicalIso J).inv.app U =
      (⟨toSheafify J (yoneda.obj U)⟩ : J.yoneda.obj U ⟶ (SheafifiedYoneda.functor J).obj U) := by
    apply ObjectProperty.hom_ext
    exact inverse_unit U
  rw [quotient_forward, h]
  exact Iso.refl _


/-- The comparison preserves the actual group action in each represented fiber. -/
theorem torsor_action (G : Sheaf J GrpCat.{u}) (U : C)
    (P : SheafTorsor.Torsor G ((SheafifiedYoneda.functor J).obj U))
    (x : (J.yoneda.obj U).obj.Elements) (g : G.obj.obj x.obj)
    (p : ((torsorEquivalence G U).functor.obj P).family.family.obj x) :
    ((torsorEquivalence G U).functor.obj P).act x g p =
      P.act (((SheafifiedYoneda.subcanonicalIso J).inv.app U).hom.mapElements.obj x) g p := rfl

/-- Every equivariant map is the existing restriction of that map. -/
theorem torsor_map (G : Sheaf J GrpCat.{u}) (U : C)
    {P Q : SheafTorsor.Torsor G ((SheafifiedYoneda.functor J).obj U)} (h : P ⟶ Q) :
    (torsorEquivalence G U).functor.map h =
      h.reindex ((SheafifiedYoneda.subcanonicalIso J).inv.app U) := rfl

/-- Quotient comparison retains its target section, not merely its underlying torsor. -/
theorem quotient_target {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) (U : C)
    (P : SheafActionQuotient.Object a ((SheafifiedYoneda.functor J).obj U))
    (x : (J.yoneda.obj U).obj.Elements)
    (p : ((quotientEquivalence a U).functor.obj P).torsor.family.family.obj x) :
    ((quotientEquivalence a U).functor.obj P).value x p =
      P.value (((SheafifiedYoneda.subcanonicalIso J).inv.app U).hom.mapElements.obj x) p := rfl

theorem quotient_map {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) (U : C)
    {P Q : SheafActionQuotient.Object a ((SheafifiedYoneda.functor J).obj U)} (h : P ⟶ Q) :
    (quotientEquivalence a U).functor.map h =
      h.reindex ((SheafifiedYoneda.subcanonicalIso J).inv.app U) := rfl

end SquareKit.SheafifiedSubcanonical
