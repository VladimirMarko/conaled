import SquareKit.SheafFunction
import SquareKit.Family
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections

/-! Experimental internal section objects from Mathlib's toOver/sections
adjunction. Products have base first and parameter second. Sections live in
Type(max u v), the constructed sheaf exponential's supported universe.
Callers supply only a site and an ordinary display map. A stage section of
this object is not an arbitrary function between same-stage fibers. -/
noncomputable section
namespace SquareKit.SheafSections
open CategoryTheory MonoidalCategory SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A Γ X Y : Sheaf J (Type (max u v))}

-- The cartesian and monoidal sheaf instances share the same tensor; expose
-- their definitional agreement to instance search for Mathlib's section functor.
local instance (Γ : Sheaf J (Type (max u v))) : @Closed _ _
    (inferInstance : CartesianMonoidalCategory (Sheaf J (Type (max u v)))).toSemiCartesianMonoidalCategory.toMonoidalCategory Γ := by
  exact (inferInstance : Closed Γ)

local instance : MonoidalCategory (Sheaf J (Type (max u v))) :=
  (inferInstance : CartesianMonoidalCategory (Sheaf J (Type (max u v)))).toSemiCartesianMonoidalCategory.toMonoidalCategory
local instance : BraidedCategory (Sheaf J (Type (max u v))) :=
  BraidedCategory.ofCartesianMonoidalCategory

local instance (Γ : Sheaf J (Type (max u v))) : ChosenPullbacksAlong (curryRightUnitorHom Γ) :=
  ChosenPullbacksAlong.ofHasPullbacksAlong _

/-- Mathlib's actual internal object of sections of the display p. -/
abbrev sections (p : A ⟶ Γ) := (Over.sections Γ).obj (Over.mk p)

/-- Parameterized sections, retaining the actual display equation. -/
abbrev Param (p : A ⟶ Γ) (X : Sheaf J (Type (max u v))) :=
  {f : product Γ X ⟶ A // f ≫ p = fst Γ X}

private theorem tensor_inv_fst (Γ X : Sheaf J (Type (max u v))) :
    ((CartesianMonoidalCategory.tensorLeftIsoProd Γ).app X).inv ≫
      CartesianMonoidalCategory.fst Γ X = Limits.prod.fst :=
  Limits.IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct Γ X) (Limits.limit.isLimit _) ⟨.left⟩

private theorem tensor_inv_snd (Γ X : Sheaf J (Type (max u v))) :
    ((CartesianMonoidalCategory.tensorLeftIsoProd Γ).app X).inv ≫
      CartesianMonoidalCategory.snd Γ X = Limits.prod.snd :=
  Limits.IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct Γ X) (Limits.limit.isLimit _) ⟨.right⟩

/-- Adapt base × parameter to Mathlib's parameter ⊗ base convention. -/
def parameterComparison (Γ X : Sheaf J (Type (max u v))) : product Γ X ≅ X ⊗ Γ :=
  SheafFunction.productComparison Γ X ≪≫ β_ Γ X

@[reassoc (attr := simp)] theorem parameterComparison_fst (Γ X : Sheaf J (Type (max u v))) :
    (parameterComparison Γ X).hom ≫ CartesianMonoidalCategory.fst X Γ = snd Γ X := by
  change ((productIso Γ X).hom ≫
    ((CartesianMonoidalCategory.tensorLeftIsoProd Γ).app X).inv ≫ (β_ Γ X).hom) ≫ _ = _
  simp only [Category.assoc, CartesianMonoidalCategory.braiding_hom_fst,
    tensor_inv_snd, productIso_snd]

@[reassoc (attr := simp)] theorem parameterComparison_snd (Γ X : Sheaf J (Type (max u v))) :
    (parameterComparison Γ X).hom ≫ CartesianMonoidalCategory.snd X Γ = fst Γ X := by
  change ((productIso Γ X).hom ≫
    ((CartesianMonoidalCategory.tensorLeftIsoProd Γ).app X).inv ≫ (β_ Γ X).hom) ≫ _ = _
  simp only [Category.assoc, CartesianMonoidalCategory.braiding_hom_snd,
    tensor_inv_fst, productIso_fst]

private theorem parameterComparison_natural (g : Y ⟶ X) :
    SheafFunction.parameterMap Γ g ≫ (parameterComparison Γ X).hom =
      (parameterComparison Γ Y).hom ≫ (g ▷ Γ) := by
  have hf : (g ▷ Γ) ≫ CartesianMonoidalCategory.fst X Γ =
      CartesianMonoidalCategory.fst Y Γ ≫ g := by
    exact CartesianMonoidalCategory.whiskerRight_fst g Γ
  have hs : (g ▷ Γ) ≫ CartesianMonoidalCategory.snd X Γ =
      CartesianMonoidalCategory.snd Y Γ := by
    exact CartesianMonoidalCategory.whiskerRight_snd g Γ
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, parameterComparison_fst, parameterComparison_snd,
      hf, hs, parameterComparison_fst_assoc]
  all_goals rfl

/-- Ordinary parameterized sections are exactly the slice maps used by toOver. -/
def overEquiv (p : A ⟶ Γ) (X : Sheaf J (Type (max u v))) :
    Param p X ≃ ((toOver Γ).obj X ⟶ Over.mk p) where
  toFun f := Over.homMk ((parameterComparison Γ X).inv ≫ f.val) (by
    dsimp [toOver]
    rw [Category.assoc, f.property, Iso.inv_comp_eq]
    exact (parameterComparison_snd Γ X).symm)
  invFun f := ⟨(parameterComparison Γ X).hom ≫ f.left, by
    have hw : f.left ≫ p = CartesianMonoidalCategory.snd X Γ := Over.w f
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (parameterComparison Γ X).hom ≫ k) hw).trans
        (parameterComparison_snd Γ X))⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv f := by
    apply Over.OverMorphism.ext
    dsimp [toOver] at f ⊢
    simp

/-- The actual adjunction, conjugated by the checked product comparison. -/
def homEquiv (p : A ⟶ Γ) (X : Sheaf J (Type (max u v))) : Param p X ≃ (X ⟶ sections p) :=
  (overEquiv p X).trans ((Over.toOverSectionsAdj Γ).homEquiv X (Over.mk p))

def curry (p : A ⟶ Γ) (f : Param p X) : X ⟶ sections p := homEquiv p X f

def uncurry (p : A ⟶ Γ) (f : X ⟶ sections p) : Param p X := (homEquiv p X).symm f

@[simp] theorem beta (p : A ⟶ Γ) (f : Param p X) : uncurry p (curry p f) = f :=
  (homEquiv p X).left_inv f

@[simp] theorem eta (p : A ⟶ Γ) (f : X ⟶ sections p) : curry p (uncurry p f) = f :=
  (homEquiv p X).right_inv f

def parameter (p : A ⟶ Γ) (f : Param p X) (g : Y ⟶ X) : Param p Y :=
  ⟨SheafFunction.parameterMap Γ g ≫ f.val, by rw [Category.assoc, f.property]; rfl⟩

theorem uncurry_parameter (p : A ⟶ Γ) (f : X ⟶ sections p) (g : Y ⟶ X) :
    uncurry p (g ≫ f) = parameter p (uncurry p f) g := by
  have h := (Over.toOverSectionsAdj Γ).homEquiv_naturality_left_symm g f
  apply Subtype.ext
  change (parameterComparison Γ Y).hom ≫ _ = _
  rw [h]
  change (parameterComparison Γ Y).hom ≫ ((g ▷ Γ) ≫ _) =
    SheafFunction.parameterMap Γ g ≫ ((parameterComparison Γ X).hom ≫ _)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (((Over.toOverSectionsAdj Γ).homEquiv X (Over.mk p)).symm f).left)
      (parameterComparison_natural g).symm).trans (Category.assoc _ _ _))

theorem curry_parameter (p : A ⟶ Γ) (f : Param p X) (g : Y ⟶ X) :
    curry p (parameter p f g) = g ≫ curry p f := by
  apply (homEquiv p Y).symm.injective
  change uncurry p (curry p (parameter p f g)) = uncurry p (g ≫ curry p f)
  rw [uncurry_parameter, beta, beta]

def evaluation (p : A ⟶ Γ) : product Γ (sections p) ⟶ A := (uncurry p (𝟙 _)).val

@[reassoc (attr := simp)] theorem evaluation_display (p : A ⟶ Γ) :
    evaluation p ≫ p = fst Γ (sections p) := (uncurry p (𝟙 _)).property

theorem uncurry_evaluation (p : A ⟶ Γ) (f : X ⟶ sections p) :
    (uncurry p f).val = SheafFunction.parameterMap Γ f ≫ evaluation p := by
  have h := congrArg Subtype.val (uncurry_parameter p (𝟙 (sections p)) f)
  simpa only [Category.comp_id, parameter, evaluation] using h

theorem evaluation_curry (p : A ⟶ Γ) (f : Param p X) :
    SheafFunction.parameterMap Γ (curry p f) ≫ evaluation p = f.val := by
  rw [← uncurry_evaluation, beta]

theorem evaluation_curry_apply (p : A ⟶ Γ) (f : Param p X) (U : Cᵒᵖ)
    (γ : Γ.obj.obj U) (x : X.obj.obj U) :
    (evaluation p).hom.app U (γ, (curry p f).hom.app U x) = f.val.hom.app U (γ,x) :=
  congrArg (fun k : product Γ X ⟶ A => k.hom.app U (γ,x)) (evaluation_curry p f)
/-- The chosen terminal sheaf used for global elements. -/
abbrev unit : Sheaf J (Type (max u v)) := Limits.terminal _

/-- Explicit product/unit comparison for the actual terminal sheaf. -/
def unitComparison (Γ : Sheaf J (Type (max u v))) : product Γ unit ≅ Γ where
  hom := fst Γ unit
  inv := lift (𝟙 Γ) (Limits.terminal.from Γ)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    have ht' : fst Γ unit ≫ Limits.terminal.from Γ = snd Γ unit :=
      Limits.terminal.hom_ext _ _
    exact Prod.ext rfl (congrArg (fun k : product Γ unit ⟶ unit => k.hom.app U x) ht')
  inv_hom_id := rfl

/-- Parameterized sections at the terminal object are ordinary family terms. -/
def termEquiv (p : A ⟶ Γ) : Param p unit ≃ Family.Term p where
  toFun f := ⟨(unitComparison Γ).inv ≫ f.val, by
    rw [Category.assoc, f.property]
    exact (unitComparison Γ).inv_hom_id⟩
  invFun t := ⟨(unitComparison Γ).hom ≫ t.val, by
    rw [Category.assoc, t.property, Category.comp_id]; rfl⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv t := by apply Subtype.ext; simp

/-- Global elements of the internal section object are exactly family terms. -/
def globalEquiv (p : A ⟶ Γ) : (unit ⟶ sections p) ≃ Family.Term p :=
  (homEquiv p unit).symm.trans (termEquiv p)

def name (p : A ⟶ Γ) (t : Family.Term p) : unit ⟶ sections p := (globalEquiv p).symm t

@[simp] theorem global_name (p : A ⟶ Γ) (t : Family.Term p) : globalEquiv p (name p t) = t :=
  (globalEquiv p).apply_symm_apply t

@[simp] theorem name_global (p : A ⟶ Γ) (f : unit ⟶ sections p) : name p (globalEquiv p f) = f :=
  (globalEquiv p).symm_apply_apply f

theorem evaluation_name (p : A ⟶ Γ) (t : Family.Term p) :
    SheafFunction.parameterMap Γ (name p t) ≫ evaluation p = fst Γ unit ≫ t.val :=
  evaluation_curry p ((termEquiv p).symm t)

theorem evaluation_name_apply (p : A ⟶ Γ) (t : Family.Term p) (U : Cᵒᵖ)
    (γ : Γ.obj.obj U) (x : (unit (J := J)).obj.obj U) :
    (evaluation p).hom.app U (γ, (name p t).hom.app U x) = t.val.hom.app U γ :=
  congrArg (fun k : product Γ unit ⟶ A => k.hom.app U (γ,x)) (evaluation_name p t)
end SquareKit.SheafSections
