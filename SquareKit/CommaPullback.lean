import SquareKit.CommaUniversal
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # The arrow-category pullback presentation of a comma category

This is the ordinary strict pullback along the endpoint functor from arrows,
not a pullback of `F` and `G` themselves and not an isocomma category.
-/

namespace SquareKit.Comma.Universal

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]
  (F : A ⥤ T) (G : B ⥤ T)

/-- The two endpoints of an arrow. -/
def endpoints : Arrow T ⥤ T × T := Arrow.leftFunc.prod' Arrow.rightFunc

/-- Both projections, retaining the original source objects. -/
def projections : CategoryTheory.Comma F G ⥤ A × B :=
  (CategoryTheory.Comma.fst F G).prod' (CategoryTheory.Comma.snd F G)

/-- The selected connector and the square between connectors. -/
def connector : CategoryTheory.Comma F G ⥤ Arrow T where
  obj c := Arrow.mk c.hom
  map f := Arrow.homMk (F.map f.left) (G.map f.right) f.w
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

theorem pullback_condition : projections F G ⋙ F.prod G = connector F G ⋙ endpoints := rfl

variable {X : Type u₄} [Category.{v₄} X]

/-- The connector comparison extracted from a strictly compatible arrow-valued functor. -/
def pullbackComparison (P : X ⥤ A × B) (Q : X ⥤ Arrow T)
    (h : P ⋙ F.prod G = Q ⋙ endpoints) :
    (P ⋙ CategoryTheory.Prod.fst A B) ⋙ F ⟶ (P ⋙ CategoryTheory.Prod.snd A B) ⋙ G :=
  eqToHom (congrArg (fun H => H ⋙ CategoryTheory.Prod.fst T T) h) ≫
    whiskerLeft Q Arrow.leftToRight ≫
      eqToHom (congrArg (fun H => H ⋙ CategoryTheory.Prod.snd T T) h).symm

/-- Lift a strictly commuting square of functors into the comma category. -/
def pullbackLift (P : X ⥤ A × B) (Q : X ⥤ Arrow T)
    (h : P ⋙ F.prod G = Q ⋙ endpoints) : X ⥤ CategoryTheory.Comma F G :=
  lift F G (P ⋙ CategoryTheory.Prod.fst A B) (P ⋙ CategoryTheory.Prod.snd A B)
    (pullbackComparison F G P Q h)

@[simp] theorem pullbackLift_projections (P : X ⥤ A × B) (Q : X ⥤ Arrow T)
    (h : P ⋙ F.prod G = Q ⋙ endpoints) :
    pullbackLift F G P Q h ⋙ projections F G = P := rfl

theorem pullbackLift_connector (P : X ⥤ A × B) (Q : X ⥤ Arrow T)
    (h : P ⋙ F.prod G = Q ⋙ endpoints) :
    pullbackLift F G P Q h ⋙ connector F G = Q := by
  refine CategoryTheory.Functor.ext
    (fun x => Arrow.ext
      (congrArg Prod.fst (CategoryTheory.Functor.congr_obj h x))
      (congrArg Prod.snd (CategoryTheory.Functor.congr_obj h x)) (by
        dsimp [pullbackLift, lift, connector, pullbackComparison]
        simp only [eqToHom_app])) ?_
  intro x y f
  apply CategoryTheory.CommaMorphism.ext
  · have e := CategoryTheory.Functor.congr_hom h f
    simpa [pullbackLift, lift, connector, endpoints, Arrow.eqToHom_left, Arrow.eqToHom_right] using congrArg Prod.fst e
  · have e := CategoryTheory.Functor.congr_hom h f
    simpa [pullbackLift, lift, connector, endpoints, Arrow.eqToHom_left, Arrow.eqToHom_right] using congrArg Prod.snd e

/-- The source objects and connector determine a comma object, even for nonfaithful functors. -/
theorem obj_ext {c d : CategoryTheory.Comma F G}
    (hl : c.left = d.left) (hr : c.right = d.right)
    (hc : (connector F G).obj c = (connector F G).obj d) : c = d := by
  rcases c with ⟨a, b, c⟩
  rcases d with ⟨a', b', d⟩
  dsimp at hl hr
  cases hl
  cases hr
  have hd : c = d := by
    injection hc with _ _ hh
  cases hd
  rfl

/-- Both functor projections and the connector jointly determine a functor. -/
theorem functor_ext {H K : X ⥤ CategoryTheory.Comma F G}
    (hp : H ⋙ projections F G = K ⋙ projections F G)
    (hc : H ⋙ connector F G = K ⋙ connector F G) : H = K := by
  refine CategoryTheory.Functor.ext (fun x => obj_ext F G
    (congrArg Prod.fst (CategoryTheory.Functor.congr_obj hp x))
    (congrArg Prod.snd (CategoryTheory.Functor.congr_obj hp x))
    (CategoryTheory.Functor.congr_obj hc x)) ?_
  intro x y f
  apply CategoryTheory.CommaMorphism.ext
  · simpa [projections, CategoryTheory.eqToHom_fst] using congrArg Prod.fst (CategoryTheory.Functor.congr_hom hp f)
  · simpa [projections, CategoryTheory.eqToHom_snd] using congrArg Prod.snd (CategoryTheory.Functor.congr_hom hp f)

/-- Uniqueness in the strict arrow-category pullback. -/
theorem pullbackLift_unique (P : X ⥤ A × B) (Q : X ⥤ Arrow T)
    (h : P ⋙ F.prod G = Q ⋙ endpoints) (H : X ⥤ CategoryTheory.Comma F G)
    (hp : H ⋙ projections F G = P) (hc : H ⋙ connector F G = Q) :
    H = pullbackLift F G P Q h :=
  functor_ext F G (hp.trans (pullbackLift_projections F G P Q h).symm)
    (hc.trans (pullbackLift_connector F G P Q h).symm)

end SquareKit.Comma.Universal

namespace SquareKit.Comma.Universal

open CategoryTheory CategoryTheory.Limits

universe u
variable {A B T : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} T]
  (F : A ⥤ T) (G : B ⥤ T)

/-- Bundling the strict square in `Cat` uses a common object/hom universe.
The unbundled lift and its uniqueness above retain independent universes. -/
def arrowPullbackCone : PullbackCone (F.prod G).toCatHom (endpoints (T := T)).toCatHom :=
  PullbackCone.mk (projections F G).toCatHom (connector F G).toCatHom rfl

/-- The comma category is the ordinary pullback of the arrow endpoint functor. -/
def arrowPullbackIsLimit : IsLimit (arrowPullbackCone F G) :=
  PullbackCone.IsLimit.mk (fst := (projections F G).toCatHom)
    (snd := (connector F G).toCatHom) rfl
    (fun s => (pullbackLift F G s.fst.toFunctor s.snd.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)).toCatHom)
    (fun _s => Cat.Hom.ext (pullbackLift_projections F G _ _ _))
    (fun _s => Cat.Hom.ext (pullbackLift_connector F G _ _ _))
    (fun _s m hl hr => Cat.Hom.ext (pullbackLift_unique F G _ _ _ m.toFunctor
      (congrArg Cat.Hom.toFunctor hl) (congrArg Cat.Hom.toFunctor hr)))

theorem isPullback_arrow : IsPullback (projections F G).toCatHom
    (connector F G).toCatHom (F.prod G).toCatHom (endpoints (T := T)).toCatHom :=
  IsPullback.of_isLimit (arrowPullbackIsLimit F G)

end SquareKit.Comma.Universal
