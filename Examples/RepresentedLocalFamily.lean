import SquareKit.Internal.RepresentedLocalFamily
import Examples.CoherentFamilyClassification

/-! Independent represented local input, nonidentity comparisons, and noninvertible maps. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.RepresentedLocalFamily
open CategoryTheory CategoryTheory.Functor
open SquareKit.RepresentableClassification
open SquareKit.RepresentedLocalFamily
open Examples.CategoryValuedEvaluation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each represented context has the constant Boolean family. Root restrictions
use the parity-dependent swap; this is local input, with no arrow-code constructor. -/
noncomputable def boolean : Family context (Type) where
  app _ := (Functor.const _).obj Bool
  comparison f := NatIso.ofComponents (fun _ => by
    letI := Examples.CoherentFamilyClassification.twisted_map_isIso f.unop.hom
    exact asIso (Examples.CoherentFamilyClassification.twisted.map f.unop.hom)) (by
      intro x y g
      simp)
  comparison_id x := by
    ext z b
    exact congrArg (fun f => f b)
      (Examples.CoherentFamilyClassification.twisted.map_id x.unop.obj)
  comparison_comp f g := by
    ext z b
    exact congrArg (fun h => h b)
      (Examples.CoherentFamilyClassification.twisted.map_comp g.unop.hom f.unop.hom)

/-- The chosen restriction really changes a value. -/
example : (boolean.comparison step.op).hom.app
    (arrowView (Arrow.mk (𝟙 (point 1)))) false = true := by
  rfl

/-- Assembly and decoding preserve this nonidentity action. -/
example : ((decode (Type) context).obj boolean).map step false = true := rfl

/-- A terminal local family, independently specified by constant local functors. -/
def terminal : Family context (Type) where
  app _ := (Functor.const _).obj PUnit
  comparison _ := Iso.refl _
  comparison_id _ := rfl
  comparison_comp _ _ := rfl

/-- All compatible maps are admitted, including a collapse of distinct values. -/
def collapse : boolean ⟶ terminal where
  app _ := { app := fun _ => TypeCat.ofHom (fun _ => PUnit.unit) }
  naturality _ := by ext z b; rfl

theorem collapse_not_iso : ¬ IsIso collapse := by
  intro h
  have : IsIso ((decode (Type) context).map collapse) :=
    (decode (Type) context).map_isIso collapse
  have hi : IsIso (((decode (Type) context).map collapse).app (point 0)) := inferInstance
  have hinj := (CategoryTheory.isIso_iff_bijective _).mp hi |>.1
  have bad : (false : Bool) = true := hinj rfl
  contradiction

/-- The categorical unit recovers this noninvertible map as well. -/
example : collapse ≫ (classification (Type) context).unitIso.hom.app terminal =
    (classification (Type) context).unitIso.hom.app boolean ≫
      ((classification (Type) context).functor ⋙
        (classification (Type) context).inverse).map collapse :=
  (classification (Type) context).unitIso.hom.naturality collapse

/-- A non-groupoidal target retains its noninvertible family action. -/
noncomputable def ordered : Family context ℕᵒᵖ :=
  (classification ℕᵒᵖ context).inverse.obj family

example : ((classification ℕᵒᵖ context).counitIso.app family).hom.app (point 2) ≫
    family.map step = ((decode ℕᵒᵖ context).obj ordered).map step ≫
      ((classification ℕᵒᵖ context).counitIso.app family).hom.app (point 1) :=
  (((classification ℕᵒᵖ context).counitIso.app family).hom.naturality step).symm

theorem ordered_step_not_iso : ¬ IsIso (((decode ℕᵒᵖ context).obj ordered).map step) := by
  intro h
  have hi := asIso (((decode ℕᵒᵖ context).obj ordered).map step)
  have back := hi.inv.unop
  have hle := leOfHom back
  change 2 ≤ 1 at hle
  omega

/-- At matching universes the local input is an actual Mathlib pseudonatural cocone. -/
noncomputable def orderedCocone := LocalData.toStrongTrans ℕᵒᵖ ordered

/-- Constant ordered fibers give a noninvertible modification between cocones. -/
def constantOrder (n : ℕ) : Family context ℕᵒᵖ where
  app _ := (Functor.const _).obj (Opposite.op n)
  comparison _ := Iso.refl _
  comparison_id _ := rfl
  comparison_comp _ _ := rfl

def orderMap : constantOrder 2 ⟶ constantOrder 1 where
  app _ := { app := fun _ => Quiver.Hom.op (homOfLE (by decide : 1 ≤ 2)) }
  naturality _ := by ext z; exact Subsingleton.elim _ _

def orderModification := LocalData.toModification ℕᵒᵖ orderMap

example : LocalData.ofModification ℕᵒᵖ orderModification = orderMap :=
  LocalData.ofModification_toModification ℕᵒᵖ orderMap

example : ¬ IsIso orderMap := by
  intro h
  have back := ((inv orderMap).app (Opposite.op (point 0))).app
    (arrowView (Arrow.mk (𝟙 (point 0))))
  have hle := leOfHom back.unop
  change 2 ≤ 1 at hle
  omega

namespace Substitution
open Examples.NonCubicalClassification
noncomputable def classified :=
  (classification (Type) Examples.NonCubicalClassification.context).inverse.obj
    Examples.NonCubicalClassification.family

example : ((decode (Type) Examples.NonCubicalClassification.context).obj
    ((reindex (Type) Examples.NonCubicalClassification.double).obj
      ((reindex (Type) Examples.NonCubicalClassification.successor).obj classified))).obj
        (Examples.NonCubicalClassification.point 2) = Fin 6 := rfl

example : ((decodeReindex (Type) (Examples.NonCubicalClassification.double ≫
    Examples.NonCubicalClassification.successor)).hom.app classified).app
      (Examples.NonCubicalClassification.point 2) =
    ((decodeReindex (Type) Examples.NonCubicalClassification.double).hom.app
      ((reindex (Type) Examples.NonCubicalClassification.successor).obj classified)).app
        (Examples.NonCubicalClassification.point 2) ≫
    ((decodeReindex (Type) Examples.NonCubicalClassification.successor).hom.app classified).app
      (Examples.NonCubicalClassification.point 4) :=
  decodeReindex_comp (Type) Examples.NonCubicalClassification.successor
    Examples.NonCubicalClassification.double classified (Examples.NonCubicalClassification.point 2)
end Substitution
end Examples.RepresentedLocalFamily
