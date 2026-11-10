import SquareKit.Internal.PathTransport.ComparisonModification
import Examples.GroupoidTransport
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.Logic.Equiv.Bool

/-! Unequal naturally isomorphic comparison functors, noninvertible primitive
maps, and a dependent fiber extension through the external modification API. -/
noncomputable section
namespace Examples.ComparisonModification
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
open Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : Groupoid GroupoidTransport.C4 := Groupoid.ofIsGroupoid
local instance : Groupoid (Codiscrete Bool) where
  toCategory := inferInstance
  inv _ := ()
  inv_comp _ := rfl
  comp_inv _ := rfl

abbrev C := Grpd.of GroupoidTransport.C4
abbrev D := Grpd.of (Codiscrete Bool)
def left : C ⥤ D := Codiscrete.functor (fun _ => false)
def right : C ⥤ D := Codiscrete.functor (fun _ => true)
def comparison : left ≅ right := Codiscrete.natIso

theorem functors_unequal : left ≠ right := by
  intro h
  have he := congrArg (fun F => (F.obj GroupoidTransport.point).as) h
  cases he

theorem arrow_map_not_injective : ¬ Function.Injective
    (left.map (X := GroupoidTransport.point) (Y := GroupoidTransport.point)) := by
  intro h
  have he := h (a₁ := Multiplicative.ofAdd (0 : ZMod 4))
    (a₂ := Multiplicative.ofAdd (1 : ZMod 4)) rfl
  have he' : (0 : ZMod 4) = 1 := congrArg Multiplicative.toAdd he
  exact (by decide : (0 : ZMod 4) ≠ 1) he'

def before : C ⥤ Type := (CategoryTheory.Functor.const _).obj Bool
def after : D ⥤ Type := (CategoryTheory.Functor.const _).obj PUnit

def alpha : before ⟶ left ⋙ after where
  app _ := ↾fun _ => PUnit.unit
  naturality {_ _} _ := rfl

def beta : before ⟶ right ⋙ after where
  app _ := ↾fun _ => PUnit.unit
  naturality {_ _} _ := rfl

theorem primitive_square : alpha ≫ CategoryTheory.Functor.whiskerRight comparison.hom after = beta := rfl

theorem fiber_map_not_injective : ¬ Function.Injective (alpha.app GroupoidTransport.point) := by
  intro h
  have he := h (a₁ := false) (a₂ := true) rfl
  cases he

def primitive := fiberModification comparison before after alpha beta primitive_square

def extended := Modification.totalIso comparison primitive

example := baseModification comparison (Discrete PUnit)
example := emptyModification.{0}

/-- The constructed comparison changes the actual target base object. -/
example : (totalMap left (A := setFamily before) (B := setFamily after) (CategoryTheory.Functor.whiskerRight alpha discrete)).obj
    ⟨GroupoidTransport.point, Discrete.mk false⟩ ≠
    (totalMap right (A := setFamily before) (B := setFamily after) (CategoryTheory.Functor.whiskerRight beta discrete)).obj
      ⟨GroupoidTransport.point, Discrete.mk false⟩ := by
  intro h
  have he := congrArg (fun x => x.base.as) h
  cases he

/-- Arbitrary dependent primitive families use the same extension construction;
no constancy, faithfulness or invertibility hypothesis is present. -/
def dependentExtension {C D : Grpd.{0,0}} {F G : C ⥤ D} (η : F ≅ G)
    (P : C ⥤ Type) (Q : D ⥤ Type) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
    (h : α ≫ CategoryTheory.Functor.whiskerRight η.hom Q = β) :=
  Modification.totalIso η (fiberModification η P Q α β h)

/-- The fiber transport changes values along the selected base isomorphism. -/
def chart (d : D) : Bool ≃ Bool := if d.as then Equiv.boolNot else Equiv.refl Bool

def varying : D ⥤ Type where
  obj _ := Bool
  map {x y} _ := ↾fun b => chart y ((chart x).symm b)
  map_id x := by ext b; exact Equiv.apply_symm_apply (chart x) b
  map_comp f g := by ext b; simp

def varyingAlpha : before ⟶ left ⋙ varying where
  app _ := ↾fun b => b
  naturality {_ _} _ := by ext b; rfl

def varyingBeta : before ⟶ right ⋙ varying :=
  varyingAlpha ≫ CategoryTheory.Functor.whiskerRight comparison.hom varying

def varyingExtension := dependentExtension comparison before varying varyingAlpha varyingBeta rfl

theorem varying_transport : varying.map (comparison.hom.app GroupoidTransport.point) false = true := rfl

example (x : Extend (setFamily before)) :
    ((Modification.totalIso comparison
      (fiberModification comparison before varying varyingAlpha varyingBeta rfl)).hom.app x).base =
      comparison.hom.app x.base :=
  Modification.totalIso_base comparison _ x

end Examples.ComparisonModification
