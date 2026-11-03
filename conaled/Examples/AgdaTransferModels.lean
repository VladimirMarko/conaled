import Examples.GroupoidTransport
import SquareKit.GroupoidTransport

/-! Concrete consumers of the same generated Agda-transfer source derivation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Examples.AgdaTransferModels
open CategoryTheory SquareKit.Internal.PathTransport Typed Typed.Authoring
open Examples.GroupoidTransport

def firstTransport := transport Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.first Typed.Authoring.UniversalTransfer.element
def leftTransport := transport Typed.Authoring.UniversalTransfer.context (concat Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.first Typed.Authoring.UniversalTransfer.second) Typed.Authoring.UniversalTransfer.element
def rightTransport := transport Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.second firstTransport

def sourceLabel (B : C4 ⥤ Type) (b : B.obj point) (n : ZMod 4) : point ⟶ point :=
  ((interpretTm (GroupoidModel.Instance.fullModel C4 B) Typed.Authoring.UniversalTransfer.first.deriv).down.obj
    (GroupoidModel.UniversalTransfer.inputs C4 B point point point (label n) (𝟙 point) b)).as

theorem sourceLabel_eq (B : C4 ⥤ Type) (b : B.obj point) (n : ZMod 4) :
    sourceLabel B b n = label n := by
  unfold sourceLabel
  rw [interpretTm_agrees]
  exact congrArg Discrete.as (eq_of_heq (GroupoidModel.UniversalTransfer.first_obj C4 B point point point (label n) (𝟙 point) b))

/-- Identity interpretation retains all four labels even when the action is trivial. -/
theorem sourceLabels_injective (B : C4 ⥤ Type) (b : B.obj point) :
    Function.Injective (sourceLabel B b) := by
  intro a c h
  apply labels_injective
  simpa only [sourceLabel_eq] using h

example : Function.Injective (sourceLabel faithful (0 : ZMod 4)) := sourceLabels_injective _ _

example : Function.Injective (sourceLabel ineffective (0 : Fin 2)) := sourceLabels_injective _ _
example : sourceLabel ineffective (0 : Fin 2) 1 ≠ sourceLabel ineffective (0 : Fin 2) 0 := by
  intro h
  exact (by decide : (1 : ZMod 4) ≠ 0) (sourceLabels_injective _ _ h)

local notation "MF" => GroupoidModel.Instance.fullModel C4 faithful
local notation "MI" => GroupoidModel.Instance.fullModel C4 ineffective

theorem faithful_first (p q : point ⟶ point) (b : ZMod 4) :
    ((interpretTm MF firstTransport.deriv).down.obj (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point p q b)).as =
      faithful.map p b := by
  rw [interpretTm_agrees]
  unfold firstTransport
  rw [GroupoidModel.SourceSemantics.transport_obj]
  rw [eq_of_heq (GroupoidModel.UniversalTransfer.first_obj C4 faithful point point point p q b),
    eq_of_heq (GroupoidModel.UniversalTransfer.element_obj C4 faithful point point point p q b)]
  rfl

theorem faithful_left (p q : point ⟶ point) (b : ZMod 4) :
    ((interpretTm MF leftTransport.deriv).down.obj (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point p q b)).as =
      faithful.map (p ≫ q) b := by
  rw [interpretTm_agrees]
  unfold leftTransport
  rw [GroupoidModel.SourceSemantics.transport_obj, GroupoidModel.ConcatSemantics.concat_obj]
  rw [eq_of_heq (GroupoidModel.UniversalTransfer.first_obj C4 faithful point point point p q b),
    eq_of_heq (GroupoidModel.UniversalTransfer.second_obj C4 faithful point point point p q b),
    eq_of_heq (GroupoidModel.UniversalTransfer.element_obj C4 faithful point point point p q b)]
  rfl

theorem faithful_right (p q : point ⟶ point) (b : ZMod 4) :
    ((interpretTm MF rightTransport.deriv).down.obj (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point p q b)).as =
      faithful.map q (faithful.map p b) := by
  rw [interpretTm_agrees]
  unfold rightTransport firstTransport
  rw [GroupoidModel.SourceSemantics.transport_obj, GroupoidModel.SourceSemantics.transport_obj]
  rw [eq_of_heq (GroupoidModel.UniversalTransfer.first_obj C4 faithful point point point p q b),
    eq_of_heq (GroupoidModel.UniversalTransfer.second_obj C4 faithful point point point p q b),
    eq_of_heq (GroupoidModel.UniversalTransfer.element_obj C4 faithful point point point p q b)]
  rfl

example : ((interpretTm MF firstTransport.deriv).down.obj
    (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point (label 1) (label 1) (0 : ZMod 4))).as = (1 : ZMod 4) := by
  rw [faithful_first]
  change (1 : ZMod 4) + 0 = 1
  decide

example (b : ZMod 4) : ((interpretTm MF firstTransport.deriv).down.obj
    (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point (𝟙 point) (label 1) b)).as = b := by
  rw [faithful_first]
  change (0 : ZMod 4) + b = b
  exact zero_add b

/-- Both evaluated sides equal two; the equality between them comes from the
same interpreted source proof used below for the ineffective family. -/
example : ((interpretTm MF leftTransport.deriv).down.obj
    (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point (label 1) (label 1) (0 : ZMod 4))).as = (2 : ZMod 4) := by
  rw [faithful_left]
  change (1 : ZMod 4) + 1 + 0 = 2
  decide

example : ((interpretTm MF rightTransport.deriv).down.obj
    (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point (label 1) (label 1) (0 : ZMod 4))).as = (2 : ZMod 4) := by
  rw [faithful_right]
  change (1 : ZMod 4) + (1 + 0) = 2
  decide

example (p q : point ⟶ point) (b : ZMod 4) : faithful.map (p ≫ q) b = faithful.map q (faithful.map p b) :=
  SquareKit.GroupoidTransport.transport_concat C4 faithful p q b

example (p q : point ⟶ point) (b : Fin 2) : ineffective.map (p ≫ q) b = ineffective.map q (ineffective.map p b) :=
  SquareKit.GroupoidTransport.transport_concat C4 ineffective p q b

theorem faithful_source_equality (p q : point ⟶ point) (b : ZMod 4) :
    ((interpretTm MF leftTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point p q b)).as =
    ((interpretTm MF rightTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 faithful point point point p q b)).as :=
  (faithful_left p q b).trans ((SquareKit.GroupoidTransport.transport_concat C4 faithful p q b).trans
    (faithful_right p q b).symm)

theorem ineffective_first (p q : point ⟶ point) (b : Fin 2) :
    ((interpretTm MI firstTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 ineffective point point point p q b)).as = b := by
  rw [interpretTm_agrees]
  unfold firstTransport
  rw [GroupoidModel.SourceSemantics.transport_obj,
    eq_of_heq (GroupoidModel.UniversalTransfer.element_obj C4 ineffective point point point p q b)]
  rfl

example (b : Fin 2) : ((interpretTm MI firstTransport.deriv).down.obj
    (GroupoidModel.UniversalTransfer.inputs C4 ineffective point point point (label 1) (label 1) b)).as = b :=
  ineffective_first _ _ _

example (b : Fin 2) : ((interpretTm MI firstTransport.deriv).down.obj
    (GroupoidModel.UniversalTransfer.inputs C4 ineffective point point point (𝟙 point) (label 1) b)).as = b :=
  ineffective_first _ _ _

theorem ineffective_left (p q : point ⟶ point) (b : Fin 2) :
    ((interpretTm MI leftTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 ineffective point point point p q b)).as =
      ineffective.map (p ≫ q) b := by
  rw [interpretTm_agrees]
  unfold leftTransport
  rw [GroupoidModel.SourceSemantics.transport_obj,
    eq_of_heq (GroupoidModel.UniversalTransfer.element_obj C4 ineffective point point point p q b)]
  rfl

theorem ineffective_right (p q : point ⟶ point) (b : Fin 2) :
    ((interpretTm MI rightTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 ineffective point point point p q b)).as =
      ineffective.map q (ineffective.map p b) := by
  rw [interpretTm_agrees]
  unfold rightTransport firstTransport
  rw [GroupoidModel.SourceSemantics.transport_obj, GroupoidModel.SourceSemantics.transport_obj,
    eq_of_heq (GroupoidModel.UniversalTransfer.element_obj C4 ineffective point point point p q b)]
  rfl

theorem ineffective_source_equality (p q : point ⟶ point) (b : Fin 2) :
    ((interpretTm MI leftTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 ineffective point point point p q b)).as =
    ((interpretTm MI rightTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 ineffective point point point p q b)).as :=
  (ineffective_left p q b).trans ((SquareKit.GroupoidTransport.transport_concat C4 ineffective p q b).trans
    (ineffective_right p q b).symm)

/-- The bridge preserves reflexivity of the actual named source path. -/
example (B : C4 ⥤ Type) (p q : point ⟶ point) (b : B.obj point) :
    GroupoidModel.TransferSoundness.basePathEquiv C4 B
      Typed.Authoring.UniversalTransfer.fixed Typed.Authoring.UniversalTransfer.fixed
      (GroupoidModel.UniversalTransfer.inputs C4 B point point point p q b)
      ((interpretTm (GroupoidModel.Instance.fullModel C4 B)
        (Path.reflexivity Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.fixed).deriv).down.obj
        (GroupoidModel.UniversalTransfer.inputs C4 B point point point p q b)) = 𝟙 _ := by
  rw [interpretTm_agrees]
  exact GroupoidModel.TransferSoundness.basePathEquiv_refl C4 B _ _ _

/-- Composition is preserved for the interpreted derived concat operation. -/
example (B : C4 ⥤ Type) (p q : point ⟶ point) (b : B.obj point) :
    GroupoidModel.TransferSoundness.basePathEquiv C4 B
      Typed.Authoring.UniversalTransfer.fixed Typed.Authoring.UniversalTransfer.last
      (GroupoidModel.UniversalTransfer.inputs C4 B point point point p q b)
      ((interpretTm (GroupoidModel.Instance.fullModel C4 B)
        (concat Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.first
          Typed.Authoring.UniversalTransfer.second).deriv).down.obj
        (GroupoidModel.UniversalTransfer.inputs C4 B point point point p q b)) =
      ((interpretTm (GroupoidModel.Instance.fullModel C4 B) Typed.Authoring.UniversalTransfer.first.deriv).down.obj
        (GroupoidModel.UniversalTransfer.inputs C4 B point point point p q b)).as ≫
      ((interpretTm (GroupoidModel.Instance.fullModel C4 B) Typed.Authoring.UniversalTransfer.second.deriv).down.obj
        (GroupoidModel.UniversalTransfer.inputs C4 B point point point p q b)).as := by
  rw [interpretTm_agrees, interpretTm_agrees, interpretTm_agrees]
  exact GroupoidModel.TransferSoundness.basePathEquiv_concat C4 B _ _ _ _

end Examples.AgdaTransferModels
