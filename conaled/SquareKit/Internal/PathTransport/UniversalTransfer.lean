import SquareKit.Internal.PathTransport.Transfer
import SquareKit.Internal.PathTransport.TransferConsumer
noncomputable section
namespace SquareKit.Internal.PathTransport.Typed.Authoring.UniversalTransfer
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
def baseContext := CtxDeriv.ext CtxDeriv.empty (TyDeriv.base CtxDeriv.empty)
def point := BasePoint.variable CtxDeriv.empty
def context := TransferFrame.context baseContext point
def fixed := TransferFrame.fixed baseContext point
def moving := TransferFrame.moving baseContext point
def last := TransferFrame.last baseContext point
def first := TransferFrame.first baseContext point
def second := TransferFrame.second baseContext point
def element := TransferFrame.element baseContext point
def proof := trConcat context first second element
end SquareKit.Internal.PathTransport.Typed.Authoring.UniversalTransfer

namespace SquareKit.Internal.PathTransport.GroupoidModel.UniversalTransfer
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B

def inputs (x y z : C) (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    ↥(show Grpd.{u,u} from TransferFrame.contextCode Authoring.UniversalTransfer.context M) := by
  refine ⟨⟨⟨⟨⟨⟨⟨PUnit.unit⟩, x⟩, y⟩, ?_⟩, z⟩, ?_⟩, ?_⟩
  · change Discrete (((Authoring.UniversalTransfer.point.code M).down.obj ⟨⟨PUnit.unit⟩, x⟩) ⟶ y)
    unfold Authoring.UniversalTransfer.point
    rw [SourceSemantics.base_variable_eval]
    exact Discrete.mk p
  · change Discrete (((ConcatFrame.yAtZ Authoring.UniversalTransfer.baseContext Authoring.UniversalTransfer.point).code M).down.obj _ ⟶
      ((ConcatFrame.z Authoring.UniversalTransfer.baseContext Authoring.UniversalTransfer.point).code M).down.obj _)
    unfold ConcatFrame.yAtZ ConcatFrame.z
    rw [SourceSemantics.base_reindex_eval, SourceSemantics.moving_eval, SourceSemantics.base_variable_eval C B (ConcatFrame.paths Authoring.UniversalTransfer.baseContext Authoring.UniversalTransfer.point)]
    exact Discrete.mk q
  · change Discrete (B.obj (((ConcatFrame.fixed Authoring.UniversalTransfer.baseContext Authoring.UniversalTransfer.point).code M).down.obj _))
    unfold ConcatFrame.fixed
    rw [SourceSemantics.base_reindex_eval, SourceSemantics.base_reindex_eval]
    change Discrete (B.obj ((Authoring.UniversalTransfer.point.code M).down.obj ⟨⟨PUnit.unit⟩, x⟩))
    unfold Authoring.UniversalTransfer.point
    rw [SourceSemantics.base_variable_eval]
    exact Discrete.mk b

theorem cast_obj_heq {δ : CtxCode.{u+1}} {a a' : TyCode δ} (h : a = a') (v : TmCode δ a)
    (g : ↥(show Grpd.{u,u} from δ M)) :
    HEq ((castCode h v M).down.obj g) ((v M).down.obj g) := by
  cases h
  rfl

theorem fixed_obj (x y z : C) (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    (Authoring.UniversalTransfer.fixed.code M).down.obj (inputs C B x y z p q b) = x := by
  unfold Authoring.UniversalTransfer.fixed TransferFrame.fixed ConcatFrame.fixed
  rw [SourceSemantics.base_reindex_eval, SourceSemantics.base_reindex_eval, SourceSemantics.base_reindex_eval]
  change (Authoring.UniversalTransfer.point.code M).down.obj ⟨⟨PUnit.unit⟩,x⟩ = x
  unfold Authoring.UniversalTransfer.point
  rw [SourceSemantics.base_variable_eval]
  rfl

theorem moving_obj (x y z : C) (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    (Authoring.UniversalTransfer.moving.code M).down.obj (inputs C B x y z p q b) = y := by
  unfold Authoring.UniversalTransfer.moving TransferFrame.moving ConcatFrame.yAtQ ConcatFrame.yAtZ
  rw [SourceSemantics.base_reindex_eval, SourceSemantics.base_reindex_eval, SourceSemantics.base_reindex_eval,
    SourceSemantics.moving_eval]
  rfl

theorem last_obj (x y z : C) (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    (Authoring.UniversalTransfer.last.code M).down.obj (inputs C B x y z p q b) = z := by
  unfold Authoring.UniversalTransfer.last TransferFrame.last ConcatFrame.zAtQ ConcatFrame.z
  rw [SourceSemantics.base_reindex_eval, SourceSemantics.base_reindex_eval,
    SourceSemantics.base_variable_eval C B (ConcatFrame.paths Authoring.UniversalTransfer.baseContext Authoring.UniversalTransfer.point)]
  rfl

theorem first_obj (x y z : C) (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    HEq ((Authoring.UniversalTransfer.first.code M).down.obj (inputs C B x y z p q b)) (Discrete.mk p) := by
  unfold Authoring.UniversalTransfer.first TransferFrame.first Path.reindex TransferFrame.firstBeforeB Path.withEndpoints pathWitness
  apply (cast_obj_heq C B _ _ _).trans
  apply (cast_obj_heq C B _ _ _).trans
  apply (cast_obj_heq C B _ _ _).trans
  apply (cast_obj_heq C B _ _ _).trans
  exact cast_heq _ _

theorem second_obj (x y z : C) (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    HEq ((Authoring.UniversalTransfer.second.code M).down.obj (inputs C B x y z p q b)) (Discrete.mk q) := by
  unfold Authoring.UniversalTransfer.second TransferFrame.second Path.reindex ConcatFrame.q Path.variable
  apply (cast_obj_heq C B _ _ _).trans
  apply (cast_obj_heq C B _ _ _).trans
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))

theorem element_obj (x y z : C) (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    HEq ((Authoring.UniversalTransfer.element.code M).down.obj (inputs C B x y z p q b)) (Discrete.mk b) := by
  unfold Authoring.UniversalTransfer.element TransferFrame.element FiberElement.variable
  apply (cast_obj_heq C B _ _ _).trans
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))

theorem action_relabel_obj {x₀ y₀ z₀ x y z : C}
    (hx : x₀ = x) (hy : y₀ = y) (hz : z₀ = z)
    (p₀ : Discrete (x₀ ⟶ y₀)) (q₀ : Discrete (y₀ ⟶ z₀)) (b₀ : Discrete (B.obj x₀))
    (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x)
    (hp : HEq p₀ (Discrete.mk p)) (hq : HEq q₀ (Discrete.mk q)) (hb : HEq b₀ (Discrete.mk b))
    (e : B.map (p₀.as ≫ q₀.as) b₀.as = B.map q₀.as (B.map p₀.as b₀.as)) :
    B.map (p ≫ q) b = B.map q (B.map p b) := by
  cases hx; cases hy; cases hz
  cases eq_of_heq hp; cases eq_of_heq hq; cases eq_of_heq hb
  exact e

theorem transport_concat {x y z : C} (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    B.map (p ≫ q) b = B.map q (B.map p b) := by
  have h := TransferConsumer.consume C B Authoring.UniversalTransfer.context
    Authoring.UniversalTransfer.fixed Authoring.UniversalTransfer.moving Authoring.UniversalTransfer.last
    Authoring.UniversalTransfer.first Authoring.UniversalTransfer.second Authoring.UniversalTransfer.element
    Authoring.UniversalTransfer.proof (inputs C B x y z p q b)
  exact action_relabel_obj C B (fixed_obj C B x y z p q b) (moving_obj C B x y z p q b)
    (last_obj C B x y z p q b) _ _ _ p q b (first_obj C B x y z p q b)
    (second_obj C B x y z p q b) (element_obj C B x y z p q b) h
end SquareKit.Internal.PathTransport.GroupoidModel.UniversalTransfer

namespace SquareKit.Internal.PathTransport.GroupoidModel.UniversalTransfer
open CategoryTheory
universe u v w
/-- Independent object, arrow and fiber universes use the same source proof
through the existing universe-lift model. -/
theorem transport_concat_universes (C : Type u) [Groupoid.{v} C] (B : C ⥤ Type w)
    {x y z : C} (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    B.map (p ≫ q) b = B.map q (B.map p b) := by
  have h := transport_concat (AsSmall.{w} C) (Instance.liftedFamily C B)
    (x := (AsSmall.up.obj x)) (y := (AsSmall.up.obj y)) (z := (AsSmall.up.obj z))
    (ULift.up p) (ULift.up q) (ULift.up b)
  exact congrArg ULift.down h
end SquareKit.Internal.PathTransport.GroupoidModel.UniversalTransfer
